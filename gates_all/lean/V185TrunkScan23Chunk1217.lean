import V185TrunkScan23Chunk1216

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_7211383 : List Nat := [1, 1, 3, 1, 1, 2, 2, 5, 2, 5]
def baseStart_7211383 : Nat := 118140960795 + 7211383 * 2 ^ 59
def prefixEnd_7211383 : Nat := 4983230072969 + 3 ^ 40 * 7211383 * 2
def baseEnd_7211383 : Nat := 1234301887554021388182653

theorem tailTrace_7211383 : CollatzResearch.WordTrace tailWord_7211383 prefixEnd_7211383 1234301887554021388182653 := by
  unfold tailWord_7211383
  simp only [CollatzResearch.WordTrace]
  refine ⟨263020746033398472008334803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175347164022265648005556535 263020746033398472008334803)
  ·
    refine ⟨394531119050097708012502205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263020746033398472008334803 394531119050097708012502205)
    ·
      refine ⟨147949169643786640504688327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 394531119050097708012502205 147949169643786640504688327)
      ·
        refine ⟨221923754465679960757032491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147949169643786640504688327 221923754465679960757032491)
        ·
          refine ⟨332885631698519941135548737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 221923754465679960757032491 332885631698519941135548737)
          ·
            refine ⟨249664223773889955851661553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 332885631698519941135548737 249664223773889955851661553)
            ·
              refine ⟨187248167830417466888746165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 249664223773889955851661553 187248167830417466888746165)
              ·
                refine ⟨17554515734101637520819953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 187248167830417466888746165 17554515734101637520819953)
                ·
                  refine ⟨13165886800576228140614965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17554515734101637520819953 13165886800576228140614965)
                  ·
                    refine ⟨1234301887554021388182653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13165886800576228140614965 1234301887554021388182653)
                    ·
                      rfl

theorem cell23_7211383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 5, 2, 5].length) (baseStart_7211383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7211383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7211383 prefixEnd_7211383 := by exact prefixLift 7211383
  have htrace : WordTrace (prefixWord ++ tailWord_7211383) baseStart_7211383 baseEnd_7211383 := by
    simpa [prefixWord, tailWord_7211383, baseEnd_7211383] using wordTrace_append hprefix tailTrace_7211383
  have hstable : (prefixWord ++ tailWord_7211383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7211383).length < 2 ^ (prefixWord ++ tailWord_7211383).sum := by decide
  have hdescent : baseEnd_7211383 < baseStart_7211383 := by decide
  rcases family_descends (prefixWord ++ tailWord_7211383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7211477 : List Nat := [1, 3, 2, 3, 1, 2, 4, 1, 6]
def baseStart_7211477 : Nat := 118140960795 + 7211477 * 2 ^ 59
def prefixEnd_7211477 : Nat := 4983230072969 + 3 ^ 40 * 7211477 * 2
def baseEnd_7211477 : Nat := 411439325538176310752503

theorem tailTrace_7211477 : CollatzResearch.WordTrace tailWord_7211477 prefixEnd_7211477 411439325538176310752503 := by
  unfold tailWord_7211477
  simp only [CollatzResearch.WordTrace]
  refine ⟨263024174495057926062256685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175349449663371950708171123 263024174495057926062256685)
  ·
    refine ⟨98634065435646722273346257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 263024174495057926062256685 98634065435646722273346257)
    ·
      refine ⟨73975549076735041705009693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98634065435646722273346257 73975549076735041705009693)
      ·
        refine ⟨27740830903775640639378635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73975549076735041705009693 27740830903775640639378635)
        ·
          refine ⟨41611246355663460959067953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27740830903775640639378635 41611246355663460959067953)
          ·
            refine ⟨31208434766747595719300965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41611246355663460959067953 31208434766747595719300965)
            ·
              refine ⟨5851581518765174197368931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31208434766747595719300965 5851581518765174197368931)
              ·
                refine ⟨8777372278147761296053397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5851581518765174197368931 8777372278147761296053397)
                ·
                  refine ⟨411439325538176310752503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8777372278147761296053397 411439325538176310752503)
                  ·
                    rfl

theorem cell23_7211477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 4, 1, 6].length) (baseStart_7211477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7211477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7211477 prefixEnd_7211477 := by exact prefixLift 7211477
  have htrace : WordTrace (prefixWord ++ tailWord_7211477) baseStart_7211477 baseEnd_7211477 := by
    simpa [prefixWord, tailWord_7211477, baseEnd_7211477] using wordTrace_append hprefix tailTrace_7211477
  have hstable : (prefixWord ++ tailWord_7211477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7211477).length < 2 ^ (prefixWord ++ tailWord_7211477).sum := by decide
  have hdescent : baseEnd_7211477 < baseStart_7211477 := by decide
  rcases family_descends (prefixWord ++ tailWord_7211477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7211504 : List Nat := [2, 1, 1, 1, 3, 3, 2, 5, 1, 1, 3]
def baseStart_7211504 : Nat := 118140960795 + 7211504 * 2 ^ 59
def prefixEnd_7211504 : Nat := 4983230072969 + 3 ^ 40 * 7211504 * 2
def baseEnd_7211504 : Nat := 3702967793821258191134903

theorem tailTrace_7211504 : CollatzResearch.WordTrace tailWord_7211504 prefixEnd_7211504 3702967793821258191134903 := by
  unfold tailWord_7211504
  simp only [CollatzResearch.WordTrace]
  refine ⟨131512579632980054836744783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175350106177306739782326377 131512579632980054836744783)
  ·
    refine ⟨197268869449470082255117175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131512579632980054836744783 197268869449470082255117175)
    ·
      refine ⟨295903304174205123382675763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197268869449470082255117175 295903304174205123382675763)
      ·
        refine ⟨443854956261307685074013645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 295903304174205123382675763 443854956261307685074013645)
        ·
          refine ⟨166445608597990381902755117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 443854956261307685074013645 166445608597990381902755117)
          ·
            refine ⟨62417103224246393213533169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 166445608597990381902755117 62417103224246393213533169)
            ·
              refine ⟨46812827418184794910149877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62417103224246393213533169 46812827418184794910149877)
              ·
                refine ⟨4388702570454824522826551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 46812827418184794910149877 4388702570454824522826551)
                ·
                  refine ⟨6583053855682236784239827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4388702570454824522826551 6583053855682236784239827)
                  ·
                    refine ⟨9874580783523355176359741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6583053855682236784239827 9874580783523355176359741)
                    ·
                      refine ⟨3702967793821258191134903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9874580783523355176359741 3702967793821258191134903)
                      ·
                        rfl

theorem cell23_7211504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 5, 1, 1, 3].length) (baseStart_7211504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7211504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7211504 prefixEnd_7211504 := by exact prefixLift 7211504
  have htrace : WordTrace (prefixWord ++ tailWord_7211504) baseStart_7211504 baseEnd_7211504 := by
    simpa [prefixWord, tailWord_7211504, baseEnd_7211504] using wordTrace_append hprefix tailTrace_7211504
  have hstable : (prefixWord ++ tailWord_7211504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7211504).length < 2 ^ (prefixWord ++ tailWord_7211504).sum := by decide
  have hdescent : baseEnd_7211504 < baseStart_7211504 := by decide
  rcases family_descends (prefixWord ++ tailWord_7211504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7211507 : List Nat := [1, 1, 1, 2, 2, 2, 7, 1, 1, 5]
def baseStart_7211507 : Nat := 118140960795 + 7211507 * 2 ^ 59
def prefixEnd_7211507 : Nat := 4983230072969 + 3 ^ 40 * 7211507 * 2
def baseEnd_7211507 : Nat := 1234323111421073893132463

theorem tailTrace_7211507 : CollatzResearch.WordTrace tailWord_7211507 prefixEnd_7211507 1234323111421073893132463 := by
  unfold tailWord_7211507
  simp only [CollatzResearch.WordTrace]
  refine ⟨263025268684949241185848775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175350179123299494123899183 263025268684949241185848775)
  ·
    refine ⟨394537903027423861778773163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263025268684949241185848775 394537903027423861778773163)
    ·
      refine ⟨591806854541135792668159745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 394537903027423861778773163 591806854541135792668159745)
      ·
        refine ⟨443855140905851844501119809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 591806854541135792668159745 443855140905851844501119809)
        ·
          refine ⟨332891355679388883375839857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 443855140905851844501119809 332891355679388883375839857)
          ·
            refine ⟨249668516759541662531879893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 332891355679388883375839857 249668516759541662531879893)
            ·
              refine ⟨5851605861551757715590935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 249668516759541662531879893 5851605861551757715590935)
              ·
                refine ⟨8777408792327636573386403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5851605861551757715590935 8777408792327636573386403)
                ·
                  refine ⟨13166113188491454860079605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8777408792327636573386403 13166113188491454860079605)
                  ·
                    refine ⟨1234323111421073893132463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13166113188491454860079605 1234323111421073893132463)
                    ·
                      rfl

theorem cell23_7211507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 7, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 7, 1, 1, 5].length) (baseStart_7211507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7211507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7211507 prefixEnd_7211507 := by exact prefixLift 7211507
  have htrace : WordTrace (prefixWord ++ tailWord_7211507) baseStart_7211507 baseEnd_7211507 := by
    simpa [prefixWord, tailWord_7211507, baseEnd_7211507] using wordTrace_append hprefix tailTrace_7211507
  have hstable : (prefixWord ++ tailWord_7211507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7211507).length < 2 ^ (prefixWord ++ tailWord_7211507).sum := by decide
  have hdescent : baseEnd_7211507 < baseStart_7211507 := by decide
  rcases family_descends (prefixWord ++ tailWord_7211507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7211521 : List Nat := [1, 2, 4, 1, 3, 2, 1, 4, 1, 1, 3]
def baseStart_7211521 : Nat := 118140960795 + 7211521 * 2 ^ 59
def prefixEnd_7211521 : Nat := 4983230072969 + 3 ^ 40 * 7211521 * 2
def baseEnd_7211521 : Nat := 3702976522992384624622325

theorem tailTrace_7211521 : CollatzResearch.WordTrace tailWord_7211521 prefixEnd_7211521 3702976522992384624622325 := by
  unfold tailWord_7211521
  simp only [CollatzResearch.WordTrace]
  refine ⟨263025779306898521576858417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175350519537932347717905611 263025779306898521576858417)
  ·
    refine ⟨197269334480173891182643813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 263025779306898521576858417 197269334480173891182643813)
    ·
      refine ⟨36988000215032604596745715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 197269334480173891182643813 36988000215032604596745715)
      ·
        refine ⟨55482000322548906895118573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36988000215032604596745715 55482000322548906895118573)
        ·
          refine ⟨20805750120955840085669465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55482000322548906895118573 20805750120955840085669465)
          ·
            refine ⟨15604312590716880064252099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20805750120955840085669465 15604312590716880064252099)
            ·
              refine ⟨23406468886075320096378149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15604312590716880064252099 23406468886075320096378149)
              ·
                refine ⟨4388712916139122518070903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23406468886075320096378149 4388712916139122518070903)
                ·
                  refine ⟨6583069374208683777106355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4388712916139122518070903 6583069374208683777106355)
                  ·
                    refine ⟨9874604061313025665659533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6583069374208683777106355 9874604061313025665659533)
                    ·
                      refine ⟨3702976522992384624622325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9874604061313025665659533 3702976522992384624622325)
                      ·
                        rfl

theorem cell23_7211521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 1, 4, 1, 1, 3].length) (baseStart_7211521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7211521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7211521 prefixEnd_7211521 := by exact prefixLift 7211521
  have htrace : WordTrace (prefixWord ++ tailWord_7211521) baseStart_7211521 baseEnd_7211521 := by
    simpa [prefixWord, tailWord_7211521, baseEnd_7211521] using wordTrace_append hprefix tailTrace_7211521
  have hstable : (prefixWord ++ tailWord_7211521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7211521).length < 2 ^ (prefixWord ++ tailWord_7211521).sum := by decide
  have hdescent : baseEnd_7211521 < baseStart_7211521 := by decide
  rcases family_descends (prefixWord ++ tailWord_7211521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7211530 : List Nat := [3, 1, 2, 2, 2, 1, 2, 1, 3, 1, 5]
def baseStart_7211530 : Nat := 118140960795 + 7211530 * 2 ^ 59
def prefixEnd_7211530 : Nat := 4983230072969 + 3 ^ 40 * 7211530 * 2
def baseEnd_7211530 : Nat := 3702981144318275089409783

theorem tailTrace_7211530 : CollatzResearch.WordTrace tailWord_7211530 prefixEnd_7211530 3702981144318275089409783 := by
  unfold tailWord_7211530
  simp only [CollatzResearch.WordTrace]
  refine ⟨65756526890966479028484011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175350738375910610742624029 65756526890966479028484011)
  ·
    refine ⟨98634790336449718542726017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65756526890966479028484011 98634790336449718542726017)
    ·
      refine ⟨73976092752337288907044513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98634790336449718542726017 73976092752337288907044513)
      ·
        refine ⟨55482069564252966680283385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73976092752337288907044513 55482069564252966680283385)
        ·
          refine ⟨41611552173189725010212539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55482069564252966680283385 41611552173189725010212539)
          ·
            refine ⟨62417328259784587515318809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41611552173189725010212539 62417328259784587515318809)
            ·
              refine ⟨46812996194838440636489107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62417328259784587515318809 46812996194838440636489107)
              ·
                refine ⟨70219494292257660954733661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46812996194838440636489107 70219494292257660954733661)
                ·
                  refine ⟨26332310359596622858025123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 70219494292257660954733661 26332310359596622858025123)
                  ·
                    refine ⟨39498465539394934287037685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26332310359596622858025123 39498465539394934287037685)
                    ·
                      refine ⟨3702981144318275089409783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39498465539394934287037685 3702981144318275089409783)
                      ·
                        rfl

theorem cell23_7211530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 2, 1, 3, 1, 5].length) (baseStart_7211530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7211530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7211530 prefixEnd_7211530 := by exact prefixLift 7211530
  have htrace : WordTrace (prefixWord ++ tailWord_7211530) baseStart_7211530 baseEnd_7211530 := by
    simpa [prefixWord, tailWord_7211530, baseEnd_7211530] using wordTrace_append hprefix tailTrace_7211530
  have hstable : (prefixWord ++ tailWord_7211530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7211530).length < 2 ^ (prefixWord ++ tailWord_7211530).sum := by decide
  have hdescent : baseEnd_7211530 < baseStart_7211530 := by decide
  rcases family_descends (prefixWord ++ tailWord_7211530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7211544 : List Nat := [2, 1, 2, 3, 3, 1, 1, 1, 5, 2, 2]
def baseStart_7211544 : Nat := 118140960795 + 7211544 * 2 ^ 59
def prefixEnd_7211544 : Nat := 4983230072969 + 3 ^ 40 * 7211544 * 2
def baseEnd_7211544 : Nat := 3702988333047438034634719

theorem tailTrace_7211544 : CollatzResearch.WordTrace tailWord_7211544 prefixEnd_7211544 3702988333047438034634719 := by
  unfold tailWord_7211544
  simp only [CollatzResearch.WordTrace]
  refine ⟨131513309092907598252472843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175351078790543464336630457 131513309092907598252472843)
  ·
    refine ⟨197269963639361397378709265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131513309092907598252472843 197269963639361397378709265)
    ·
      refine ⟨147952472729521048034031949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 197269963639361397378709265 147952472729521048034031949)
      ·
        refine ⟨55482177273570393012761981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 147952472729521048034031949 55482177273570393012761981)
        ·
          refine ⟨20805816477588897379785743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55482177273570393012761981 20805816477588897379785743)
          ·
            refine ⟨31208724716383346069678615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20805816477588897379785743 31208724716383346069678615)
            ·
              refine ⟨46813087074575019104517923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31208724716383346069678615 46813087074575019104517923)
              ·
                refine ⟨70219630611862528656776885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46813087074575019104517923 70219630611862528656776885)
                ·
                  refine ⟨6583090369862112061572833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 70219630611862528656776885 6583090369862112061572833)
                  ·
                    refine ⟨4937317777396584046179625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6583090369862112061572833 4937317777396584046179625)
                    ·
                      refine ⟨3702988333047438034634719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4937317777396584046179625 3702988333047438034634719)
                      ·
                        rfl

theorem cell23_7211544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 1, 1, 5, 2, 2].length) (baseStart_7211544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7211544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7211544 prefixEnd_7211544 := by exact prefixLift 7211544
  have htrace : WordTrace (prefixWord ++ tailWord_7211544) baseStart_7211544 baseEnd_7211544 := by
    simpa [prefixWord, tailWord_7211544, baseEnd_7211544] using wordTrace_append hprefix tailTrace_7211544
  have hstable : (prefixWord ++ tailWord_7211544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7211544).length < 2 ^ (prefixWord ++ tailWord_7211544).sum := by decide
  have hdescent : baseEnd_7211544 < baseStart_7211544 := by decide
  rcases family_descends (prefixWord ++ tailWord_7211544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7211587 : List Nat := [1, 1, 1, 3, 1, 2, 1, 3, 5, 3, 2]
def baseStart_7211587 : Nat := 118140960795 + 7211587 * 2 ^ 59
def prefixEnd_7211587 : Nat := 4983230072969 + 3 ^ 40 * 7211587 * 2
def baseEnd_7211587 : Nat := 3703010412715581366397021

theorem tailTrace_7211587 : CollatzResearch.WordTrace tailWord_7211587 prefixEnd_7211587 3703010412715581366397021 := by
  unfold tailWord_7211587
  simp only [CollatzResearch.WordTrace]
  refine ⟨263028186524659414848761015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175352124349772943232507343 263028186524659414848761015)
  ·
    refine ⟨394542279786989122273141523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263028186524659414848761015 394542279786989122273141523)
    ·
      refine ⟨591813419680483683409712285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 394542279786989122273141523 591813419680483683409712285)
      ·
        refine ⟨221930032380181381278642107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 591813419680483683409712285 221930032380181381278642107)
        ·
          refine ⟨332895048570272071917963161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 221930032380181381278642107 332895048570272071917963161)
          ·
            refine ⟨249671286427704053938472371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 332895048570272071917963161 249671286427704053938472371)
            ·
              refine ⟨374506929641556080907708557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 249671286427704053938472371 374506929641556080907708557)
              ·
                refine ⟨140440098615583530340390709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 374506929641556080907708557 140440098615583530340390709)
                ·
                  refine ⟨13166259245210955969411629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 140440098615583530340390709 13166259245210955969411629)
                  ·
                    refine ⟨4937347216954108488529361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13166259245210955969411629 4937347216954108488529361)
                    ·
                      refine ⟨3703010412715581366397021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4937347216954108488529361 3703010412715581366397021)
                      ·
                        rfl

theorem cell23_7211587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 3, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 3, 5, 3, 2].length) (baseStart_7211587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7211587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7211587 prefixEnd_7211587 := by exact prefixLift 7211587
  have htrace : WordTrace (prefixWord ++ tailWord_7211587) baseStart_7211587 baseEnd_7211587 := by
    simpa [prefixWord, tailWord_7211587, baseEnd_7211587] using wordTrace_append hprefix tailTrace_7211587
  have hstable : (prefixWord ++ tailWord_7211587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7211587).length < 2 ^ (prefixWord ++ tailWord_7211587).sum := by decide
  have hdescent : baseEnd_7211587 < baseStart_7211587 := by decide
  rcases family_descends (prefixWord ++ tailWord_7211587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7211588 : List Nat := [2, 3, 5, 1, 1, 2, 1, 1, 1, 6]
def baseStart_7211588 : Nat := 118140960795 + 7211588 * 2 ^ 59
def prefixEnd_7211588 : Nat := 4983230072969 + 3 ^ 40 * 7211588 * 2
def baseEnd_7211588 : Nat := 1234336975398745287494839

theorem tailTrace_7211588 : CollatzResearch.WordTrace tailWord_7211588 prefixEnd_7211588 1234336975398745287494839 := by
  unfold tailWord_7211588
  simp only [CollatzResearch.WordTrace]
  refine ⟨131514111498827896009773709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175352148665103861346364945 131514111498827896009773709)
  ·
    refine ⟨49317791812060461003665141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 131514111498827896009773709 49317791812060461003665141)
    ·
      refine ⟨4623542982380668219093607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 49317791812060461003665141 4623542982380668219093607)
      ·
        refine ⟨6935314473571002328640411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4623542982380668219093607 6935314473571002328640411)
        ·
          refine ⟨10402971710356503492960617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6935314473571002328640411 10402971710356503492960617)
          ·
            refine ⟨7802228782767377619720463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10402971710356503492960617 7802228782767377619720463)
            ·
              refine ⟨11703343174151066429580695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7802228782767377619720463 11703343174151066429580695)
              ·
                refine ⟨17555014761226599644371043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11703343174151066429580695 17555014761226599644371043)
                ·
                  refine ⟨26332522141839899466556565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17555014761226599644371043 26332522141839899466556565)
                  ·
                    refine ⟨1234336975398745287494839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26332522141839899466556565 1234336975398745287494839)
                    ·
                      rfl

theorem cell23_7211588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 2, 1, 1, 1, 6].length) (baseStart_7211588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7211588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7211588 prefixEnd_7211588 := by exact prefixLift 7211588
  have htrace : WordTrace (prefixWord ++ tailWord_7211588) baseStart_7211588 baseEnd_7211588 := by
    simpa [prefixWord, tailWord_7211588, baseEnd_7211588] using wordTrace_append hprefix tailTrace_7211588
  have hstable : (prefixWord ++ tailWord_7211588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7211588).length < 2 ^ (prefixWord ++ tailWord_7211588).sum := by decide
  have hdescent : baseEnd_7211588 < baseStart_7211588 := by decide
  rcases family_descends (prefixWord ++ tailWord_7211588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7211594 : List Nat := [3, 1, 2, 1, 1, 6, 1, 1, 1, 3, 3]
def baseStart_7211594 : Nat := 118140960795 + 7211594 * 2 ^ 59
def prefixEnd_7211594 : Nat := 4983230072969 + 3 ^ 40 * 7211594 * 2
def baseEnd_7211594 : Nat := 3703014007080162839009489

theorem tailTrace_7211594 : CollatzResearch.WordTrace tailWord_7211594 prefixEnd_7211594 3703014007080162839009489 := by
  unfold tailWord_7211594
  simp only [CollatzResearch.WordTrace]
  refine ⟨65757110458908513761066459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175352294557089370029510557 65757110458908513761066459)
  ·
    refine ⟨98635665688362770641599689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65757110458908513761066459 98635665688362770641599689)
    ·
      refine ⟨73976749266272077981199767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98635665688362770641599689 73976749266272077981199767)
      ·
        refine ⟨110965123899408116971799651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73976749266272077981199767 110965123899408116971799651)
        ·
          refine ⟨166447685849112175457699477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110965123899408116971799651 166447685849112175457699477)
          ·
            refine ⟨7802235274177133224579663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 166447685849112175457699477 7802235274177133224579663)
            ·
              refine ⟨11703352911265699836869495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7802235274177133224579663 11703352911265699836869495)
              ·
                refine ⟨17555029366898549755304243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11703352911265699836869495 17555029366898549755304243)
                ·
                  refine ⟨26332544050347824632956365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17555029366898549755304243 26332544050347824632956365)
                  ·
                    refine ⟨9874704018880434237358637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26332544050347824632956365 9874704018880434237358637)
                    ·
                      refine ⟨3703014007080162839009489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9874704018880434237358637 3703014007080162839009489)
                      ·
                        rfl

theorem cell23_7211594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 6, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 6, 1, 1, 1, 3, 3].length) (baseStart_7211594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7211594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7211594 prefixEnd_7211594 := by exact prefixLift 7211594
  have htrace : WordTrace (prefixWord ++ tailWord_7211594) baseStart_7211594 baseEnd_7211594 := by
    simpa [prefixWord, tailWord_7211594, baseEnd_7211594] using wordTrace_append hprefix tailTrace_7211594
  have hstable : (prefixWord ++ tailWord_7211594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7211594).length < 2 ^ (prefixWord ++ tailWord_7211594).sum := by decide
  have hdescent : baseEnd_7211594 < baseStart_7211594 := by decide
  rcases family_descends (prefixWord ++ tailWord_7211594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7211612 : List Nat := [2, 2, 4, 1, 4, 1, 1, 3, 1, 2, 2]
def baseStart_7211612 : Nat := 118140960795 + 7211612 * 2 ^ 59
def prefixEnd_7211612 : Nat := 4983230072969 + 3 ^ 40 * 7211612 * 2
def baseEnd_7211612 : Nat := 3703023249731943768584407

theorem tailTrace_7211612 : CollatzResearch.WordTrace tailWord_7211612 prefixEnd_7211612 3703023249731943768584407 := by
  unfold tailWord_7211612
  simp only [CollatzResearch.WordTrace]
  refine ⟨131514549174784422059210545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175352732233045896078947393 131514549174784422059210545)
  ·
    refine ⟨98635911881088316544407909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131514549174784422059210545 98635911881088316544407909)
    ·
      refine ⟨18494233477704059352076483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 98635911881088316544407909 18494233477704059352076483)
      ·
        refine ⟨27741350216556089028114725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18494233477704059352076483 27741350216556089028114725)
        ·
          refine ⟨5201503165604266692771511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27741350216556089028114725 5201503165604266692771511)
          ·
            refine ⟨7802254748406400039157267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5201503165604266692771511 7802254748406400039157267)
            ·
              refine ⟨11703382122609600058735901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7802254748406400039157267 11703382122609600058735901)
              ·
                refine ⟨4388768295978600022025963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11703382122609600058735901 4388768295978600022025963)
                ·
                  refine ⟨6583152443967900033038945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4388768295978600022025963 6583152443967900033038945)
                  ·
                    refine ⟨4937364332975925024779209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6583152443967900033038945 4937364332975925024779209)
                    ·
                      refine ⟨3703023249731943768584407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4937364332975925024779209 3703023249731943768584407)
                      ·
                        rfl

theorem cell23_7211612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 4, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 4, 1, 1, 3, 1, 2, 2].length) (baseStart_7211612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7211612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7211612 prefixEnd_7211612 := by exact prefixLift 7211612
  have htrace : WordTrace (prefixWord ++ tailWord_7211612) baseStart_7211612 baseEnd_7211612 := by
    simpa [prefixWord, tailWord_7211612, baseEnd_7211612] using wordTrace_append hprefix tailTrace_7211612
  have hstable : (prefixWord ++ tailWord_7211612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7211612).length < 2 ^ (prefixWord ++ tailWord_7211612).sum := by decide
  have hdescent : baseEnd_7211612 < baseStart_7211612 := by decide
  rcases family_descends (prefixWord ++ tailWord_7211612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7211645 : List Nat := [1, 4, 1, 1, 6, 1, 2, 1, 2, 1, 3]
def baseStart_7211645 : Nat := 118140960795 + 7211645 * 2 ^ 59
def prefixEnd_7211645 : Nat := 4983230072969 + 3 ^ 40 * 7211645 * 2
def baseEnd_7211645 : Nat := 3703040194593542139471755

theorem tailTrace_7211645 : CollatzResearch.WordTrace tailWord_7211645 prefixEnd_7211645 3703040194593542139471755 := by
  unfold tailWord_7211645
  simp only [CollatzResearch.WordTrace]
  refine ⟨263030301958449290754372389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175353534638966193836248259 263030301958449290754372389)
  ·
    refine ⟨49318181617209242016444823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 263030301958449290754372389 49318181617209242016444823)
    ·
      refine ⟨73977272425813863024667235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49318181617209242016444823 73977272425813863024667235)
      ·
        refine ⟨110965908638720794537000853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73977272425813863024667235 110965908638720794537000853)
        ·
          refine ⟨5201526967440037243921915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 110965908638720794537000853 5201526967440037243921915)
          ·
            refine ⟨7802290451160055865882873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5201526967440037243921915 7802290451160055865882873)
            ·
              refine ⟨5851717838370041899412155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7802290451160055865882873 5851717838370041899412155)
              ·
                refine ⟨8777576757555062849118233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5851717838370041899412155 8777576757555062849118233)
                ·
                  refine ⟨6583182568166297136838675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8777576757555062849118233 6583182568166297136838675)
                  ·
                    refine ⟨9874773852249445705258013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6583182568166297136838675 9874773852249445705258013)
                    ·
                      refine ⟨3703040194593542139471755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9874773852249445705258013 3703040194593542139471755)
                      ·
                        rfl

theorem cell23_7211645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 6, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 6, 1, 2, 1, 2, 1, 3].length) (baseStart_7211645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7211645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7211645 prefixEnd_7211645 := by exact prefixLift 7211645
  have htrace : WordTrace (prefixWord ++ tailWord_7211645) baseStart_7211645 baseEnd_7211645 := by
    simpa [prefixWord, tailWord_7211645, baseEnd_7211645] using wordTrace_append hprefix tailTrace_7211645
  have hstable : (prefixWord ++ tailWord_7211645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7211645).length < 2 ^ (prefixWord ++ tailWord_7211645).sum := by decide
  have hdescent : baseEnd_7211645 < baseStart_7211645 := by decide
  rcases family_descends (prefixWord ++ tailWord_7211645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7211724 : List Nat := [2, 2, 1, 5, 1, 2, 1, 1, 1, 3, 4]
def baseStart_7211724 : Nat := 118140960795 + 7211724 * 2 ^ 59
def prefixEnd_7211724 : Nat := 4983230072969 + 3 ^ 40 * 7211724 * 2
def baseEnd_7211724 : Nat := 3703080759565247330383891

theorem tailTrace_7211724 : CollatzResearch.WordTrace tailWord_7211724 prefixEnd_7211724 3703080759565247330383891 := by
  unfold tailWord_7211724
  simp only [CollatzResearch.WordTrace]
  refine ⟨131516591662581543623249113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175355455550108724830998817 131516591662581543623249113)
  ·
    refine ⟨98637443746936157717436835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131516591662581543623249113 98637443746936157717436835)
    ·
      refine ⟨147956165620404236576155253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98637443746936157717436835 147956165620404236576155253)
      ·
        refine ⟨13870890526912897179014555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 147956165620404236576155253 13870890526912897179014555)
        ·
          refine ⟨20806335790369345768521833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13870890526912897179014555 20806335790369345768521833)
          ·
            refine ⟨15604751842777009326391375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20806335790369345768521833 15604751842777009326391375)
            ·
              refine ⟨23407127764165513989587063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15604751842777009326391375 23407127764165513989587063)
              ·
                refine ⟨35110691646248270984380595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23407127764165513989587063 35110691646248270984380595)
                ·
                  refine ⟨52666037469372406476570893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35110691646248270984380595 52666037469372406476570893)
                  ·
                    refine ⟨19749764051014652428714085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 52666037469372406476570893 19749764051014652428714085)
                    ·
                      refine ⟨3703080759565247330383891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19749764051014652428714085 3703080759565247330383891)
                      ·
                        rfl

theorem cell23_7211724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 1, 1, 1, 3, 4].length) (baseStart_7211724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7211724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7211724 prefixEnd_7211724 := by exact prefixLift 7211724
  have htrace : WordTrace (prefixWord ++ tailWord_7211724) baseStart_7211724 baseEnd_7211724 := by
    simpa [prefixWord, tailWord_7211724, baseEnd_7211724] using wordTrace_append hprefix tailTrace_7211724
  have hstable : (prefixWord ++ tailWord_7211724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7211724).length < 2 ^ (prefixWord ++ tailWord_7211724).sum := by decide
  have hdescent : baseEnd_7211724 < baseStart_7211724 := by decide
  rcases family_descends (prefixWord ++ tailWord_7211724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7211808 : List Nat := [2, 1, 1, 5, 1, 4, 1, 1, 3, 1, 3]
def baseStart_7211808 : Nat := 118140960795 + 7211808 * 2 ^ 59
def prefixEnd_7211808 : Nat := 4983230072969 + 3 ^ 40 * 7211808 * 2
def baseEnd_7211808 : Nat := 3703123891940225001733505

theorem tailTrace_7211808 : CollatzResearch.WordTrace tailWord_7211808 prefixEnd_7211808 3703123891940225001733505 := by
  unfold tailWord_7211808
  simp only [CollatzResearch.WordTrace]
  refine ⟨131518123528429384796278039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175357498037905846395037385 131518123528429384796278039)
  ·
    refine ⟨197277185292644077194417059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131518123528429384796278039 197277185292644077194417059)
    ·
      refine ⟨295915777938966115791625589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197277185292644077194417059 295915777938966115791625589)
      ·
        refine ⟨27742104181778073355464899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 295915777938966115791625589 27742104181778073355464899)
        ·
          refine ⟨41613156272667110033197349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27742104181778073355464899 41613156272667110033197349)
          ·
            refine ⟨7802466801125083131224503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41613156272667110033197349 7802466801125083131224503)
            ·
              refine ⟨11703700201687624696836755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7802466801125083131224503 11703700201687624696836755)
              ·
                refine ⟨17555550302531437045255133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11703700201687624696836755 17555550302531437045255133)
                ·
                  refine ⟨6583331363449288891970675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17555550302531437045255133 6583331363449288891970675)
                  ·
                    refine ⟨9874997045173933337956013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6583331363449288891970675 9874997045173933337956013)
                    ·
                      refine ⟨3703123891940225001733505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9874997045173933337956013 3703123891940225001733505)
                      ·
                        rfl

theorem cell23_7211808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 4, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 4, 1, 1, 3, 1, 3].length) (baseStart_7211808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7211808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7211808 prefixEnd_7211808 := by exact prefixLift 7211808
  have htrace : WordTrace (prefixWord ++ tailWord_7211808) baseStart_7211808 baseEnd_7211808 := by
    simpa [prefixWord, tailWord_7211808, baseEnd_7211808] using wordTrace_append hprefix tailTrace_7211808
  have hstable : (prefixWord ++ tailWord_7211808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7211808).length < 2 ^ (prefixWord ++ tailWord_7211808).sum := by decide
  have hdescent : baseEnd_7211808 < baseStart_7211808 := by decide
  rcases family_descends (prefixWord ++ tailWord_7211808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7211831 : List Nat := [1, 1, 3, 1, 2, 1, 4, 1, 5, 2, 2]
def baseStart_7211831 : Nat := 118140960795 + 7211831 * 2 ^ 59
def prefixEnd_7211831 : Nat := 4983230072969 + 3 ^ 40 * 7211831 * 2
def baseEnd_7211831 : Nat := 3703135701995278411745899

theorem tailTrace_7211831 : CollatzResearch.WordTrace tailWord_7211831 prefixEnd_7211831 3703135701995278411745899 := by
  unfold tailWord_7211831
  simp only [CollatzResearch.WordTrace]
  refine ⟨263037085935775444520643347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175358057290516963013762231 263037085935775444520643347)
  ·
    refine ⟨394555628903663166780965021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263037085935775444520643347 394555628903663166780965021)
    ·
      refine ⟨147958360838873687542861883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 394555628903663166780965021 147958360838873687542861883)
      ·
        refine ⟨221937541258310531314292825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147958360838873687542861883 221937541258310531314292825)
        ·
          refine ⟨166453155943732898485719619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 221937541258310531314292825 166453155943732898485719619)
          ·
            refine ⟨249679733915599347728579429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 166453155943732898485719619 249679733915599347728579429)
            ·
              refine ⟨46814950109174877699108643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 249679733915599347728579429 46814950109174877699108643)
              ·
                refine ⟨70222425163762316548662965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46814950109174877699108643 70222425163762316548662965)
                ·
                  refine ⟨6583352359102717176437153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 70222425163762316548662965 6583352359102717176437153)
                  ·
                    refine ⟨4937514269327037882327865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6583352359102717176437153 4937514269327037882327865)
                    ·
                      refine ⟨3703135701995278411745899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4937514269327037882327865 3703135701995278411745899)
                      ·
                        rfl

theorem cell23_7211831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 4, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 4, 1, 5, 2, 2].length) (baseStart_7211831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7211831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7211831 prefixEnd_7211831 := by exact prefixLift 7211831
  have htrace : WordTrace (prefixWord ++ tailWord_7211831) baseStart_7211831 baseEnd_7211831 := by
    simpa [prefixWord, tailWord_7211831, baseEnd_7211831] using wordTrace_append hprefix tailTrace_7211831
  have hstable : (prefixWord ++ tailWord_7211831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7211831).length < 2 ^ (prefixWord ++ tailWord_7211831).sum := by decide
  have hdescent : baseEnd_7211831 < baseStart_7211831 := by decide
  rcases family_descends (prefixWord ++ tailWord_7211831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7211865 : List Nat := [1, 2, 1, 2, 2, 5, 1, 4, 1, 2, 2]
def baseStart_7211865 : Nat := 118140960795 + 7211865 * 2 ^ 59
def prefixEnd_7211865 : Nat := 4983230072969 + 3 ^ 40 * 7211865 * 2
def baseEnd_7211865 : Nat := 3703153160337531278720743

theorem tailTrace_7211865 : CollatzResearch.WordTrace tailWord_7211865 prefixEnd_7211865 3703153160337531278720743 := by
  unfold tailWord_7211865
  simp only [CollatzResearch.WordTrace]
  refine ⟨263038326017652268327381049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175358884011768178884920699 263038326017652268327381049)
  ·
    refine ⟨197278744513239201245535787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 263038326017652268327381049 197278744513239201245535787)
    ·
      refine ⟨295918116769858801868303681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197278744513239201245535787 295918116769858801868303681)
      ·
        refine ⟨221938587577394101401227761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 295918116769858801868303681 221938587577394101401227761)
        ·
          refine ⟨166453940683045576050920821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 221938587577394101401227761 166453940683045576050920821)
          ·
            refine ⟨15605056939035522754773827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 166453940683045576050920821 15605056939035522754773827)
            ·
              refine ⟨23407585408553284132160741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15605056939035522754773827 23407585408553284132160741)
              ·
                refine ⟨4388922264103740774780139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23407585408553284132160741 4388922264103740774780139)
                ·
                  refine ⟨6583383396155611162170209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4388922264103740774780139 6583383396155611162170209)
                  ·
                    refine ⟨4937537547116708371627657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6583383396155611162170209 4937537547116708371627657)
                    ·
                      refine ⟨3703153160337531278720743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4937537547116708371627657 3703153160337531278720743)
                      ·
                        rfl

theorem cell23_7211865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 1, 4, 1, 2, 2].length) (baseStart_7211865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7211865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7211865 prefixEnd_7211865 := by exact prefixLift 7211865
  have htrace : WordTrace (prefixWord ++ tailWord_7211865) baseStart_7211865 baseEnd_7211865 := by
    simpa [prefixWord, tailWord_7211865, baseEnd_7211865] using wordTrace_append hprefix tailTrace_7211865
  have hstable : (prefixWord ++ tailWord_7211865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7211865).length < 2 ^ (prefixWord ++ tailWord_7211865).sum := by decide
  have hdescent : baseEnd_7211865 < baseStart_7211865 := by decide
  rcases family_descends (prefixWord ++ tailWord_7211865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7211891 : List Nat := [1, 1, 1, 2, 2, 1, 6, 1, 3, 3, 2]
def baseStart_7211891 : Nat := 118140960795 + 7211891 * 2 ^ 59
def prefixEnd_7211891 : Nat := 4983230072969 + 3 ^ 40 * 7211891 * 2
def baseEnd_7211891 : Nat := 3703166510834548176995623

theorem tailTrace_7211891 : CollatzResearch.WordTrace tailWord_7211891 prefixEnd_7211891 3703166510834548176995623 := by
  unfold tailWord_7211891
  simp only [CollatzResearch.WordTrace]
  refine ⟨263039274315558074767827527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175359516210372049845218351 263039274315558074767827527)
  ·
    refine ⟨394558911473337112151741291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263039274315558074767827527 394558911473337112151741291)
    ·
      refine ⟨591838367210005668227611937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 394558911473337112151741291 591838367210005668227611937)
      ·
        refine ⟨443878775407504251170708953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 591838367210005668227611937 443878775407504251170708953)
        ·
          refine ⟨332909081555628188378031715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 443878775407504251170708953 332909081555628188378031715)
          ·
            refine ⟨499363622333442282567047573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 332909081555628188378031715 499363622333442282567047573)
            ·
              refine ⟨23407669796880106995330355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 499363622333442282567047573 23407669796880106995330355)
              ·
                refine ⟨35111504695320160492995533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23407669796880106995330355 35111504695320160492995533)
                ·
                  refine ⟨13166814260745060184873325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35111504695320160492995533 13166814260745060184873325)
                  ·
                    refine ⟨4937555347779397569327497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13166814260745060184873325 4937555347779397569327497)
                    ·
                      refine ⟨3703166510834548176995623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4937555347779397569327497 3703166510834548176995623)
                      ·
                        rfl

theorem cell23_7211891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 6, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 6, 1, 3, 3, 2].length) (baseStart_7211891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7211891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7211891 prefixEnd_7211891 := by exact prefixLift 7211891
  have htrace : WordTrace (prefixWord ++ tailWord_7211891) baseStart_7211891 baseEnd_7211891 := by
    simpa [prefixWord, tailWord_7211891, baseEnd_7211891] using wordTrace_append hprefix tailTrace_7211891
  have hstable : (prefixWord ++ tailWord_7211891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7211891).length < 2 ^ (prefixWord ++ tailWord_7211891).sum := by decide
  have hdescent : baseEnd_7211891 < baseStart_7211891 := by decide
  rcases family_descends (prefixWord ++ tailWord_7211891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7211932 : List Nat := [2, 2, 3, 3, 2, 1, 3, 1, 2, 1, 3]
def baseStart_7211932 : Nat := 118140960795 + 7211932 * 2 ^ 59
def prefixEnd_7211932 : Nat := 4983230072969 + 3 ^ 40 * 7211932 * 2
def baseEnd_7211932 : Nat := 3703187563541382516582935

theorem tailTrace_7211932 : CollatzResearch.WordTrace tailWord_7211932 prefixEnd_7211932 3703187563541382516582935 := by
  unfold tailWord_7211932
  simp only [CollatzResearch.WordTrace]
  refine ⟨131520384854204769385035025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175360513138939692513380033 131520384854204769385035025)
  ·
    refine ⟨98640288640653577038776269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131520384854204769385035025 98640288640653577038776269)
    ·
      refine ⟨36990108240245091389541101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98640288640653577038776269 36990108240245091389541101)
      ·
        refine ⟨13871290590091909271077913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36990108240245091389541101 13871290590091909271077913)
        ·
          refine ⟨10403467942568931953308435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13871290590091909271077913 10403467942568931953308435)
          ·
            refine ⟨15605201913853397929962653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10403467942568931953308435 15605201913853397929962653)
            ·
              refine ⟨5851950717695024223735995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15605201913853397929962653 5851950717695024223735995)
              ·
                refine ⟨8777926076542536335603993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5851950717695024223735995 8777926076542536335603993)
                ·
                  refine ⟨6583444557406902251702995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8777926076542536335603993 6583444557406902251702995)
                  ·
                    refine ⟨9875166836110353377554493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6583444557406902251702995 9875166836110353377554493)
                    ·
                      refine ⟨3703187563541382516582935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9875166836110353377554493 3703187563541382516582935)
                      ·
                        rfl

theorem cell23_7211932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 3, 1, 2, 1, 3].length) (baseStart_7211932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7211932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7211932 prefixEnd_7211932 := by exact prefixLift 7211932
  have htrace : WordTrace (prefixWord ++ tailWord_7211932) baseStart_7211932 baseEnd_7211932 := by
    simpa [prefixWord, tailWord_7211932, baseEnd_7211932] using wordTrace_append hprefix tailTrace_7211932
  have hstable : (prefixWord ++ tailWord_7211932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7211932).length < 2 ^ (prefixWord ++ tailWord_7211932).sum := by decide
  have hdescent : baseEnd_7211932 < baseStart_7211932 := by decide
  rcases family_descends (prefixWord ++ tailWord_7211932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7211989 : List Nat := [1, 3, 2, 3, 3, 2, 2, 1, 2, 2, 2]
def baseStart_7211989 : Nat := 118140960795 + 7211989 * 2 ^ 59
def prefixEnd_7211989 : Nat := 4983230072969 + 3 ^ 40 * 7211989 * 2
def baseEnd_7211989 : Nat := 3703216831938688793570173

theorem tailTrace_7211989 : CollatzResearch.WordTrace tailWord_7211989 prefixEnd_7211989 3703216831938688793570173 := by
  unfold tailWord_7211989
  simp only [CollatzResearch.WordTrace]
  refine ⟨263042848669203037504895021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175361899112802025003263347 263042848669203037504895021)
  ·
    refine ⟨98641068250951139064335633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 263042848669203037504895021 98641068250951139064335633)
    ·
      refine ⟨73980801188213354298251725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98641068250951139064335633 73980801188213354298251725)
      ·
        refine ⟨27742800445580007861844397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73980801188213354298251725 27742800445580007861844397)
        ·
          refine ⟨10403550167092502948191649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27742800445580007861844397 10403550167092502948191649)
          ·
            refine ⟨7802662625319377211143737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10403550167092502948191649 7802662625319377211143737)
            ·
              refine ⟨5851996968989532908357803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7802662625319377211143737 5851996968989532908357803)
              ·
                refine ⟨8777995453484299362536705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5851996968989532908357803 8777995453484299362536705)
                ·
                  refine ⟨6583496590113224521902529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8777995453484299362536705 6583496590113224521902529)
                  ·
                    refine ⟨4937622442584918391426897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6583496590113224521902529 4937622442584918391426897)
                    ·
                      refine ⟨3703216831938688793570173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4937622442584918391426897 3703216831938688793570173)
                      ·
                        rfl

theorem cell23_7211989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 2, 2, 1, 2, 2, 2].length) (baseStart_7211989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7211989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7211989 prefixEnd_7211989 := by exact prefixLift 7211989
  have htrace : WordTrace (prefixWord ++ tailWord_7211989) baseStart_7211989 baseEnd_7211989 := by
    simpa [prefixWord, tailWord_7211989, baseEnd_7211989] using wordTrace_append hprefix tailTrace_7211989
  have hstable : (prefixWord ++ tailWord_7211989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7211989).length < 2 ^ (prefixWord ++ tailWord_7211989).sum := by decide
  have hdescent : baseEnd_7211989 < baseStart_7211989 := by decide
  rcases family_descends (prefixWord ++ tailWord_7211989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7212011 : List Nat := [1, 1, 1, 1, 2, 3, 1, 1, 6, 4, 2]
def baseStart_7212011 : Nat := 118140960795 + 7212011 * 2 ^ 59
def prefixEnd_7212011 : Nat := 4983230072969 + 3 ^ 40 * 7212011 * 2
def baseEnd_7212011 : Nat := 3703228128513087707495071

theorem tailTrace_7212011 : CollatzResearch.WordTrace tailWord_7212011 prefixEnd_7212011 3703228128513087707495071 := by
  unfold tailWord_7212011
  simp only [CollatzResearch.WordTrace]
  refine ⟨263043651075123335262195887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175362434050082223508130591 263043651075123335262195887)
  ·
    refine ⟨394565476612685002893293831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263043651075123335262195887 394565476612685002893293831)
    ·
      refine ⟨591848214919027504339940747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 394565476612685002893293831 591848214919027504339940747)
      ·
        refine ⟨887772322378541256509911121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 591848214919027504339940747 887772322378541256509911121)
        ·
          refine ⟨665829241783905942382433341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 887772322378541256509911121 665829241783905942382433341)
          ·
            refine ⟨249685965668964728393412503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 665829241783905942382433341 249685965668964728393412503)
            ·
              refine ⟨374528948503447092590118755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 249685965668964728393412503 374528948503447092590118755)
              ·
                refine ⟨561793422755170638885178133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 374528948503447092590118755 561793422755170638885178133)
                ·
                  refine ⟨26334066691648623697742725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 561793422755170638885178133 26334066691648623697742725)
                  ·
                    refine ⟨4937637504684116943326761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26334066691648623697742725 4937637504684116943326761)
                    ·
                      refine ⟨3703228128513087707495071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4937637504684116943326761 3703228128513087707495071)
                      ·
                        rfl

theorem cell23_7212011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 1, 6, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 1, 6, 4, 2].length) (baseStart_7212011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7212011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7212011 prefixEnd_7212011 := by exact prefixLift 7212011
  have htrace : WordTrace (prefixWord ++ tailWord_7212011) baseStart_7212011 baseEnd_7212011 := by
    simpa [prefixWord, tailWord_7212011, baseEnd_7212011] using wordTrace_append hprefix tailTrace_7212011
  have hstable : (prefixWord ++ tailWord_7212011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7212011).length < 2 ^ (prefixWord ++ tailWord_7212011).sum := by decide
  have hdescent : baseEnd_7212011 < baseStart_7212011 := by decide
  rcases family_descends (prefixWord ++ tailWord_7212011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7212024 : List Nat := [2, 1, 2, 1, 1, 3, 1, 3, 2, 1, 6]
def baseStart_7212024 : Nat := 118140960795 + 7212024 * 2 ^ 59
def prefixEnd_7212024 : Nat := 4983230072969 + 3 ^ 40 * 7212024 * 2
def baseEnd_7212024 : Nat := 3703234803761596156632511

theorem tailTrace_7212024 : CollatzResearch.WordTrace tailWord_7212024 prefixEnd_7212024 3703234803761596156632511 := by
  unfold tailWord_7212024
  simp only [CollatzResearch.WordTrace]
  refine ⟨131522062612038119241209563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175362750149384158988279417 131522062612038119241209563)
  ·
    refine ⟨197283093918057178861814345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131522062612038119241209563 197283093918057178861814345)
    ·
      refine ⟨147962320438542884146360759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 197283093918057178861814345 147962320438542884146360759)
      ·
        refine ⟨221943480657814326219541139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147962320438542884146360759 221943480657814326219541139)
        ·
          refine ⟨332915220986721489329311709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 221943480657814326219541139 332915220986721489329311709)
          ·
            refine ⟨124843207870020558498491891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 332915220986721489329311709 124843207870020558498491891)
            ·
              refine ⟨187264811805030837747737837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 124843207870020558498491891 187264811805030837747737837)
              ·
                refine ⟨70224304426886564155401689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 187264811805030837747737837 70224304426886564155401689)
                ·
                  refine ⟨52668228320164923116551267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 70224304426886564155401689 52668228320164923116551267)
                  ·
                    refine ⟨79002342480247384674826901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 52668228320164923116551267 79002342480247384674826901)
                    ·
                      refine ⟨3703234803761596156632511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 79002342480247384674826901 3703234803761596156632511)
                      ·
                        rfl

theorem cell23_7212024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 3, 2, 1, 6].length) (baseStart_7212024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7212024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7212024 prefixEnd_7212024 := by exact prefixLift 7212024
  have htrace : WordTrace (prefixWord ++ tailWord_7212024) baseStart_7212024 baseEnd_7212024 := by
    simpa [prefixWord, tailWord_7212024, baseEnd_7212024] using wordTrace_append hprefix tailTrace_7212024
  have hstable : (prefixWord ++ tailWord_7212024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7212024).length < 2 ^ (prefixWord ++ tailWord_7212024).sum := by decide
  have hdescent : baseEnd_7212024 < baseStart_7212024 := by decide
  rcases family_descends (prefixWord ++ tailWord_7212024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7212065 : List Nat := [1, 2, 3, 2, 3, 3, 1, 1, 2, 2, 3]
def baseStart_7212065 : Nat := 118140960795 + 7212065 * 2 ^ 59
def prefixEnd_7212065 : Nat := 4983230072969 + 3 ^ 40 * 7212065 * 2
def baseEnd_7212065 : Nat := 3703255856468430496219823

theorem tailTrace_7212065 : CollatzResearch.WordTrace tailWord_7212065 prefixEnd_7212065 3703255856468430496219823 := by
  unfold tailWord_7212065
  simp only [CollatzResearch.WordTrace]
  refine ⟨263045620616927702484661649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175363747077951801656441099 263045620616927702484661649)
  ·
    refine ⟨197284215462695776863496237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 263045620616927702484661649 197284215462695776863496237)
    ·
      refine ⟨73981580798510916323811089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 197284215462695776863496237 73981580798510916323811089)
      ·
        refine ⟨55486185598883187242858317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73981580798510916323811089 55486185598883187242858317)
        ·
          refine ⟨20807319599581195216071869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55486185598883187242858317 20807319599581195216071869)
          ·
            refine ⟨7802744849842948206026951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20807319599581195216071869 7802744849842948206026951)
            ·
              refine ⟨11704117274764422309040427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7802744849842948206026951 11704117274764422309040427)
              ·
                refine ⟨17556175912146633463560641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11704117274764422309040427 17556175912146633463560641)
                ·
                  refine ⟨13167131934109975097670481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17556175912146633463560641 13167131934109975097670481)
                  ·
                    refine ⟨9875348950582481323252861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13167131934109975097670481 9875348950582481323252861)
                    ·
                      refine ⟨3703255856468430496219823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9875348950582481323252861 3703255856468430496219823)
                      ·
                        rfl

theorem cell23_7212065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 3, 1, 1, 2, 2, 3].length) (baseStart_7212065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7212065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7212065 prefixEnd_7212065 := by exact prefixLift 7212065
  have htrace : WordTrace (prefixWord ++ tailWord_7212065) baseStart_7212065 baseEnd_7212065 := by
    simpa [prefixWord, tailWord_7212065, baseEnd_7212065] using wordTrace_append hprefix tailTrace_7212065
  have hstable : (prefixWord ++ tailWord_7212065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7212065).length < 2 ^ (prefixWord ++ tailWord_7212065).sum := by decide
  have hdescent : baseEnd_7212065 < baseStart_7212065 := by decide
  rcases family_descends (prefixWord ++ tailWord_7212065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7212101 : List Nat := [1, 3, 1, 1, 1, 3, 2, 1, 5, 1, 4]
def baseStart_7212101 : Nat := 118140960795 + 7212101 * 2 ^ 59
def prefixEnd_7212101 : Nat := 4983230072969 + 3 ^ 40 * 7212101 * 2
def baseEnd_7212101 : Nat := 3703274341771992355369657

theorem tailTrace_7212101 : CollatzResearch.WordTrace tailWord_7212101 prefixEnd_7212101 3703274341771992355369657 := by
  unfold tailWord_7212101
  simp only [CollatzResearch.WordTrace]
  refine ⟨263046933644797280632972157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175364622429864853755314771 263046933644797280632972157)
  ·
    refine ⟨98642600116798980237364559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 263046933644797280632972157 98642600116798980237364559)
    ·
      refine ⟨147963900175198470356046839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98642600116798980237364559 147963900175198470356046839)
      ·
        refine ⟨221945850262797705534070259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147963900175198470356046839 221945850262797705534070259)
        ·
          refine ⟨332918775394196558301105389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 221945850262797705534070259 332918775394196558301105389)
          ·
            refine ⟨124844540772823709362914521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 332918775394196558301105389 124844540772823709362914521)
            ·
              refine ⟨93633405579617782022185891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 124844540772823709362914521 93633405579617782022185891)
              ·
                refine ⟨140450108369426673033278837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 93633405579617782022185891 140450108369426673033278837)
                ·
                  refine ⟨13167197659633750596869891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 140450108369426673033278837 13167197659633750596869891)
                  ·
                    refine ⟨19750796489450625895304837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13167197659633750596869891 19750796489450625895304837)
                    ·
                      refine ⟨3703274341771992355369657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19750796489450625895304837 3703274341771992355369657)
                      ·
                        rfl

theorem cell23_7212101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 1, 5, 1, 4].length) (baseStart_7212101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7212101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7212101 prefixEnd_7212101 := by exact prefixLift 7212101
  have htrace : WordTrace (prefixWord ++ tailWord_7212101) baseStart_7212101 baseEnd_7212101 := by
    simpa [prefixWord, tailWord_7212101, baseEnd_7212101] using wordTrace_append hprefix tailTrace_7212101
  have hstable : (prefixWord ++ tailWord_7212101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7212101).length < 2 ^ (prefixWord ++ tailWord_7212101).sum := by decide
  have hdescent : baseEnd_7212101 < baseStart_7212101 := by decide
  rcases family_descends (prefixWord ++ tailWord_7212101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7212102 : List Nat := [6, 1, 1, 1, 1, 3, 3, 1, 6]
def baseStart_7212102 : Nat := 118140960795 + 7212102 * 2 ^ 59
def prefixEnd_7212102 : Nat := 4983230072969 + 3 ^ 40 * 7212102 * 2
def baseEnd_7212102 : Nat := 411474983916960761273017

theorem tailTrace_7212102 : CollatzResearch.WordTrace tailWord_7212102 prefixEnd_7212102 411474983916960761273017 := by
  unfold tailWord_7212102
  simp only [CollatzResearch.WordTrace]
  refine ⟨8220217816181051806367455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 175364646745195771869172373 8220217816181051806367455)
  ·
    refine ⟨12330326724271577709551183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8220217816181051806367455 12330326724271577709551183)
    ·
      refine ⟨18495490086407366564326775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12330326724271577709551183 18495490086407366564326775)
      ·
        refine ⟨27743235129611049846490163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18495490086407366564326775 27743235129611049846490163)
        ·
          refine ⟨41614852694416574769735245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27743235129611049846490163 41614852694416574769735245)
          ·
            refine ⟨15605569760406215538650717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41614852694416574769735245 15605569760406215538650717)
            ·
              refine ⟨5852088660152330826994019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15605569760406215538650717 5852088660152330826994019)
              ·
                refine ⟨8778132990228496240491029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5852088660152330826994019 8778132990228496240491029)
                ·
                  refine ⟨411474983916960761273017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8778132990228496240491029 411474983916960761273017)
                  ·
                    rfl

theorem cell23_7212102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 3, 1, 6].length) (baseStart_7212102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7212102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7212102 prefixEnd_7212102 := by exact prefixLift 7212102
  have htrace : WordTrace (prefixWord ++ tailWord_7212102) baseStart_7212102 baseEnd_7212102 := by
    simpa [prefixWord, tailWord_7212102, baseEnd_7212102] using wordTrace_append hprefix tailTrace_7212102
  have hstable : (prefixWord ++ tailWord_7212102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7212102).length < 2 ^ (prefixWord ++ tailWord_7212102).sum := by decide
  have hdescent : baseEnd_7212102 < baseStart_7212102 := by decide
  rcases family_descends (prefixWord ++ tailWord_7212102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7212111 : List Nat := [1, 1, 2, 1, 1, 2, 2, 1, 8, 4]
def baseStart_7212111 : Nat := 118140960795 + 7212111 * 2 ^ 59
def prefixEnd_7212111 : Nat := 4983230072969 + 3 ^ 40 * 7212111 * 2
def baseEnd_7212111 : Nat := 1234426492192845772081537

theorem tailTrace_7212111 : CollatzResearch.WordTrace tailWord_7212111 prefixEnd_7212111 1234426492192845772081537 := by
  unfold tailWord_7212111
  simp only [CollatzResearch.WordTrace]
  refine ⟨263047298374761052340836187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175364865583174034893890791 263047298374761052340836187)
  ·
    refine ⟨394570947562141578511254281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263047298374761052340836187 394570947562141578511254281)
    ·
      refine ⟨295928210671606183883440711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 394570947562141578511254281 295928210671606183883440711)
      ·
        refine ⟨443892316007409275825161067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 295928210671606183883440711 443892316007409275825161067)
        ·
          refine ⟨665838474011113913737741601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 443892316007409275825161067 665838474011113913737741601)
          ·
            refine ⟨499378855508335435303306201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 665838474011113913737741601 499378855508335435303306201)
            ·
              refine ⟨374534141631251576477479651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 499378855508335435303306201 374534141631251576477479651)
              ·
                refine ⟨561801212446877364716219477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 374534141631251576477479651 561801212446877364716219477)
                ·
                  refine ⟨6583607958361844117768197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 561801212446877364716219477 6583607958361844117768197)
                  ·
                    refine ⟨1234426492192845772081537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6583607958361844117768197 1234426492192845772081537)
                    ·
                      rfl

theorem cell23_7212111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 1, 8, 4].length) (baseStart_7212111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7212111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7212111 prefixEnd_7212111 := by exact prefixLift 7212111
  have htrace : WordTrace (prefixWord ++ tailWord_7212111) baseStart_7212111 baseEnd_7212111 := by
    simpa [prefixWord, tailWord_7212111, baseEnd_7212111] using wordTrace_append hprefix tailTrace_7212111
  have hstable : (prefixWord ++ tailWord_7212111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7212111).length < 2 ^ (prefixWord ++ tailWord_7212111).sum := by decide
  have hdescent : baseEnd_7212111 < baseStart_7212111 := by decide
  rcases family_descends (prefixWord ++ tailWord_7212111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7212131 : List Nat := [1, 1, 1, 5, 1, 1, 1, 3, 3, 2, 4]
def baseStart_7212131 : Nat := 118140960795 + 7212131 * 2 ^ 59
def prefixEnd_7212131 : Nat := 4983230072969 + 3 ^ 40 * 7212131 * 2
def baseEnd_7212131 : Nat := 3703289746191627237994519

theorem tailTrace_7212131 : CollatzResearch.WordTrace tailWord_7212131 prefixEnd_7212131 3703289746191627237994519 := by
  unfold tailWord_7212131
  simp only [CollatzResearch.WordTrace]
  refine ⟨263048027834688595756564247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175365351889792397171042831 263048027834688595756564247)
  ·
    refine ⟨394572041752032893634846371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263048027834688595756564247 394572041752032893634846371)
    ·
      refine ⟨591858062628049340452269557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 394572041752032893634846371 591858062628049340452269557)
      ·
        refine ⟨55486693371379625667400271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 591858062628049340452269557 55486693371379625667400271)
        ·
          refine ⟨83230040057069438501100407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55486693371379625667400271 83230040057069438501100407)
          ·
            refine ⟨124845060085604157751650611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83230040057069438501100407 124845060085604157751650611)
            ·
              refine ⟨187267590128406236627475917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 124845060085604157751650611 187267590128406236627475917)
              ·
                refine ⟨70225346298152338735303469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 187267590128406236627475917 70225346298152338735303469)
                ·
                  refine ⟨26334504861807127025738801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 70225346298152338735303469 26334504861807127025738801)
                  ·
                    refine ⟨19750878646355345269304101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26334504861807127025738801 19750878646355345269304101)
                    ·
                      refine ⟨3703289746191627237994519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19750878646355345269304101 3703289746191627237994519)
                      ·
                        rfl

theorem cell23_7212131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 3, 3, 2, 4].length) (baseStart_7212131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7212131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7212131 prefixEnd_7212131 := by exact prefixLift 7212131
  have htrace : WordTrace (prefixWord ++ tailWord_7212131) baseStart_7212131 baseEnd_7212131 := by
    simpa [prefixWord, tailWord_7212131, baseEnd_7212131] using wordTrace_append hprefix tailTrace_7212131
  have hstable : (prefixWord ++ tailWord_7212131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7212131).length < 2 ^ (prefixWord ++ tailWord_7212131).sum := by decide
  have hdescent : baseEnd_7212131 < baseStart_7212131 := by decide
  rcases family_descends (prefixWord ++ tailWord_7212131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7212138 : List Nat := [3, 1, 3, 2, 2, 1, 1, 3, 1, 1, 5]
def baseStart_7212138 : Nat := 118140960795 + 7212138 * 2 ^ 59
def prefixEnd_7212138 : Nat := 4983230072969 + 3 ^ 40 * 7212138 * 2
def baseEnd_7212138 : Nat := 3703293340556208710606987

theorem tailTrace_7212138 : CollatzResearch.WordTrace tailWord_7212138 prefixEnd_7212138 3703293340556208710606987 := by
  unfold tailWord_7212138
  simp only [CollatzResearch.WordTrace]
  refine ⟨65762070786415808988017267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175365522097108823968046045 65762070786415808988017267)
  ·
    refine ⟨98643106179623713482025901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65762070786415808988017267 98643106179623713482025901)
    ·
      refine ⟨36991164817358892555759713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98643106179623713482025901 36991164817358892555759713)
      ·
        refine ⟨27743373613019169416819785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36991164817358892555759713 27743373613019169416819785)
        ·
          refine ⟨20807530209764377062614839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27743373613019169416819785 20807530209764377062614839)
          ·
            refine ⟨31211295314646565593922259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20807530209764377062614839 31211295314646565593922259)
            ·
              refine ⟨46816942971969848390883389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31211295314646565593922259 46816942971969848390883389)
              ·
                refine ⟨17556353614488693146581271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46816942971969848390883389 17556353614488693146581271)
                ·
                  refine ⟨26334530421733039719871907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17556353614488693146581271 26334530421733039719871907)
                  ·
                    refine ⟨39501795632599559579807861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26334530421733039719871907 39501795632599559579807861)
                    ·
                      refine ⟨3703293340556208710606987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39501795632599559579807861 3703293340556208710606987)
                      ·
                        rfl

theorem cell23_7212138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 1, 3, 1, 1, 5].length) (baseStart_7212138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7212138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7212138 prefixEnd_7212138 := by exact prefixLift 7212138
  have htrace : WordTrace (prefixWord ++ tailWord_7212138) baseStart_7212138 baseEnd_7212138 := by
    simpa [prefixWord, tailWord_7212138, baseEnd_7212138] using wordTrace_append hprefix tailTrace_7212138
  have hstable : (prefixWord ++ tailWord_7212138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7212138).length < 2 ^ (prefixWord ++ tailWord_7212138).sum := by decide
  have hdescent : baseEnd_7212138 < baseStart_7212138 := by decide
  rcases family_descends (prefixWord ++ tailWord_7212138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7212141 : List Nat := [1, 5, 1, 1, 2, 2, 11]
def baseStart_7212141 : Nat := 118140960795 + 7212141 * 2 ^ 59
def prefixEnd_7212141 : Nat := 4983230072969 + 3 ^ 40 * 7212141 * 2
def baseEnd_7212141 : Nat := 45719689888866323442833

theorem tailTrace_7212141 : CollatzResearch.WordTrace tailWord_7212141 prefixEnd_7212141 45719689888866323442833 := by
  unfold tailWord_7212141
  simp only [CollatzResearch.WordTrace]
  refine ⟨263048392564652367464428277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175365595043101578309618851 263048392564652367464428277)
  ·
    refine ⟨24660786802936159449790151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 263048392564652367464428277 24660786802936159449790151)
    ·
      refine ⟨36991180204404239174685227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24660786802936159449790151 36991180204404239174685227)
      ·
        refine ⟨55486770306606358762027841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36991180204404239174685227 55486770306606358762027841)
        ·
          refine ⟨41615077729954769071520881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55486770306606358762027841 41615077729954769071520881)
          ·
            refine ⟨31211308297466076803640661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41615077729954769071520881 31211308297466076803640661)
            ·
              refine ⟨45719689888866323442833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 31211308297466076803640661 45719689888866323442833)
              ·
                rfl

theorem cell23_7212141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 11].length) (baseStart_7212141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7212141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7212141 prefixEnd_7212141 := by exact prefixLift 7212141
  have htrace : WordTrace (prefixWord ++ tailWord_7212141) baseStart_7212141 baseEnd_7212141 := by
    simpa [prefixWord, tailWord_7212141, baseEnd_7212141] using wordTrace_append hprefix tailTrace_7212141
  have hstable : (prefixWord ++ tailWord_7212141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7212141).length < 2 ^ (prefixWord ++ tailWord_7212141).sum := by decide
  have hdescent : baseEnd_7212141 < baseStart_7212141 := by decide
  rcases family_descends (prefixWord ++ tailWord_7212141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7212152 : List Nat := [2, 1, 2, 1, 1, 1, 4, 6, 1, 2, 2]
def baseStart_7212152 : Nat := 118140960795 + 7212152 * 2 ^ 59
def prefixEnd_7212152 : Nat := 4983230072969 + 3 ^ 40 * 7212152 * 2
def baseEnd_7212152 : Nat := 3703300529285371655831923

theorem tailTrace_7212152 : CollatzResearch.WordTrace tailWord_7212152 prefixEnd_7212152 3703300529285371655831923 := by
  unfold tailWord_7212152
  simp only [CollatzResearch.WordTrace]
  refine ⟨131524396883806258171539355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175365862511741677562052473 131524396883806258171539355)
  ·
    refine ⟨197286595325709387257309033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131524396883806258171539355 197286595325709387257309033)
    ·
      refine ⟨147964946494282040442981775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 197286595325709387257309033 147964946494282040442981775)
      ·
        refine ⟨221947419741423060664472663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147964946494282040442981775 221947419741423060664472663)
        ·
          refine ⟨332921129612134590996708995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 221947419741423060664472663 332921129612134590996708995)
          ·
            refine ⟨499381694418201886495063493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 332921129612134590996708995 499381694418201886495063493)
            ·
              refine ⟨93634067703412853717824405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 499381694418201886495063493 93634067703412853717824405)
              ·
                refine ⟨4389096923597477518023019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 93634067703412853717824405 4389096923597477518023019)
                ·
                  refine ⟨6583645385396216277034529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4389096923597477518023019 6583645385396216277034529)
                  ·
                    refine ⟨4937734039047162207775897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6583645385396216277034529 4937734039047162207775897)
                    ·
                      refine ⟨3703300529285371655831923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4937734039047162207775897 3703300529285371655831923)
                      ·
                        rfl

theorem cell23_7212152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 6, 1, 2, 2].length) (baseStart_7212152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7212152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7212152 prefixEnd_7212152 := by exact prefixLift 7212152
  have htrace : WordTrace (prefixWord ++ tailWord_7212152) baseStart_7212152 baseEnd_7212152 := by
    simpa [prefixWord, tailWord_7212152, baseEnd_7212152] using wordTrace_append hprefix tailTrace_7212152
  have hstable : (prefixWord ++ tailWord_7212152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7212152).length < 2 ^ (prefixWord ++ tailWord_7212152).sum := by decide
  have hdescent : baseEnd_7212152 < baseStart_7212152 := by decide
  rcases family_descends (prefixWord ++ tailWord_7212152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7212181 : List Nat := [1, 3, 2, 1, 1, 1, 2, 3, 2, 2, 5]
def baseStart_7212181 : Nat := 118140960795 + 7212181 * 2 ^ 59
def prefixEnd_7212181 : Nat := 4983230072969 + 3 ^ 40 * 7212181 * 2
def baseEnd_7212181 : Nat := 3703315420224352042369289

theorem tailTrace_7212181 : CollatzResearch.WordTrace tailWord_7212181 prefixEnd_7212181 3703315420224352042369289 := by
  unfold tailWord_7212181
  simp only [CollatzResearch.WordTrace]
  refine ⟨263049851484507454295884397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175366567656338302863922931 263049851484507454295884397)
  ·
    refine ⟨98643694306690295360956649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 263049851484507454295884397 98643694306690295360956649)
    ·
      refine ⟨73982770730017721520717487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98643694306690295360956649 73982770730017721520717487)
      ·
        refine ⟨110974156095026582281076231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73982770730017721520717487 110974156095026582281076231)
        ·
          refine ⟨166461234142539873421614347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110974156095026582281076231 166461234142539873421614347)
          ·
            refine ⟨249691851213809810132421521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 166461234142539873421614347 249691851213809810132421521)
            ·
              refine ⟨187268888410357357599316141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 249691851213809810132421521 187268888410357357599316141)
              ·
                refine ⟨70225833153884009099743553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 187268888410357357599316141 70225833153884009099743553)
                ·
                  refine ⟨52669374865413006824807665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 70225833153884009099743553 52669374865413006824807665)
                  ·
                    refine ⟨39502031149059755118605749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 52669374865413006824807665 39502031149059755118605749)
                    ·
                      refine ⟨3703315420224352042369289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39502031149059755118605749 3703315420224352042369289)
                      ·
                        rfl

theorem cell23_7212181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 3, 2, 2, 5].length) (baseStart_7212181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7212181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7212181 prefixEnd_7212181 := by exact prefixLift 7212181
  have htrace : WordTrace (prefixWord ++ tailWord_7212181) baseStart_7212181 baseEnd_7212181 := by
    simpa [prefixWord, tailWord_7212181, baseEnd_7212181] using wordTrace_append hprefix tailTrace_7212181
  have hstable : (prefixWord ++ tailWord_7212181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7212181).length < 2 ^ (prefixWord ++ tailWord_7212181).sum := by decide
  have hdescent : baseEnd_7212181 < baseStart_7212181 := by decide
  rcases family_descends (prefixWord ++ tailWord_7212181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7212195 : List Nat := [1, 1, 1, 4, 1, 1, 1, 7, 1, 3, 2]
def baseStart_7212195 : Nat := 118140960795 + 7212195 * 2 ^ 59
def prefixEnd_7212195 : Nat := 4983230072969 + 3 ^ 40 * 7212195 * 2
def baseEnd_7212195 : Nat := 3703322608953514987594225

theorem tailTrace_7212195 : CollatzResearch.WordTrace tailWord_7212195 prefixEnd_7212195 3703322608953514987594225 := by
  unfold tailWord_7212195
  simp only [CollatzResearch.WordTrace]
  refine ⟨263050362106456734686894039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175366908070971156457929359 263050362106456734686894039)
  ·
    refine ⟨394575543159685102030341059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263050362106456734686894039 394575543159685102030341059)
    ·
      refine ⟨591863314739527653045511589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 394575543159685102030341059 591863314739527653045511589)
      ·
        refine ⟨110974371513661434946033423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 591863314739527653045511589 110974371513661434946033423)
        ·
          refine ⟨166461557270492152419050135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110974371513661434946033423 166461557270492152419050135)
          ·
            refine ⟨249692335905738228628575203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 166461557270492152419050135 249692335905738228628575203)
            ·
              refine ⟨374538503858607342942862805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 249692335905738228628575203 374538503858607342942862805)
              ·
                refine ⟨8778246184186109600223347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 374538503858607342942862805 8778246184186109600223347)
                ·
                  refine ⟨13167369276279164400335021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8778246184186109600223347 13167369276279164400335021)
                  ·
                    refine ⟨4937763478604686650125633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13167369276279164400335021 4937763478604686650125633)
                    ·
                      refine ⟨3703322608953514987594225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4937763478604686650125633 3703322608953514987594225)
                      ·
                        rfl

theorem cell23_7212195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 7, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 7, 1, 3, 2].length) (baseStart_7212195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7212195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7212195 prefixEnd_7212195 := by exact prefixLift 7212195
  have htrace : WordTrace (prefixWord ++ tailWord_7212195) baseStart_7212195 baseEnd_7212195 := by
    simpa [prefixWord, tailWord_7212195, baseEnd_7212195] using wordTrace_append hprefix tailTrace_7212195
  have hstable : (prefixWord ++ tailWord_7212195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7212195).length < 2 ^ (prefixWord ++ tailWord_7212195).sum := by decide
  have hdescent : baseEnd_7212195 < baseStart_7212195 := by decide
  rcases family_descends (prefixWord ++ tailWord_7212195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7212211 : List Nat := [1, 1, 1, 2, 3, 2, 2, 2, 1, 3, 5]
def baseStart_7212211 : Nat := 118140960795 + 7212211 * 2 ^ 59
def prefixEnd_7212211 : Nat := 4983230072969 + 3 ^ 40 * 7212211 * 2
def baseEnd_7212211 : Nat := 3703330824643986924994151

theorem tailTrace_7212211 : CollatzResearch.WordTrace tailWord_7212211 prefixEnd_7212211 3703330824643986924994151 := by
  unfold tailWord_7212211
  simp only [CollatzResearch.WordTrace]
  refine ⟨263050945674398769419476487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175367297116265846279650991 263050945674398769419476487)
  ·
    refine ⟨394576418511598154129214731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263050945674398769419476487 394576418511598154129214731)
    ·
      refine ⟨591864627767397231193822097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 394576418511598154129214731 591864627767397231193822097)
      ·
        refine ⟨443898470825547923395366573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 591864627767397231193822097 443898470825547923395366573)
        ·
          refine ⟨166461926559580471273262465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 443898470825547923395366573 166461926559580471273262465)
          ·
            refine ⟨124846444919685353454946849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 166461926559580471273262465 124846444919685353454946849)
            ·
              refine ⟨93634833689764015091210137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 124846444919685353454946849 93634833689764015091210137)
              ·
                refine ⟨70226125267323011318407603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 93634833689764015091210137 70226125267323011318407603)
                ·
                  refine ⟨105339187900984516977611405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70226125267323011318407603 105339187900984516977611405)
                  ·
                    refine ⟨39502195462869193866604277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 105339187900984516977611405 39502195462869193866604277)
                    ·
                      refine ⟨3703330824643986924994151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39502195462869193866604277 3703330824643986924994151)
                      ·
                        rfl

theorem cell23_7212211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 2, 1, 3, 5].length) (baseStart_7212211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7212211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7212211 prefixEnd_7212211 := by exact prefixLift 7212211
  have htrace : WordTrace (prefixWord ++ tailWord_7212211) baseStart_7212211 baseEnd_7212211 := by
    simpa [prefixWord, tailWord_7212211, baseEnd_7212211] using wordTrace_append hprefix tailTrace_7212211
  have hstable : (prefixWord ++ tailWord_7212211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7212211).length < 2 ^ (prefixWord ++ tailWord_7212211).sum := by decide
  have hdescent : baseEnd_7212211 < baseStart_7212211 := by decide
  rcases family_descends (prefixWord ++ tailWord_7212211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7212241 : List Nat := [1, 2, 2, 1, 2, 2, 1, 2, 1, 2, 7]
def baseStart_7212241 : Nat := 118140960795 + 7212241 * 2 ^ 59
def prefixEnd_7212241 : Nat := 4983230072969 + 3 ^ 40 * 7212241 * 2
def baseEnd_7212241 : Nat := 3703346229063621807619013

theorem tailTrace_7212241 : CollatzResearch.WordTrace tailWord_7212241 prefixEnd_7212241 3703346229063621807619013 := by
  unfold tailWord_7212241
  simp only [CollatzResearch.WordTrace]
  refine ⟨263052039864290084543068577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175368026576193389695379051 263052039864290084543068577)
  ·
    refine ⟨197289029898217563407301433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 263052039864290084543068577 197289029898217563407301433)
    ·
      refine ⟨147966772423663172555476075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 197289029898217563407301433 147966772423663172555476075)
      ·
        refine ⟨221950158635494758833214113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147966772423663172555476075 221950158635494758833214113)
        ·
          refine ⟨166462618976621069124910585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 221950158635494758833214113 166462618976621069124910585)
          ·
            refine ⟨124846964232465801843682939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 166462618976621069124910585 124846964232465801843682939)
            ·
              refine ⟨187270446348698702765524409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 124846964232465801843682939 187270446348698702765524409)
              ·
                refine ⟨140452834761524027074143307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 187270446348698702765524409 140452834761524027074143307)
                ·
                  refine ⟨210679252142286040611214961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 140452834761524027074143307 210679252142286040611214961)
                  ·
                    refine ⟨158009439106714530458411221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 210679252142286040611214961 158009439106714530458411221)
                    ·
                      refine ⟨3703346229063621807619013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 158009439106714530458411221 3703346229063621807619013)
                      ·
                        rfl

theorem cell23_7212241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 2, 1, 2, 7].length) (baseStart_7212241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7212241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7212241 prefixEnd_7212241 := by exact prefixLift 7212241
  have htrace : WordTrace (prefixWord ++ tailWord_7212241) baseStart_7212241 baseEnd_7212241 := by
    simpa [prefixWord, tailWord_7212241, baseEnd_7212241] using wordTrace_append hprefix tailTrace_7212241
  have hstable : (prefixWord ++ tailWord_7212241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7212241).length < 2 ^ (prefixWord ++ tailWord_7212241).sum := by decide
  have hdescent : baseEnd_7212241 < baseStart_7212241 := by decide
  rcases family_descends (prefixWord ++ tailWord_7212241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7212242 : List Nat := [3, 2, 2, 2, 1, 1, 2, 2, 4, 2, 2]
def baseStart_7212242 : Nat := 118140960795 + 7212242 * 2 ^ 59
def prefixEnd_7212242 : Nat := 4983230072969 + 3 ^ 40 * 7212242 * 2
def baseEnd_7212242 : Nat := 3703346742544276303706509

theorem tailTrace_7212242 : CollatzResearch.WordTrace tailWord_7212242 prefixEnd_7212242 3703346742544276303706509 := by
  unfold tailWord_7212242
  simp only [CollatzResearch.WordTrace]
  refine ⟨65763019084321615428463745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175368050891524307809236653 65763019084321615428463745)
  ·
    refine ⟨49322264313241211571347809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65763019084321615428463745 49322264313241211571347809)
    ·
      refine ⟨36991698234930908678510857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49322264313241211571347809 36991698234930908678510857)
      ·
        refine ⟨27743773676198181508883143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36991698234930908678510857 27743773676198181508883143)
        ·
          refine ⟨41615660514297272263324715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27743773676198181508883143 41615660514297272263324715)
          ·
            refine ⟨62423490771445908394987073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41615660514297272263324715 62423490771445908394987073)
            ·
              refine ⟨46817618078584431296240305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62423490771445908394987073 46817618078584431296240305)
              ·
                refine ⟨35113213558938323472180229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46817618078584431296240305 35113213558938323472180229)
                ·
                  refine ⟨6583727542300935651033793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35113213558938323472180229 6583727542300935651033793)
                  ·
                    refine ⟨4937795656725701738275345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6583727542300935651033793 4937795656725701738275345)
                    ·
                      refine ⟨3703346742544276303706509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4937795656725701738275345 3703346742544276303706509)
                      ·
                        rfl

theorem cell23_7212242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 2, 2, 4, 2, 2].length) (baseStart_7212242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7212242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7212242 prefixEnd_7212242 := by exact prefixLift 7212242
  have htrace : WordTrace (prefixWord ++ tailWord_7212242) baseStart_7212242 baseEnd_7212242 := by
    simpa [prefixWord, tailWord_7212242, baseEnd_7212242] using wordTrace_append hprefix tailTrace_7212242
  have hstable : (prefixWord ++ tailWord_7212242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7212242).length < 2 ^ (prefixWord ++ tailWord_7212242).sum := by decide
  have hdescent : baseEnd_7212242 < baseStart_7212242 := by decide
  rcases family_descends (prefixWord ++ tailWord_7212242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7212246 : List Nat := [5, 2, 1, 2, 2, 1, 1, 3, 1, 3, 2]
def baseStart_7212246 : Nat := 118140960795 + 7212246 * 2 ^ 59
def prefixEnd_7212246 : Nat := 4983230072969 + 3 ^ 40 * 7212246 * 2
def baseEnd_7212246 : Nat := 3703348796466894288056491

theorem tailTrace_7212246 : CollatzResearch.WordTrace tailWord_7212246 prefixEnd_7212246 3703348796466894288056491 := by
  unfold tailWord_7212246
  simp only [CollatzResearch.WordTrace]
  refine ⟨16440763889329498149812537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 175368148152847980264667061 16440763889329498149812537)
  ·
    refine ⟨12330572916997123612359403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16440763889329498149812537 12330572916997123612359403)
    ·
      refine ⟨18495859375495685418539105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12330572916997123612359403 18495859375495685418539105)
      ·
        refine ⟨13871894531621764063904329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18495859375495685418539105 13871894531621764063904329)
        ·
          refine ⟨10403920898716323047928247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13871894531621764063904329 10403920898716323047928247)
          ·
            refine ⟨15605881348074484571892371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10403920898716323047928247 15605881348074484571892371)
            ·
              refine ⟨23408822022111726857838557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15605881348074484571892371 23408822022111726857838557)
              ·
                refine ⟨8778308258291897571689459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23408822022111726857838557 8778308258291897571689459)
                ·
                  refine ⟨13167462387437846357534189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8778308258291897571689459 13167462387437846357534189)
                  ·
                    refine ⟨4937798395289192384075321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13167462387437846357534189 4937798395289192384075321)
                    ·
                      refine ⟨3703348796466894288056491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4937798395289192384075321 3703348796466894288056491)
                      ·
                        rfl

theorem cell23_7212246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 1, 3, 1, 3, 2].length) (baseStart_7212246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7212246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7212246 prefixEnd_7212246 := by exact prefixLift 7212246
  have htrace : WordTrace (prefixWord ++ tailWord_7212246) baseStart_7212246 baseEnd_7212246 := by
    simpa [prefixWord, tailWord_7212246, baseEnd_7212246] using wordTrace_append hprefix tailTrace_7212246
  have hstable : (prefixWord ++ tailWord_7212246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7212246).length < 2 ^ (prefixWord ++ tailWord_7212246).sum := by decide
  have hdescent : baseEnd_7212246 < baseStart_7212246 := by decide
  rcases family_descends (prefixWord ++ tailWord_7212246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7212349 : List Nat := [1, 4, 1, 5, 1, 1, 2, 1, 2, 1, 4]
def baseStart_7212349 : Nat := 118140960795 + 7212349 * 2 ^ 59
def prefixEnd_7212349 : Nat := 4983230072969 + 3 ^ 40 * 7212349 * 2
def baseEnd_7212349 : Nat := 3703401684974307385068517

theorem tailTrace_7212349 : CollatzResearch.WordTrace tailWord_7212349 prefixEnd_7212349 3703401684974307385068517 := by
  unfold tailWord_7212349
  simp only [CollatzResearch.WordTrace]
  refine ⟨263055978947898818988000101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175370652631932545992000067 263055978947898818988000101)
  ·
    refine ⟨49322996052731028560250019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 263055978947898818988000101 49322996052731028560250019)
    ·
      refine ⟨73984494079096542840375029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49322996052731028560250019 73984494079096542840375029)
      ·
        refine ⟨6936046319915300891285159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 73984494079096542840375029 6936046319915300891285159)
        ·
          refine ⟨10404069479872951336927739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6936046319915300891285159 10404069479872951336927739)
          ·
            refine ⟨15606104219809427005391609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10404069479872951336927739 15606104219809427005391609)
            ·
              refine ⟨11704578164857070254043707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15606104219809427005391609 11704578164857070254043707)
              ·
                refine ⟨17556867247285605381065561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11704578164857070254043707 17556867247285605381065561)
                ·
                  refine ⟨13167650435464204035799171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17556867247285605381065561 13167650435464204035799171)
                  ·
                    refine ⟨19751475653196306053698757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13167650435464204035799171 19751475653196306053698757)
                    ·
                      refine ⟨3703401684974307385068517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19751475653196306053698757 3703401684974307385068517)
                      ·
                        rfl

theorem cell23_7212349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 2, 1, 2, 1, 4].length) (baseStart_7212349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7212349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7212349 prefixEnd_7212349 := by exact prefixLift 7212349
  have htrace : WordTrace (prefixWord ++ tailWord_7212349) baseStart_7212349 baseEnd_7212349 := by
    simpa [prefixWord, tailWord_7212349, baseEnd_7212349] using wordTrace_append hprefix tailTrace_7212349
  have hstable : (prefixWord ++ tailWord_7212349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7212349).length < 2 ^ (prefixWord ++ tailWord_7212349).sum := by decide
  have hdescent : baseEnd_7212349 < baseStart_7212349 := by decide
  rcases family_descends (prefixWord ++ tailWord_7212349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7212419 : List Nat := [1, 1, 1, 3, 5, 3, 2, 1, 1, 5]
def baseStart_7212419 : Nat := 118140960795 + 7212419 * 2 ^ 59
def prefixEnd_7212419 : Nat := 4983230072969 + 3 ^ 40 * 7212419 * 2
def baseEnd_7212419 : Nat := 1234479209540040703731065

theorem tailTrace_7212419 : CollatzResearch.WordTrace tailWord_7212419 prefixEnd_7212419 1234479209540040703731065 := by
  unfold tailWord_7212419
  simp only [CollatzResearch.WordTrace]
  refine ⟨263058532057645220943048311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175372354705096813962032207 263058532057645220943048311)
  ·
    refine ⟨394587798086467831414572467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263058532057645220943048311 394587798086467831414572467)
    ·
      refine ⟨591881697129701747121858701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 394587798086467831414572467 591881697129701747121858701)
      ·
        refine ⟨221955636423638155170697013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 591881697129701747121858701 221955636423638155170697013)
        ·
          refine ⟨20808340914716077047252845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 221955636423638155170697013 20808340914716077047252845)
          ·
            refine ⟨7803127843018528892719817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20808340914716077047252845 7803127843018528892719817)
            ·
              refine ⟨5852345882263896669539863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7803127843018528892719817 5852345882263896669539863)
              ·
                refine ⟨8778518823395845004309795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5852345882263896669539863 8778518823395845004309795)
                ·
                  refine ⟨13167778235093767506464693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8778518823395845004309795 13167778235093767506464693)
                  ·
                    refine ⟨1234479209540040703731065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13167778235093767506464693 1234479209540040703731065)
                    ·
                      rfl

theorem cell23_7212419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 3, 2, 1, 1, 5].length) (baseStart_7212419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7212419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7212419 prefixEnd_7212419 := by exact prefixLift 7212419
  have htrace : WordTrace (prefixWord ++ tailWord_7212419) baseStart_7212419 baseEnd_7212419 := by
    simpa [prefixWord, tailWord_7212419, baseEnd_7212419] using wordTrace_append hprefix tailTrace_7212419
  have hstable : (prefixWord ++ tailWord_7212419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7212419).length < 2 ^ (prefixWord ++ tailWord_7212419).sum := by decide
  have hdescent : baseEnd_7212419 < baseStart_7212419 := by decide
  rcases family_descends (prefixWord ++ tailWord_7212419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7212428 : List Nat := [2, 2, 1, 2, 1, 3, 12]
def baseStart_7212428 : Nat := 118140960795 + 7212428 * 2 ^ 59
def prefixEnd_7212428 : Nat := 4983230072969 + 3 ^ 40 * 7212428 * 2
def baseEnd_7212428 : Nat := 45721509258592747851613

theorem tailTrace_7212428 : CollatzResearch.WordTrace tailWord_7212428 prefixEnd_7212428 45721509258592747851613 := by
  unfold tailWord_7212428
  simp only [CollatzResearch.WordTrace]
  refine ⟨131529430157306307740062969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175372573543075076986750625 131529430157306307740062969)
  ·
    refine ⟨98647072617979730805047227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131529430157306307740062969 98647072617979730805047227)
    ·
      refine ⟨147970608926969596207570841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98647072617979730805047227 147970608926969596207570841)
      ·
        refine ⟨110977956695227197155678131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147970608926969596207570841 110977956695227197155678131)
        ·
          refine ⟨166466935042840795733517197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110977956695227197155678131 166466935042840795733517197)
          ·
            refine ⟨62425100641065298400068949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 166466935042840795733517197 62425100641065298400068949)
            ·
              refine ⟨45721509258592747851613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 62425100641065298400068949 45721509258592747851613)
              ·
                rfl

theorem cell23_7212428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 12].length) (baseStart_7212428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7212428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7212428 prefixEnd_7212428 := by exact prefixLift 7212428
  have htrace : WordTrace (prefixWord ++ tailWord_7212428) baseStart_7212428 baseEnd_7212428 := by
    simpa [prefixWord, tailWord_7212428, baseEnd_7212428] using wordTrace_append hprefix tailTrace_7212428
  have hstable : (prefixWord ++ tailWord_7212428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7212428).length < 2 ^ (prefixWord ++ tailWord_7212428).sum := by decide
  have hdescent : baseEnd_7212428 < baseStart_7212428 := by decide
  rcases family_descends (prefixWord ++ tailWord_7212428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7212456 : List Nat := [2, 1, 6, 1, 2, 1, 2, 2, 1, 1, 4]
def baseStart_7212456 : Nat := 118140960795 + 7212456 * 2 ^ 59
def prefixEnd_7212456 : Nat := 4983230072969 + 3 ^ 40 * 7212456 * 2
def baseEnd_7212456 : Nat := 3703456627404338466430525

theorem tailTrace_7212456 : CollatzResearch.WordTrace tailWord_7212456 prefixEnd_7212456 3703456627404338466430525 := by
  unfold tailWord_7212456
  simp only [CollatzResearch.WordTrace]
  refine ⟨131529940779255588131072611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175373254372340784174763481 131529940779255588131072611)
  ·
    refine ⟨197294911168883382196608917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131529940779255588131072611 197294911168883382196608917)
    ·
      refine ⟨9248198961041408540466043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 197294911168883382196608917 9248198961041408540466043)
      ·
        refine ⟨13872298441562112810699065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9248198961041408540466043 13872298441562112810699065)
        ·
          refine ⟨10404223831171584608024299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13872298441562112810699065 10404223831171584608024299)
          ·
            refine ⟨15606335746757376912036449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10404223831171584608024299 15606335746757376912036449)
            ·
              refine ⟨11704751810068032684027337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15606335746757376912036449 11704751810068032684027337)
              ·
                refine ⟨8778563857551024513020503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11704751810068032684027337 8778563857551024513020503)
                ·
                  refine ⟨13167845786326536769530755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8778563857551024513020503 13167845786326536769530755)
                  ·
                    refine ⟨19751768679489805154296133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13167845786326536769530755 19751768679489805154296133)
                    ·
                      refine ⟨3703456627404338466430525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19751768679489805154296133 3703456627404338466430525)
                      ·
                        rfl

theorem cell23_7212456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 2, 2, 1, 1, 4].length) (baseStart_7212456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7212456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7212456 prefixEnd_7212456 := by exact prefixLift 7212456
  have htrace : WordTrace (prefixWord ++ tailWord_7212456) baseStart_7212456 baseEnd_7212456 := by
    simpa [prefixWord, tailWord_7212456, baseEnd_7212456] using wordTrace_append hprefix tailTrace_7212456
  have hstable : (prefixWord ++ tailWord_7212456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7212456).length < 2 ^ (prefixWord ++ tailWord_7212456).sum := by decide
  have hdescent : baseEnd_7212456 < baseStart_7212456 := by decide
  rcases family_descends (prefixWord ++ tailWord_7212456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7212472 : List Nat := [2, 1, 2, 1, 2, 2, 3, 2, 4, 1, 3]
def baseStart_7212472 : Nat := 118140960795 + 7212472 * 2 ^ 59
def prefixEnd_7212472 : Nat := 4983230072969 + 3 ^ 40 * 7212472 * 2
def baseEnd_7212472 : Nat := 3703464843094810403830451

theorem tailTrace_7212472 : CollatzResearch.WordTrace tailWord_7212472 prefixEnd_7212472 3703464843094810403830451 := by
  unfold tailWord_7212472
  simp only [CollatzResearch.WordTrace]
  refine ⟨131530232563226605497363835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175373643417635473996485113 131530232563226605497363835)
  ·
    refine ⟨197295348844839908246045753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131530232563226605497363835 197295348844839908246045753)
    ·
      refine ⟨147971511633629931184534315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 197295348844839908246045753 147971511633629931184534315)
      ·
        refine ⟨221957267450444896776801473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147971511633629931184534315 221957267450444896776801473)
        ·
          refine ⟨166467950587833672582601105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 221957267450444896776801473 166467950587833672582601105)
          ·
            refine ⟨124850962940875254436950829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 166467950587833672582601105 124850962940875254436950829)
            ·
              refine ⟨46819111102828220413856561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 124850962940875254436950829 46819111102828220413856561)
              ·
                refine ⟨35114333327121165310392421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46819111102828220413856561 35114333327121165310392421)
                ·
                  refine ⟨6583937498835218495698579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35114333327121165310392421 6583937498835218495698579)
                  ·
                    refine ⟨9875906248252827743547869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6583937498835218495698579 9875906248252827743547869)
                    ·
                      refine ⟨3703464843094810403830451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9875906248252827743547869 3703464843094810403830451)
                      ·
                        rfl

theorem cell23_7212472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 3, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 3, 2, 4, 1, 3].length) (baseStart_7212472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7212472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7212472 prefixEnd_7212472 := by exact prefixLift 7212472
  have htrace : WordTrace (prefixWord ++ tailWord_7212472) baseStart_7212472 baseEnd_7212472 := by
    simpa [prefixWord, tailWord_7212472, baseEnd_7212472] using wordTrace_append hprefix tailTrace_7212472
  have hstable : (prefixWord ++ tailWord_7212472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7212472).length < 2 ^ (prefixWord ++ tailWord_7212472).sum := by decide
  have hdescent : baseEnd_7212472 < baseStart_7212472 := by decide
  rcases family_descends (prefixWord ++ tailWord_7212472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7212506 : List Nat := [3, 1, 1, 2, 3, 2, 4, 1, 2, 1, 3]
def baseStart_7212506 : Nat := 118140960795 + 7212506 * 2 ^ 59
def prefixEnd_7212506 : Nat := 4983230072969 + 3 ^ 40 * 7212506 * 2
def baseEnd_7212506 : Nat := 3703482301437063270805295

theorem tailTrace_7212506 : CollatzResearch.WordTrace tailWord_7212506 prefixEnd_7212506 3703482301437063270805295 := by
  unfold tailWord_7212506
  simp only [CollatzResearch.WordTrace]
  refine ⟨65765426302082508700366343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175374470138886689867643581 65765426302082508700366343)
  ·
    refine ⟨98648139453123763050549515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65765426302082508700366343 98648139453123763050549515)
    ·
      refine ⟨147972209179685644575824273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98648139453123763050549515 147972209179685644575824273)
      ·
        refine ⟨110979156884764233431868205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147972209179685644575824273 110979156884764233431868205)
        ·
          refine ⟨41617183831786587536950577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 110979156884764233431868205 41617183831786587536950577)
          ·
            refine ⟨31212887873839940652712933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41617183831786587536950577 31212887873839940652712933)
            ·
              refine ⟨5852416476344988872383675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31212887873839940652712933 5852416476344988872383675)
              ·
                refine ⟨8778624714517483308575513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5852416476344988872383675 8778624714517483308575513)
                ·
                  refine ⟨6583968535888112481431635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8778624714517483308575513 6583968535888112481431635)
                  ·
                    refine ⟨9875952803832168722147453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6583968535888112481431635 9875952803832168722147453)
                    ·
                      refine ⟨3703482301437063270805295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9875952803832168722147453 3703482301437063270805295)
                      ·
                        rfl

theorem cell23_7212506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 4, 1, 2, 1, 3].length) (baseStart_7212506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7212506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7212506 prefixEnd_7212506 := by exact prefixLift 7212506
  have htrace : WordTrace (prefixWord ++ tailWord_7212506) baseStart_7212506 baseEnd_7212506 := by
    simpa [prefixWord, tailWord_7212506, baseEnd_7212506] using wordTrace_append hprefix tailTrace_7212506
  have hstable : (prefixWord ++ tailWord_7212506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7212506).length < 2 ^ (prefixWord ++ tailWord_7212506).sum := by decide
  have hdescent : baseEnd_7212506 < baseStart_7212506 := by decide
  rcases family_descends (prefixWord ++ tailWord_7212506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7212529 : List Nat := [1, 2, 2, 2, 3, 3, 1, 2, 1, 4, 2]
def baseStart_7212529 : Nat := 118140960795 + 7212529 * 2 ^ 59
def prefixEnd_7212529 : Nat := 4983230072969 + 3 ^ 40 * 7212529 * 2
def baseEnd_7212529 : Nat := 3703494111492116680817689

theorem tailTrace_7212529 : CollatzResearch.WordTrace tailWord_7212529 prefixEnd_7212529 3703494111492116680817689 := by
  unfold tailWord_7212529
  simp only [CollatzResearch.WordTrace]
  refine ⟨263062544087246709729552641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175375029391497806486368427 263062544087246709729552641)
  ·
    refine ⟨197296908065435032297164481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 263062544087246709729552641 197296908065435032297164481)
    ·
      refine ⟨147972681049076274222873361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 197296908065435032297164481 147972681049076274222873361)
      ·
        refine ⟨110979510786807205667155021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147972681049076274222873361 110979510786807205667155021)
        ·
          refine ⟨41617316545052702125183133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 110979510786807205667155021 41617316545052702125183133)
          ·
            refine ⟨15606493704394763296943675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41617316545052702125183133 15606493704394763296943675)
            ·
              refine ⟨23409740556592144945415513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15606493704394763296943675 23409740556592144945415513)
              ·
                refine ⟨17557305417444108709061635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23409740556592144945415513 17557305417444108709061635)
                ·
                  refine ⟨26335958126166163063592453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17557305417444108709061635 26335958126166163063592453)
                  ·
                    refine ⟨4937992148656155574423585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26335958126166163063592453 4937992148656155574423585)
                    ·
                      refine ⟨3703494111492116680817689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4937992148656155574423585 3703494111492116680817689)
                      ·
                        rfl

theorem cell23_7212529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 1, 2, 1, 4, 2].length) (baseStart_7212529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7212529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7212529 prefixEnd_7212529 := by exact prefixLift 7212529
  have htrace : WordTrace (prefixWord ++ tailWord_7212529) baseStart_7212529 baseEnd_7212529 := by
    simpa [prefixWord, tailWord_7212529, baseEnd_7212529] using wordTrace_append hprefix tailTrace_7212529
  have hstable : (prefixWord ++ tailWord_7212529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7212529).length < 2 ^ (prefixWord ++ tailWord_7212529).sum := by decide
  have hdescent : baseEnd_7212529 < baseStart_7212529 := by decide
  rcases family_descends (prefixWord ++ tailWord_7212529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7212575 : List Nat := [1, 1, 2, 4, 1, 1, 2, 2, 1, 1, 7]
def baseStart_7212575 : Nat := 118140960795 + 7212575 * 2 ^ 59
def prefixEnd_7212575 : Nat := 4983230072969 + 3 ^ 40 * 7212575 * 2
def baseEnd_7212575 : Nat := 3703517731602223500842477

theorem tailTrace_7212575 : CollatzResearch.WordTrace tailWord_7212575 prefixEnd_7212575 3703517731602223500842477 := by
  unfold tailWord_7212575
  simp only [CollatzResearch.WordTrace]
  refine ⟨263064221845080059585727179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175376147896720039723818119 263064221845080059585727179)
  ·
    refine ⟨394596332767620089378590769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263064221845080059585727179 394596332767620089378590769)
    ·
      refine ⟨295947249575715067033943077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 394596332767620089378590769 295947249575715067033943077)
      ·
        refine ⟨55490109295446575068864327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 295947249575715067033943077 55490109295446575068864327)
        ·
          refine ⟨83235163943169862603296491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55490109295446575068864327 83235163943169862603296491)
          ·
            refine ⟨124852745914754793904944737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83235163943169862603296491 124852745914754793904944737)
            ·
              refine ⟨93639559436066095428708553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 124852745914754793904944737 93639559436066095428708553)
              ·
                refine ⟨70229669577049571571531415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 93639559436066095428708553 70229669577049571571531415)
                ·
                  refine ⟨105344504365574357357297123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70229669577049571571531415 105344504365574357357297123)
                  ·
                    refine ⟨158016756548361536035945685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 105344504365574357357297123 158016756548361536035945685)
                    ·
                      refine ⟨3703517731602223500842477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 158016756548361536035945685 3703517731602223500842477)
                      ·
                        rfl

theorem cell23_7212575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 2, 1, 1, 7].length) (baseStart_7212575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7212575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7212575 prefixEnd_7212575 := by exact prefixLift 7212575
  have htrace : WordTrace (prefixWord ++ tailWord_7212575) baseStart_7212575 baseEnd_7212575 := by
    simpa [prefixWord, tailWord_7212575, baseEnd_7212575] using wordTrace_append hprefix tailTrace_7212575
  have hstable : (prefixWord ++ tailWord_7212575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7212575).length < 2 ^ (prefixWord ++ tailWord_7212575).sum := by decide
  have hdescent : baseEnd_7212575 < baseStart_7212575 := by decide
  rcases family_descends (prefixWord ++ tailWord_7212575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7212602 : List Nat := [3, 1, 1, 1, 3, 2, 2, 1, 4, 1, 4]
def baseStart_7212602 : Nat := 118140960795 + 7212602 * 2 ^ 59
def prefixEnd_7212602 : Nat := 4983230072969 + 3 ^ 40 * 7212602 * 2
def baseEnd_7212602 : Nat := 3703531595579894895204853

theorem tailTrace_7212602 : CollatzResearch.WordTrace tailWord_7212602 prefixEnd_7212602 3703531595579894895204853 := by
  unfold tailWord_7212602
  simp only [CollatzResearch.WordTrace]
  refine ⟨65766301653995560799240015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175376804410654828797973373 65766301653995560799240015)
  ·
    refine ⟨98649452480993341198860023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65766301653995560799240015 98649452480993341198860023)
    ·
      refine ⟨147974178721490011798290035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98649452480993341198860023 147974178721490011798290035)
      ·
        refine ⟨221961268082235017697435053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147974178721490011798290035 221961268082235017697435053)
        ·
          refine ⟨83235475530838131636538145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 221961268082235017697435053 83235475530838131636538145)
          ·
            refine ⟨62426606648128598727403609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83235475530838131636538145 62426606648128598727403609)
            ·
              refine ⟨46819954986096449045552707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62426606648128598727403609 46819954986096449045552707)
              ·
                refine ⟨70229932479144673568329061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46819954986096449045552707 70229932479144673568329061)
                ·
                  refine ⟨13168112339839626294061699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 70229932479144673568329061 13168112339839626294061699)
                  ·
                    refine ⟨19752168509759439441092549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13168112339839626294061699 19752168509759439441092549)
                    ·
                      refine ⟨3703531595579894895204853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19752168509759439441092549 3703531595579894895204853)
                      ·
                        rfl

theorem cell23_7212602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 2, 1, 4, 1, 4].length) (baseStart_7212602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7212602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7212602 prefixEnd_7212602 := by exact prefixLift 7212602
  have htrace : WordTrace (prefixWord ++ tailWord_7212602) baseStart_7212602 baseEnd_7212602 := by
    simpa [prefixWord, tailWord_7212602, baseEnd_7212602] using wordTrace_append hprefix tailTrace_7212602
  have hstable : (prefixWord ++ tailWord_7212602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7212602).length < 2 ^ (prefixWord ++ tailWord_7212602).sum := by decide
  have hdescent : baseEnd_7212602 < baseStart_7212602 := by decide
  rcases family_descends (prefixWord ++ tailWord_7212602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7212672 : List Nat := [2, 1, 1, 2, 1, 4, 2, 2, 3, 5]
def baseStart_7212672 : Nat := 118140960795 + 7212672 * 2 ^ 59
def prefixEnd_7212672 : Nat := 4983230072969 + 3 ^ 40 * 7212672 * 2
def baseEnd_7212672 : Nat := 1234522513075236540443177

theorem tailTrace_7212672 : CollatzResearch.WordTrace tailWord_7212672 prefixEnd_7212672 1234522513075236540443177 := by
  unfold tailWord_7212672
  simp only [CollatzResearch.WordTrace]
  refine ⟨131533879862864322576004135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175378506483819096768005513 131533879862864322576004135)
  ·
    refine ⟨197300819794296483864006203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131533879862864322576004135 197300819794296483864006203)
    ·
      refine ⟨295951229691444725796009305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197300819794296483864006203 295951229691444725796009305)
      ·
        refine ⟨221963422268583544347006979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 295951229691444725796009305 221963422268583544347006979)
        ·
          refine ⟨332945133402875316520510469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 221963422268583544347006979 332945133402875316520510469)
          ·
            refine ⟨62427212513039121847595713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 332945133402875316520510469 62427212513039121847595713)
            ·
              refine ⟨46820409384779341385696785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62427212513039121847595713 46820409384779341385696785)
              ·
                refine ⟨35115307038584506039272589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46820409384779341385696785 35115307038584506039272589)
                ·
                  refine ⟨13168240139469189764727221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35115307038584506039272589 13168240139469189764727221)
                  ·
                    refine ⟨1234522513075236540443177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13168240139469189764727221 1234522513075236540443177)
                    ·
                      rfl

theorem cell23_7212672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 2, 2, 3, 5].length) (baseStart_7212672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7212672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7212672 prefixEnd_7212672 := by exact prefixLift 7212672
  have htrace : WordTrace (prefixWord ++ tailWord_7212672) baseStart_7212672 baseEnd_7212672 := by
    simpa [prefixWord, tailWord_7212672, baseEnd_7212672] using wordTrace_append hprefix tailTrace_7212672
  have hstable : (prefixWord ++ tailWord_7212672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7212672).length < 2 ^ (prefixWord ++ tailWord_7212672).sum := by decide
  have hdescent : baseEnd_7212672 < baseStart_7212672 := by decide
  rcases family_descends (prefixWord ++ tailWord_7212672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7212696 : List Nat := [2, 1, 2, 4, 1, 2, 1, 3, 2, 3, 2]
def baseStart_7212696 : Nat := 118140960795 + 7212696 * 2 ^ 59
def prefixEnd_7212696 : Nat := 4983230072969 + 3 ^ 40 * 7212696 * 2
def baseEnd_7212696 : Nat := 3703579862761417527429421

theorem tailTrace_7212696 : CollatzResearch.WordTrace tailWord_7212696 prefixEnd_7212696 3703579862761417527429421 := by
  unfold tailWord_7212696
  simp only [CollatzResearch.WordTrace]
  refine ⟨131534317538820848625440971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175379090051761131500587961 131534317538820848625440971)
  ·
    refine ⟨197301476308231272938161457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131534317538820848625440971 197301476308231272938161457)
    ·
      refine ⟨147976107231173454703621093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 197301476308231272938161457 147976107231173454703621093)
      ·
        refine ⟨27745520105845022756928955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 147976107231173454703621093 27745520105845022756928955)
        ·
          refine ⟨41618280158767534135393433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27745520105845022756928955 41618280158767534135393433)
          ·
            refine ⟨31213710119075650601545075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41618280158767534135393433 31213710119075650601545075)
            ·
              refine ⟨46820565178613475902317613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31213710119075650601545075 46820565178613475902317613)
              ·
                refine ⟨17557711941980053463369105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46820565178613475902317613 17557711941980053463369105)
                ·
                  refine ⟨13168283956485040097526829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17557711941980053463369105 13168283956485040097526829)
                  ·
                    refine ⟨4938106483681890036572561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13168283956485040097526829 4938106483681890036572561)
                    ·
                      refine ⟨3703579862761417527429421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4938106483681890036572561 3703579862761417527429421)
                      ·
                        rfl

theorem cell23_7212696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 1, 3, 2, 3, 2].length) (baseStart_7212696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7212696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7212696 prefixEnd_7212696 := by exact prefixLift 7212696
  have htrace : WordTrace (prefixWord ++ tailWord_7212696) baseStart_7212696 baseEnd_7212696 := by
    simpa [prefixWord, tailWord_7212696, baseEnd_7212696] using wordTrace_append hprefix tailTrace_7212696
  have hstable : (prefixWord ++ tailWord_7212696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7212696).length < 2 ^ (prefixWord ++ tailWord_7212696).sum := by decide
  have hdescent : baseEnd_7212696 < baseStart_7212696 := by decide
  rcases family_descends (prefixWord ++ tailWord_7212696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7212709 : List Nat := [1, 3, 1, 2, 1, 2, 2, 5, 1, 1, 4]
def baseStart_7212709 : Nat := 118140960795 + 7212709 * 2 ^ 59
def prefixEnd_7212709 : Nat := 4983230072969 + 3 ^ 40 * 7212709 * 2
def baseEnd_7212709 : Nat := 3703586538009925976566861

theorem tailTrace_7212709 : CollatzResearch.WordTrace tailWord_7212709 prefixEnd_7212709 3703586538009925976566861 := by
  unfold tailWord_7212709
  simp only [CollatzResearch.WordTrace]
  refine ⟨263069109226594600471105181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175379406151063066980736787 263069109226594600471105181)
  ·
    refine ⟨98650915959972975176664443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 263069109226594600471105181 98650915959972975176664443)
    ·
      refine ⟨147976373939959462764996665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98650915959972975176664443 147976373939959462764996665)
      ·
        refine ⟨110982280454969597073747499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147976373939959462764996665 110982280454969597073747499)
        ·
          refine ⟨166473420682454395610621249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110982280454969597073747499 166473420682454395610621249)
          ·
            refine ⟨124855065511840796707965937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 166473420682454395610621249 124855065511840796707965937)
            ·
              refine ⟨93641299133880597530974453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 124855065511840796707965937 93641299133880597530974453)
              ·
                refine ⟨8778871793801306018528855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 93641299133880597530974453 8778871793801306018528855)
                ·
                  refine ⟨13168307690701959027793283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8778871793801306018528855 13168307690701959027793283)
                  ·
                    refine ⟨19752461536052938541689925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13168307690701959027793283 19752461536052938541689925)
                    ·
                      refine ⟨3703586538009925976566861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19752461536052938541689925 3703586538009925976566861)
                      ·
                        rfl

theorem cell23_7212709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 5, 1, 1, 4].length) (baseStart_7212709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7212709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7212709 prefixEnd_7212709 := by exact prefixLift 7212709
  have htrace : WordTrace (prefixWord ++ tailWord_7212709) baseStart_7212709 baseEnd_7212709 := by
    simpa [prefixWord, tailWord_7212709, baseEnd_7212709] using wordTrace_append hprefix tailTrace_7212709
  have hstable : (prefixWord ++ tailWord_7212709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7212709).length < 2 ^ (prefixWord ++ tailWord_7212709).sum := by decide
  have hdescent : baseEnd_7212709 < baseStart_7212709 := by decide
  rcases family_descends (prefixWord ++ tailWord_7212709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7212722 : List Nat := [3, 2, 1, 1, 1, 2, 2, 1, 3, 1, 6]
def baseStart_7212722 : Nat := 118140960795 + 7212722 * 2 ^ 59
def prefixEnd_7212722 : Nat := 4983230072969 + 3 ^ 40 * 7212722 * 2
def baseEnd_7212722 : Nat := 3703593213258434425704301

theorem tailTrace_7212722 : CollatzResearch.WordTrace tailWord_7212722 prefixEnd_7212722 3703593213258434425704301 := by
  unfold tailWord_7212722
  simp only [CollatzResearch.WordTrace]
  refine ⟨65767395843886875922832105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175379722250365002460885613 65767395843886875922832105)
  ·
    refine ⟨49325546882915156942124079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65767395843886875922832105 49325546882915156942124079)
    ·
      refine ⟨73988320324372735413186119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49325546882915156942124079 73988320324372735413186119)
      ·
        refine ⟨110982480486559103119779179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73988320324372735413186119 110982480486559103119779179)
        ·
          refine ⟨166473720729838654679668769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110982480486559103119779179 166473720729838654679668769)
          ·
            refine ⟨124855290547378991009751577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 166473720729838654679668769 124855290547378991009751577)
            ·
              refine ⟨93641467910534243257313683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 124855290547378991009751577 93641467910534243257313683)
              ·
                refine ⟨140462201865801364885970525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 93641467910534243257313683 140462201865801364885970525)
                ·
                  refine ⟨52673325699675511832238947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 140462201865801364885970525 52673325699675511832238947)
                  ·
                    refine ⟨79009988549513267748358421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 52673325699675511832238947 79009988549513267748358421)
                    ·
                      refine ⟨3703593213258434425704301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 79009988549513267748358421 3703593213258434425704301)
                      ·
                        rfl

theorem cell23_7212722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 1, 3, 1, 6].length) (baseStart_7212722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7212722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7212722 prefixEnd_7212722 := by exact prefixLift 7212722
  have htrace : WordTrace (prefixWord ++ tailWord_7212722) baseStart_7212722 baseEnd_7212722 := by
    simpa [prefixWord, tailWord_7212722, baseEnd_7212722] using wordTrace_append hprefix tailTrace_7212722
  have hstable : (prefixWord ++ tailWord_7212722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7212722).length < 2 ^ (prefixWord ++ tailWord_7212722).sum := by decide
  have hdescent : baseEnd_7212722 < baseStart_7212722 := by decide
  rcases family_descends (prefixWord ++ tailWord_7212722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7212729 : List Nat := [1, 2, 1, 4, 1, 1, 3, 2, 3, 2, 3]
def baseStart_7212729 : Nat := 118140960795 + 7212729 * 2 ^ 59
def prefixEnd_7212729 : Nat := 4983230072969 + 3 ^ 40 * 7212729 * 2
def baseEnd_7212729 : Nat := 3703596807623015898316769

theorem tailTrace_7212729 : CollatzResearch.WordTrace tailWord_7212729 prefixEnd_7212729 3703596807623015898316769 := by
  unfold tailWord_7212729
  simp only [CollatzResearch.WordTrace]
  refine ⟨263069838686522143886833241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175379892457681429257888827 263069838686522143886833241)
  ·
    refine ⟨197302379014891607915124931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 263069838686522143886833241 197302379014891607915124931)
    ·
      refine ⟨295953568522337411872687397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197302379014891607915124931 295953568522337411872687397)
      ·
        refine ⟨55491294097938264726128887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 295953568522337411872687397 55491294097938264726128887)
        ·
          refine ⟨83236941146907397089193331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55491294097938264726128887 83236941146907397089193331)
          ·
            refine ⟨124855411720361095633789997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83236941146907397089193331 124855411720361095633789997)
            ·
              refine ⟨46820779395135410862671249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 124855411720361095633789997 46820779395135410862671249)
              ·
                refine ⟨35115584546351558147003437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46820779395135410862671249 35115584546351558147003437)
                ·
                  refine ⟨13168344204881834305126289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35115584546351558147003437 13168344204881834305126289)
                  ·
                    refine ⟨9876258153661375728844717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13168344204881834305126289 9876258153661375728844717)
                    ·
                      refine ⟨3703596807623015898316769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9876258153661375728844717 3703596807623015898316769)
                      ·
                        rfl

theorem cell23_7212729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 3, 2, 3, 2, 3].length) (baseStart_7212729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7212729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7212729 prefixEnd_7212729 := by exact prefixLift 7212729
  have htrace : WordTrace (prefixWord ++ tailWord_7212729) baseStart_7212729 baseEnd_7212729 := by
    simpa [prefixWord, tailWord_7212729, baseEnd_7212729] using wordTrace_append hprefix tailTrace_7212729
  have hstable : (prefixWord ++ tailWord_7212729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7212729).length < 2 ^ (prefixWord ++ tailWord_7212729).sum := by decide
  have hdescent : baseEnd_7212729 < baseStart_7212729 := by decide
  rcases family_descends (prefixWord ++ tailWord_7212729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7212756 : List Nat := [2, 4, 1, 3, 1, 1, 2, 2, 1, 2, 4]
def baseStart_7212756 : Nat := 118140960795 + 7212756 * 2 ^ 59
def prefixEnd_7212756 : Nat := 4983230072969 + 3 ^ 40 * 7212756 * 2
def baseEnd_7212756 : Nat := 3703610671600687292679145

theorem tailTrace_7212756 : CollatzResearch.WordTrace tailWord_7212756 prefixEnd_7212756 3703610671600687292679145 := by
  unfold tailWord_7212756
  simp only [CollatzResearch.WordTrace]
  refine ⟨131535411728712163749033061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175380548971616218332044081 131535411728712163749033061)
  ·
    refine ⟨24662889699133530702943699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 131535411728712163749033061 24662889699133530702943699)
    ·
      refine ⟨36994334548700296054415549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24662889699133530702943699 36994334548700296054415549)
      ·
        refine ⟨13872875455762611020405831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36994334548700296054415549 13872875455762611020405831)
        ·
          refine ⟨20809313183643916530608747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13872875455762611020405831 20809313183643916530608747)
          ·
            refine ⟨31213969775465874795913121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20809313183643916530608747 31213969775465874795913121)
            ·
              refine ⟨23410477331599406096934841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31213969775465874795913121 23410477331599406096934841)
              ·
                refine ⟨17557857998699554572701131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23410477331599406096934841 17557857998699554572701131)
                ·
                  refine ⟨26336786998049331859051697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17557857998699554572701131 26336786998049331859051697)
                  ·
                    refine ⟨19752590248536998894288773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26336786998049331859051697 19752590248536998894288773)
                    ·
                      refine ⟨3703610671600687292679145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19752590248536998894288773 3703610671600687292679145)
                      ·
                        rfl

theorem cell23_7212756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 2, 2, 1, 2, 4].length) (baseStart_7212756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7212756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7212756 prefixEnd_7212756 := by exact prefixLift 7212756
  have htrace : WordTrace (prefixWord ++ tailWord_7212756) baseStart_7212756 baseEnd_7212756 := by
    simpa [prefixWord, tailWord_7212756, baseEnd_7212756] using wordTrace_append hprefix tailTrace_7212756
  have hstable : (prefixWord ++ tailWord_7212756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7212756).length < 2 ^ (prefixWord ++ tailWord_7212756).sum := by decide
  have hdescent : baseEnd_7212756 < baseStart_7212756 := by decide
  rcases family_descends (prefixWord ++ tailWord_7212756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7212759 : List Nat := [1, 1, 3, 2, 1, 3, 1, 4, 1, 3, 3]
def baseStart_7212759 : Nat := 118140960795 + 7212759 * 2 ^ 59
def prefixEnd_7212759 : Nat := 4983230072969 + 3 ^ 40 * 7212759 * 2
def baseEnd_7212759 : Nat := 3703612212042650780941631

theorem tailTrace_7212759 : CollatzResearch.WordTrace tailWord_7212759 prefixEnd_7212759 3703612212042650780941631 := by
  unfold tailWord_7212759
  simp only [CollatzResearch.WordTrace]
  refine ⟨263070932876413459010425331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175380621917608972673616887 263070932876413459010425331)
  ·
    refine ⟨394606399314620188515637997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263070932876413459010425331 394606399314620188515637997)
    ·
      refine ⟨147977399742982570693364249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 394606399314620188515637997 147977399742982570693364249)
      ·
        refine ⟨110983049807236928020023187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147977399742982570693364249 110983049807236928020023187)
        ·
          refine ⟨166474574710855392030034781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110983049807236928020023187 166474574710855392030034781)
          ·
            refine ⟨62427965516570772011263043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 166474574710855392030034781 62427965516570772011263043)
            ·
              refine ⟨93641948274856158016894565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62427965516570772011263043 93641948274856158016894565)
              ·
                refine ⟨17557865301535529628167731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 93641948274856158016894565 17557865301535529628167731)
                ·
                  refine ⟨26336797952303294442251597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17557865301535529628167731 26336797952303294442251597)
                  ·
                    refine ⟨9876299232113735415844349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26336797952303294442251597 9876299232113735415844349)
                    ·
                      refine ⟨3703612212042650780941631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9876299232113735415844349 3703612212042650780941631)
                      ·
                        rfl

theorem cell23_7212759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 4, 1, 3, 3].length) (baseStart_7212759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7212759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7212759 prefixEnd_7212759 := by exact prefixLift 7212759
  have htrace : WordTrace (prefixWord ++ tailWord_7212759) baseStart_7212759 baseEnd_7212759 := by
    simpa [prefixWord, tailWord_7212759, baseEnd_7212759] using wordTrace_append hprefix tailTrace_7212759
  have hstable : (prefixWord ++ tailWord_7212759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7212759).length < 2 ^ (prefixWord ++ tailWord_7212759).sum := by decide
  have hdescent : baseEnd_7212759 < baseStart_7212759 := by decide
  rcases family_descends (prefixWord ++ tailWord_7212759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7212760 : List Nat := [2, 1, 2, 2, 3, 1, 4, 3, 1, 2, 2]
def baseStart_7212760 : Nat := 118140960795 + 7212760 * 2 ^ 59
def prefixEnd_7212760 : Nat := 4983230072969 + 3 ^ 40 * 7212760 * 2
def baseEnd_7212760 : Nat := 3703612725523305277029127

theorem tailTrace_7212760 : CollatzResearch.WordTrace tailWord_7212760 prefixEnd_7212760 3703612725523305277029127 := by
  unfold tailWord_7212760
  simp only [CollatzResearch.WordTrace]
  refine ⟨131535484674704918090605867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175380646232939890787474489 131535484674704918090605867)
  ·
    refine ⟨197303227012057377135908801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131535484674704918090605867 197303227012057377135908801)
    ·
      refine ⟨147977420259043032851931601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 197303227012057377135908801 147977420259043032851931601)
      ·
        refine ⟨110983065194282274638948701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147977420259043032851931601 110983065194282274638948701)
        ·
          refine ⟨41618649447855852989605763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 110983065194282274638948701 41618649447855852989605763)
          ·
            refine ⟨62427974171783779484408645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41618649447855852989605763 62427974171783779484408645)
            ·
              refine ⟨11705245157209458653326621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 62427974171783779484408645 11705245157209458653326621)
              ·
                refine ⟨4389466933953546994997483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11705245157209458653326621 4389466933953546994997483)
                ·
                  refine ⟨6584200400930320492496225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4389466933953546994997483 6584200400930320492496225)
                  ·
                    refine ⟨4938150300697740369372169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6584200400930320492496225 4938150300697740369372169)
                    ·
                      refine ⟨3703612725523305277029127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4938150300697740369372169 3703612725523305277029127)
                      ·
                        rfl

theorem cell23_7212760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 4, 3, 1, 2, 2].length) (baseStart_7212760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7212760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7212760 prefixEnd_7212760 := by exact prefixLift 7212760
  have htrace : WordTrace (prefixWord ++ tailWord_7212760) baseStart_7212760 baseEnd_7212760 := by
    simpa [prefixWord, tailWord_7212760, baseEnd_7212760] using wordTrace_append hprefix tailTrace_7212760
  have hstable : (prefixWord ++ tailWord_7212760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7212760).length < 2 ^ (prefixWord ++ tailWord_7212760).sum := by decide
  have hdescent : baseEnd_7212760 < baseStart_7212760 := by decide
  rcases family_descends (prefixWord ++ tailWord_7212760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7212792 : List Nat := [2, 1, 2, 1, 1, 2, 2, 3, 1, 8]
def baseStart_7212792 : Nat := 118140960795 + 7212792 * 2 ^ 59
def prefixEnd_7212792 : Nat := 4983230072969 + 3 ^ 40 * 7212792 * 2
def baseEnd_7212792 : Nat := 1234543052301416383942993

theorem tailTrace_7212792 : CollatzResearch.WordTrace tailWord_7212792 prefixEnd_7212792 1234543052301416383942993 := by
  unfold tailWord_7212792
  simp only [CollatzResearch.WordTrace]
  refine ⟨131536068242646952823188315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175381424323529270430917753 131536068242646952823188315)
  ·
    refine ⟨197304102363970429234782473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131536068242646952823188315 197304102363970429234782473)
    ·
      refine ⟨147978076772977821926086855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 197304102363970429234782473 147978076772977821926086855)
      ·
        refine ⟨221967115159466732889130283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147978076772977821926086855 221967115159466732889130283)
        ·
          refine ⟨332950672739200099333695425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 221967115159466732889130283 332950672739200099333695425)
          ·
            refine ⟨249713004554400074500271569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 332950672739200099333695425 249713004554400074500271569)
            ·
              refine ⟨187284753415800055875203677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 249713004554400074500271569 187284753415800055875203677)
              ·
                refine ⟨70231782530925020953201379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 187284753415800055875203677 70231782530925020953201379)
                ·
                  refine ⟨105347673796387531429802069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70231782530925020953201379 105347673796387531429802069)
                  ·
                    refine ⟨1234543052301416383942993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 105347673796387531429802069 1234543052301416383942993)
                    ·
                      rfl

theorem cell23_7212792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 3, 1, 8].length) (baseStart_7212792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7212792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7212792 prefixEnd_7212792 := by exact prefixLift 7212792
  have htrace : WordTrace (prefixWord ++ tailWord_7212792) baseStart_7212792 baseEnd_7212792 := by
    simpa [prefixWord, tailWord_7212792, baseEnd_7212792] using wordTrace_append hprefix tailTrace_7212792
  have hstable : (prefixWord ++ tailWord_7212792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7212792).length < 2 ^ (prefixWord ++ tailWord_7212792).sum := by decide
  have hdescent : baseEnd_7212792 < baseStart_7212792 := by decide
  rcases family_descends (prefixWord ++ tailWord_7212792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7212833 : List Nat := [1, 2, 3, 2, 1, 3, 2, 1, 4, 2, 2]
def baseStart_7212833 : Nat := 118140960795 + 7212833 * 2 ^ 59
def prefixEnd_7212833 : Nat := 4983230072969 + 3 ^ 40 * 7212833 * 2
def baseEnd_7212833 : Nat := 3703650209611083491416291

theorem tailTrace_7212833 : CollatzResearch.WordTrace tailWord_7212833 prefixEnd_7212833 3703650209611083491416291 := by
  unfold tailWord_7212833
  simp only [CollatzResearch.WordTrace]
  refine ⟨263073631878145369648619153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175382421252096913099079435 263073631878145369648619153)
  ·
    refine ⟨197305223908609027236464365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 263073631878145369648619153 197305223908609027236464365)
    ·
      refine ⟨73989458965728385213674137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 197305223908609027236464365 73989458965728385213674137)
      ·
        refine ⟨55492094224296288910255603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73989458965728385213674137 55492094224296288910255603)
        ·
          refine ⟨83238141336444433365383405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55492094224296288910255603 83238141336444433365383405)
          ·
            refine ⟨31214303001166662512018777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 83238141336444433365383405 31214303001166662512018777)
            ·
              refine ⟨23410727250874996884014083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31214303001166662512018777 23410727250874996884014083)
              ·
                refine ⟨35116090876312495326021125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23410727250874996884014083 35116090876312495326021125)
                ·
                  refine ⟨6584267039308592873628961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35116090876312495326021125 6584267039308592873628961)
                  ·
                    refine ⟨4938200279481444655221721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6584267039308592873628961 4938200279481444655221721)
                    ·
                      refine ⟨3703650209611083491416291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4938200279481444655221721 3703650209611083491416291)
                      ·
                        rfl

theorem cell23_7212833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 2, 1, 4, 2, 2].length) (baseStart_7212833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7212833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7212833 prefixEnd_7212833 := by exact prefixLift 7212833
  have htrace : WordTrace (prefixWord ++ tailWord_7212833) baseStart_7212833 baseEnd_7212833 := by
    simpa [prefixWord, tailWord_7212833, baseEnd_7212833] using wordTrace_append hprefix tailTrace_7212833
  have hstable : (prefixWord ++ tailWord_7212833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7212833).length < 2 ^ (prefixWord ++ tailWord_7212833).sum := by decide
  have hdescent : baseEnd_7212833 < baseStart_7212833 := by decide
  rcases family_descends (prefixWord ++ tailWord_7212833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7212850 : List Nat := [3, 2, 1, 1, 3, 3, 1, 3, 2, 2, 2]
def baseStart_7212850 : Nat := 118140960795 + 7212850 * 2 ^ 59
def prefixEnd_7212850 : Nat := 4983230072969 + 3 ^ 40 * 7212850 * 2
def baseEnd_7212850 : Nat := 3703658938782209924903713

theorem tailTrace_7212850 : CollatzResearch.WordTrace tailWord_7212850 prefixEnd_7212850 3703658938782209924903713 := by
  unfold tailWord_7212850
  simp only [CollatzResearch.WordTrace]
  refine ⟨65768562979770945387997001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175382834612722521034658669 65768562979770945387997001)
  ·
    refine ⟨49326422234828209040997751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65768562979770945387997001 49326422234828209040997751)
    ·
      refine ⟨73989633352242313561496627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49326422234828209040997751 73989633352242313561496627)
      ·
        refine ⟨110984450028363470342244941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73989633352242313561496627 110984450028363470342244941)
        ·
          refine ⟨41619168760636301378341853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 110984450028363470342244941 41619168760636301378341853)
          ·
            refine ⟨15607188285238613016878195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41619168760636301378341853 15607188285238613016878195)
            ·
              refine ⟨23410782427857919525317293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15607188285238613016878195 23410782427857919525317293)
              ·
                refine ⟨8779043410446719821993985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23410782427857919525317293 8779043410446719821993985)
                ·
                  refine ⟨6584282557835039866495489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8779043410446719821993985 6584282557835039866495489)
                  ·
                    refine ⟨4938211918376279899871617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6584282557835039866495489 4938211918376279899871617)
                    ·
                      refine ⟨3703658938782209924903713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4938211918376279899871617 3703658938782209924903713)
                      ·
                        rfl

theorem cell23_7212850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 1, 3, 2, 2, 2].length) (baseStart_7212850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7212850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7212850 prefixEnd_7212850 := by exact prefixLift 7212850
  have htrace : WordTrace (prefixWord ++ tailWord_7212850) baseStart_7212850 baseEnd_7212850 := by
    simpa [prefixWord, tailWord_7212850, baseEnd_7212850] using wordTrace_append hprefix tailTrace_7212850
  have hstable : (prefixWord ++ tailWord_7212850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7212850).length < 2 ^ (prefixWord ++ tailWord_7212850).sum := by decide
  have hdescent : baseEnd_7212850 < baseStart_7212850 := by decide
  rcases family_descends (prefixWord ++ tailWord_7212850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7212949 : List Nat := [1, 3, 2, 1, 1, 3, 1, 1, 1, 1, 8]
def baseStart_7212949 : Nat := 118140960795 + 7212949 * 2 ^ 59
def prefixEnd_7212949 : Nat := 4983230072969 + 3 ^ 40 * 7212949 * 2
def baseEnd_7212949 : Nat := 3703709773367005037565757

theorem tailTrace_7212949 : CollatzResearch.WordTrace tailWord_7212949 prefixEnd_7212949 3703709773367005037565757 := by
  unfold tailWord_7212949
  simp only [CollatzResearch.WordTrace]
  refine ⟨263077862745725121459841901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175385241830483414306561267 263077862745725121459841901)
  ·
    refine ⟨98654198529646920547440713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 263077862745725121459841901 98654198529646920547440713)
    ·
      refine ⟨73990648897235190410580535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98654198529646920547440713 73990648897235190410580535)
      ·
        refine ⟨110985973345852785615870803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73990648897235190410580535 110985973345852785615870803)
        ·
          refine ⟨166478960018779178423806205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110985973345852785615870803 166478960018779178423806205)
          ·
            refine ⟨62429610007042191908927327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 166478960018779178423806205 62429610007042191908927327)
            ·
              refine ⟨93644415010563287863390991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62429610007042191908927327 93644415010563287863390991)
              ·
                refine ⟨140466622515844931795086487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 93644415010563287863390991 140466622515844931795086487)
                ·
                  refine ⟨210699933773767397692629731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 140466622515844931795086487 210699933773767397692629731)
                  ·
                    refine ⟨316049900660651096538944597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 210699933773767397692629731 316049900660651096538944597)
                    ·
                      refine ⟨3703709773367005037565757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 316049900660651096538944597 3703709773367005037565757)
                      ·
                        rfl

theorem cell23_7212949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 1, 1, 1, 8].length) (baseStart_7212949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7212949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7212949 prefixEnd_7212949 := by exact prefixLift 7212949
  have htrace : WordTrace (prefixWord ++ tailWord_7212949) baseStart_7212949 baseEnd_7212949 := by
    simpa [prefixWord, tailWord_7212949, baseEnd_7212949] using wordTrace_append hprefix tailTrace_7212949
  have hstable : (prefixWord ++ tailWord_7212949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7212949).length < 2 ^ (prefixWord ++ tailWord_7212949).sum := by decide
  have hdescent : baseEnd_7212949 < baseStart_7212949 := by decide
  rcases family_descends (prefixWord ++ tailWord_7212949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7212983 : List Nat := [1, 1, 3, 1, 3, 1, 1, 5, 2, 3, 2]
def baseStart_7212983 : Nat := 118140960795 + 7212983 * 2 ^ 59
def prefixEnd_7212983 : Nat := 4983230072969 + 3 ^ 40 * 7212983 * 2
def baseEnd_7212983 : Nat := 3703727231709257904540601

theorem tailTrace_7212983 : CollatzResearch.WordTrace tailWord_7212983 prefixEnd_7212983 3703727231709257904540601 := by
  unfold tailWord_7212983
  simp only [CollatzResearch.WordTrace]
  refine ⟨263079102827601945266579603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175386068551734630177719735 263079102827601945266579603)
  ·
    refine ⟨394618654241402917899869405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263079102827601945266579603 394618654241402917899869405)
    ·
      refine ⟨147981995340526094212451027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 394618654241402917899869405 147981995340526094212451027)
      ·
        refine ⟨221972993010789141318676541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147981995340526094212451027 221972993010789141318676541)
        ·
          refine ⟨83239872379045927994503703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 221972993010789141318676541 83239872379045927994503703)
          ·
            refine ⟨124859808568568891991755555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83239872379045927994503703 124859808568568891991755555)
            ·
              refine ⟨187289712852853337987633333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 124859808568568891991755555 187289712852853337987633333)
              ·
                refine ⟨17558410579955000436340625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 187289712852853337987633333 17558410579955000436340625)
                ·
                  refine ⟨13168807934966250327255469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17558410579955000436340625 13168807934966250327255469)
                  ·
                    refine ⟨4938302975612343872720801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13168807934966250327255469 4938302975612343872720801)
                    ·
                      refine ⟨3703727231709257904540601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4938302975612343872720801 3703727231709257904540601)
                      ·
                        rfl

theorem cell23_7212983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 5, 2, 3, 2].length) (baseStart_7212983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7212983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7212983 prefixEnd_7212983 := by exact prefixLift 7212983
  have htrace : WordTrace (prefixWord ++ tailWord_7212983) baseStart_7212983 baseEnd_7212983 := by
    simpa [prefixWord, tailWord_7212983, baseEnd_7212983] using wordTrace_append hprefix tailTrace_7212983
  have hstable : (prefixWord ++ tailWord_7212983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7212983).length < 2 ^ (prefixWord ++ tailWord_7212983).sum := by decide
  have hdescent : baseEnd_7212983 < baseStart_7212983 := by decide
  rcases family_descends (prefixWord ++ tailWord_7212983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7213000 : List Nat := [2, 1, 3, 1, 4, 2, 1, 2, 2, 3, 2]
def baseStart_7213000 : Nat := 118140960795 + 7213000 * 2 ^ 59
def prefixEnd_7213000 : Nat := 4983230072969 + 3 ^ 40 * 7213000 * 2
def baseEnd_7213000 : Nat := 3703735960880384338028023

theorem tailTrace_7213000 : CollatzResearch.WordTrace tailWord_7213000 prefixEnd_7213000 3703735960880384338028023 := by
  unfold tailWord_7213000
  simp only [CollatzResearch.WordTrace]
  refine ⟨131539861434270178584974227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175386481912360238113298969 131539861434270178584974227)
  ·
    refine ⟨197309792151405267877461341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131539861434270178584974227 197309792151405267877461341)
    ·
      refine ⟨73991172056776975454048003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 197309792151405267877461341 73991172056776975454048003)
      ·
        refine ⟨110986758085165463181072005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73991172056776975454048003 110986758085165463181072005)
        ·
          refine ⟨20810017140968524346451001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 110986758085165463181072005 20810017140968524346451001)
          ·
            refine ⟨15607512855726393259838251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20810017140968524346451001 15607512855726393259838251)
            ·
              refine ⟨23411269283589589889757377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15607512855726393259838251 23411269283589589889757377)
              ·
                refine ⟨17558451962692192417318033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23411269283589589889757377 17558451962692192417318033)
                ·
                  refine ⟨13168838972019144312988525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17558451962692192417318033 13168838972019144312988525)
                  ·
                    refine ⟨4938314614507179117370697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13168838972019144312988525 4938314614507179117370697)
                    ·
                      refine ⟨3703735960880384338028023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4938314614507179117370697 3703735960880384338028023)
                      ·
                        rfl

theorem cell23_7213000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 1, 2, 2, 3, 2].length) (baseStart_7213000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7213000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7213000 prefixEnd_7213000 := by exact prefixLift 7213000
  have htrace : WordTrace (prefixWord ++ tailWord_7213000) baseStart_7213000 baseEnd_7213000 := by
    simpa [prefixWord, tailWord_7213000, baseEnd_7213000] using wordTrace_append hprefix tailTrace_7213000
  have hstable : (prefixWord ++ tailWord_7213000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7213000).length < 2 ^ (prefixWord ++ tailWord_7213000).sum := by decide
  have hdescent : baseEnd_7213000 < baseStart_7213000 := by decide
  rcases family_descends (prefixWord ++ tailWord_7213000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7213007 : List Nat := [1, 1, 2, 1, 1, 5, 5, 2, 1, 1, 3]
def baseStart_7213007 : Nat := 118140960795 + 7213007 * 2 ^ 59
def prefixEnd_7213007 : Nat := 4983230072969 + 3 ^ 40 * 7213007 * 2
def baseEnd_7213007 : Nat := 3703739555244965810640491

theorem tailTrace_7213007 : CollatzResearch.WordTrace tailWord_7213007 prefixEnd_7213007 3703739555244965810640491 := by
  unfold tailWord_7213007
  simp only [CollatzResearch.WordTrace]
  refine ⟨263079978179514997365453275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175386652119676664910302183 263079978179514997365453275)
  ·
    refine ⟨394619967269272496048179913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263079978179514997365453275 394619967269272496048179913)
    ·
      refine ⟨295964975451954372036134935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 394619967269272496048179913 295964975451954372036134935)
      ·
        refine ⟨443947463177931558054202403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 295964975451954372036134935 443947463177931558054202403)
        ·
          refine ⟨665921194766897337081303605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 443947463177931558054202403 665921194766897337081303605)
          ·
            refine ⟨62430112009396625351372213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 665921194766897337081303605 62430112009396625351372213)
            ·
              refine ⟨5852823000880933626691145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 62430112009396625351372213 5852823000880933626691145)
              ·
                refine ⟨4389617250660700220018359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5852823000880933626691145 4389617250660700220018359)
                ·
                  refine ⟨6584425875991050330027539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4389617250660700220018359 6584425875991050330027539)
                  ·
                    refine ⟨9876638813986575495041309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6584425875991050330027539 9876638813986575495041309)
                    ·
                      refine ⟨3703739555244965810640491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9876638813986575495041309 3703739555244965810640491)
                      ·
                        rfl

theorem cell23_7213007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 5, 2, 1, 1, 3].length) (baseStart_7213007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7213007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7213007 prefixEnd_7213007 := by exact prefixLift 7213007
  have htrace : WordTrace (prefixWord ++ tailWord_7213007) baseStart_7213007 baseEnd_7213007 := by
    simpa [prefixWord, tailWord_7213007, baseEnd_7213007] using wordTrace_append hprefix tailTrace_7213007
  have hstable : (prefixWord ++ tailWord_7213007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7213007).length < 2 ^ (prefixWord ++ tailWord_7213007).sum := by decide
  have hdescent : baseEnd_7213007 < baseStart_7213007 := by decide
  rcases family_descends (prefixWord ++ tailWord_7213007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7213014 : List Nat := [5, 2, 1, 1, 4, 1, 2, 1, 6]
def baseStart_7213014 : Nat := 118140960795 + 7213014 * 2 ^ 59
def prefixEnd_7213014 : Nat := 4983230072969 + 3 ^ 40 * 7213014 * 2
def baseEnd_7213014 : Nat := 411527016623283031472551

theorem tailTrace_7213014 : CollatzResearch.WordTrace tailWord_7213014 prefixEnd_7213014 411527016623283031472551 := by
  unfold tailWord_7213014
  simp only [CollatzResearch.WordTrace]
  refine ⟨16442514593155602347559881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 175386822326993091707305397 16442514593155602347559881)
  ·
    refine ⟨12331885944866701760669911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16442514593155602347559881 12331885944866701760669911)
    ·
      refine ⟨18497828917300052641004867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12331885944866701760669911 18497828917300052641004867)
      ·
        refine ⟨27746743375950078961507301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18497828917300052641004867 27746743375950078961507301)
        ·
          refine ⟨5202514382990639805282619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27746743375950078961507301 5202514382990639805282619)
          ·
            refine ⟨7803771574485959707923929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5202514382990639805282619 7803771574485959707923929)
            ·
              refine ⟨5852828680864469780942947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7803771574485959707923929 5852828680864469780942947)
              ·
                refine ⟨8779243021296704671414421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5852828680864469780942947 8779243021296704671414421)
                ·
                  refine ⟨411527016623283031472551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8779243021296704671414421 411527016623283031472551)
                  ·
                    rfl

theorem cell23_7213014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 4, 1, 2, 1, 6].length) (baseStart_7213014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7213014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7213014 prefixEnd_7213014 := by exact prefixLift 7213014
  have htrace : WordTrace (prefixWord ++ tailWord_7213014) baseStart_7213014 baseEnd_7213014 := by
    simpa [prefixWord, tailWord_7213014, baseEnd_7213014] using wordTrace_append hprefix tailTrace_7213014
  have hstable : (prefixWord ++ tailWord_7213014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7213014).length < 2 ^ (prefixWord ++ tailWord_7213014).sum := by decide
  have hdescent : baseEnd_7213014 < baseStart_7213014 := by decide
  rcases family_descends (prefixWord ++ tailWord_7213014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7213016 : List Nat := [2, 1, 2, 2, 2, 2, 1, 4, 1, 1, 5]
def baseStart_7213016 : Nat := 118140960795 + 7213016 * 2 ^ 59
def prefixEnd_7213016 : Nat := 4983230072969 + 3 ^ 40 * 7213016 * 2
def baseEnd_7213016 : Nat := 3703744176570856275427949

theorem tailTrace_7213016 : CollatzResearch.WordTrace tailWord_7213016 prefixEnd_7213016 3703744176570856275427949 := by
  unfold tailWord_7213016
  simp only [CollatzResearch.WordTrace]
  refine ⟨131540153218241195951265451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175386870957654927935020601 131540153218241195951265451)
  ·
    refine ⟨197310229827361793926898177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131540153218241195951265451 197310229827361793926898177)
    ·
      refine ⟨147982672370521345445173633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 197310229827361793926898177 147982672370521345445173633)
      ·
        refine ⟨110987004277891009083880225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147982672370521345445173633 110987004277891009083880225)
        ·
          refine ⟨83240253208418256812910169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110987004277891009083880225 83240253208418256812910169)
          ·
            refine ⟨62430189906313692609682627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83240253208418256812910169 62430189906313692609682627)
            ·
              refine ⟨93645284859470538914523941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62430189906313692609682627 93645284859470538914523941)
              ·
                refine ⟨17558490911150726046473239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 93645284859470538914523941 17558490911150726046473239)
                ·
                  refine ⟨26337736366726089069709859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17558490911150726046473239 26337736366726089069709859)
                  ·
                    refine ⟨39506604550089133604564789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26337736366726089069709859 39506604550089133604564789)
                    ·
                      refine ⟨3703744176570856275427949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39506604550089133604564789 3703744176570856275427949)
                      ·
                        rfl

theorem cell23_7213016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 4, 1, 1, 5].length) (baseStart_7213016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7213016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7213016 prefixEnd_7213016 := by exact prefixLift 7213016
  have htrace : WordTrace (prefixWord ++ tailWord_7213016) baseStart_7213016 baseEnd_7213016 := by
    simpa [prefixWord, tailWord_7213016, baseEnd_7213016] using wordTrace_append hprefix tailTrace_7213016
  have hstable : (prefixWord ++ tailWord_7213016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7213016).length < 2 ^ (prefixWord ++ tailWord_7213016).sum := by decide
  have hdescent : baseEnd_7213016 < baseStart_7213016 := by decide
  rcases family_descends (prefixWord ++ tailWord_7213016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7213080 : List Nat := [2, 1, 2, 3, 2, 1, 1, 5, 2, 1, 3]
def baseStart_7213080 : Nat := 118140960795 + 7213080 * 2 ^ 59
def prefixEnd_7213080 : Nat := 4983230072969 + 3 ^ 40 * 7213080 * 2
def baseEnd_7213080 : Nat := 3703777039332744025027655

theorem tailTrace_7213080 : CollatzResearch.WordTrace tailWord_7213080 prefixEnd_7213080 3703777039332744025027655 := by
  unfold tailWord_7213080
  simp only [CollatzResearch.WordTrace]
  refine ⟨131541320354125265416430347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175388427138833687221907129 131541320354125265416430347)
  ·
    refine ⟨197311980531187898124645521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131541320354125265416430347 197311980531187898124645521)
    ·
      refine ⟨147983985398390923593484141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 197311980531187898124645521 147983985398390923593484141)
      ·
        refine ⟨55493994524396596347556553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 147983985398390923593484141 55493994524396596347556553)
        ·
          refine ⟨41620495893297447260667415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55493994524396596347556553 41620495893297447260667415)
          ·
            refine ⟨62430743839946170891001123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41620495893297447260667415 62430743839946170891001123)
            ·
              refine ⟨93646115759919256336501685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62430743839946170891001123 93646115759919256336501685)
              ·
                refine ⟨8779323352492430281547033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 93646115759919256336501685 8779323352492430281547033)
                ·
                  refine ⟨6584492514369322711160275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8779323352492430281547033 6584492514369322711160275)
                  ·
                    refine ⟨9876738771553984066740413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6584492514369322711160275 9876738771553984066740413)
                    ·
                      refine ⟨3703777039332744025027655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9876738771553984066740413 3703777039332744025027655)
                      ·
                        rfl

theorem cell23_7213080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 5, 2, 1, 3].length) (baseStart_7213080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7213080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7213080 prefixEnd_7213080 := by exact prefixLift 7213080
  have htrace : WordTrace (prefixWord ++ tailWord_7213080) baseStart_7213080 baseEnd_7213080 := by
    simpa [prefixWord, tailWord_7213080, baseEnd_7213080] using wordTrace_append hprefix tailTrace_7213080
  have hstable : (prefixWord ++ tailWord_7213080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7213080).length < 2 ^ (prefixWord ++ tailWord_7213080).sum := by decide
  have hdescent : baseEnd_7213080 < baseStart_7213080 := by decide
  rcases family_descends (prefixWord ++ tailWord_7213080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7213090 : List Nat := [3, 3, 1, 1, 1, 2, 1, 3, 3, 3, 2]
def baseStart_7213090 : Nat := 118140960795 + 7213090 * 2 ^ 59
def prefixEnd_7213090 : Nat := 4983230072969 + 3 ^ 40 * 7213090 * 2
def baseEnd_7213090 : Nat := 3703782174139288985902609

theorem tailTrace_7213090 : CollatzResearch.WordTrace tailWord_7213090 prefixEnd_7213090 3703782174139288985902609 := by
  unfold tailWord_7213090
  simp only [CollatzResearch.WordTrace]
  refine ⟨65770751359553575635181181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175388670292142868360483149 65770751359553575635181181)
  ·
    refine ⟨24664031759832590863192943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65770751359553575635181181 24664031759832590863192943)
    ·
      refine ⟨36996047639748886294789415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24664031759832590863192943 36996047639748886294789415)
      ·
        refine ⟨55494071459623329442184123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36996047639748886294789415 55494071459623329442184123)
        ·
          refine ⟨83241107189434994163276185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55494071459623329442184123 83241107189434994163276185)
          ·
            refine ⟨62430830392076245622457139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83241107189434994163276185 62430830392076245622457139)
            ·
              refine ⟨93646245588114368433685709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62430830392076245622457139 93646245588114368433685709)
              ·
                refine ⟨35117342095542888162632141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 93646245588114368433685709 35117342095542888162632141)
                ·
                  refine ⟨13169003285828583060987053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35117342095542888162632141 13169003285828583060987053)
                  ·
                    refine ⟨4938376232185718647870145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13169003285828583060987053 4938376232185718647870145)
                    ·
                      refine ⟨3703782174139288985902609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4938376232185718647870145 3703782174139288985902609)
                      ·
                        rfl

theorem cell23_7213090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 3, 3, 3, 2].length) (baseStart_7213090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7213090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7213090 prefixEnd_7213090 := by exact prefixLift 7213090
  have htrace : WordTrace (prefixWord ++ tailWord_7213090) baseStart_7213090 baseEnd_7213090 := by
    simpa [prefixWord, tailWord_7213090, baseEnd_7213090] using wordTrace_append hprefix tailTrace_7213090
  have hstable : (prefixWord ++ tailWord_7213090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7213090).length < 2 ^ (prefixWord ++ tailWord_7213090).sum := by decide
  have hdescent : baseEnd_7213090 < baseStart_7213090 := by decide
  rcases family_descends (prefixWord ++ tailWord_7213090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7213103 : List Nat := [1, 1, 2, 1, 2, 1, 1, 5, 3, 4, 2]
def baseStart_7213103 : Nat := 118140960795 + 7213103 * 2 ^ 59
def prefixEnd_7213103 : Nat := 4983230072969 + 3 ^ 40 * 7213103 * 2
def baseEnd_7213103 : Nat := 3703788849387797435040049

theorem tailTrace_7213103 : CollatzResearch.WordTrace tailWord_7213103 prefixEnd_7213103 3703788849387797435040049 := by
  unfold tailWord_7213103
  simp only [CollatzResearch.WordTrace]
  refine ⟨263083479587167205760947963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175388986391444803840631975 263083479587167205760947963)
  ·
    refine ⟨394625219380750808641421945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263083479587167205760947963 394625219380750808641421945)
    ·
      refine ⟨295968914535563106481066459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 394625219380750808641421945 295968914535563106481066459)
      ·
        refine ⟨443953371803344659721599689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 295968914535563106481066459 443953371803344659721599689)
        ·
          refine ⟨332965028852508494791199767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 443953371803344659721599689 332965028852508494791199767)
          ·
            refine ⟨499447543278762742186799651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 332965028852508494791199767 499447543278762742186799651)
            ·
              refine ⟨749171314918144113280199477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 499447543278762742186799651 749171314918144113280199477)
              ·
                refine ⟨70234810773576010620018701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 749171314918144113280199477 70234810773576010620018701)
                ·
                  refine ⟨26338054040091003982507013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 70234810773576010620018701 26338054040091003982507013)
                  ·
                    refine ⟨4938385132517063246720065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26338054040091003982507013 4938385132517063246720065)
                    ·
                      refine ⟨3703788849387797435040049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4938385132517063246720065 3703788849387797435040049)
                      ·
                        rfl

theorem cell23_7213103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 5, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 5, 3, 4, 2].length) (baseStart_7213103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7213103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7213103 prefixEnd_7213103 := by exact prefixLift 7213103
  have htrace : WordTrace (prefixWord ++ tailWord_7213103) baseStart_7213103 baseEnd_7213103 := by
    simpa [prefixWord, tailWord_7213103, baseEnd_7213103] using wordTrace_append hprefix tailTrace_7213103
  have hstable : (prefixWord ++ tailWord_7213103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7213103).length < 2 ^ (prefixWord ++ tailWord_7213103).sum := by decide
  have hdescent : baseEnd_7213103 < baseStart_7213103 := by decide
  rcases family_descends (prefixWord ++ tailWord_7213103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7213107 : List Nat := [1, 1, 1, 2, 4, 1, 6, 1, 1, 3, 2]
def baseStart_7213107 : Nat := 118140960795 + 7213107 * 2 ^ 59
def prefixEnd_7213107 : Nat := 4983230072969 + 3 ^ 40 * 7213107 * 2
def baseEnd_7213107 : Nat := 3703790903310415419390031

theorem tailTrace_7213107 : CollatzResearch.WordTrace tailWord_7213107 prefixEnd_7213107 3703790903310415419390031 := by
  unfold tailWord_7213107
  simp only [CollatzResearch.WordTrace]
  refine ⟨263083625479152714444093575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175389083652768476296062383 263083625479152714444093575)
  ·
    refine ⟨394625438218729071666140363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263083625479152714444093575 394625438218729071666140363)
    ·
      refine ⟨591938157328093607499210545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 394625438218729071666140363 591938157328093607499210545)
      ·
        refine ⟨443953617996070205624407909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 591938157328093607499210545 443953617996070205624407909)
        ·
          refine ⟨83241303374263163554576483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 443953617996070205624407909 83241303374263163554576483)
          ·
            refine ⟨124861955061394745331864725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83241303374263163554576483 124861955061394745331864725)
            ·
              refine ⟨5852904143502878687431159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 124861955061394745331864725 5852904143502878687431159)
              ·
                refine ⟨8779356215254318031146739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5852904143502878687431159 8779356215254318031146739)
                ·
                  refine ⟨13169034322881477046720109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8779356215254318031146739 13169034322881477046720109)
                  ·
                    refine ⟨4938387871080553892520041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13169034322881477046720109 4938387871080553892520041)
                    ·
                      refine ⟨3703790903310415419390031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4938387871080553892520041 3703790903310415419390031)
                      ·
                        rfl

theorem cell23_7213107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 6, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 6, 1, 1, 3, 2].length) (baseStart_7213107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7213107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7213107 prefixEnd_7213107 := by exact prefixLift 7213107
  have htrace : WordTrace (prefixWord ++ tailWord_7213107) baseStart_7213107 baseEnd_7213107 := by
    simpa [prefixWord, tailWord_7213107, baseEnd_7213107] using wordTrace_append hprefix tailTrace_7213107
  have hstable : (prefixWord ++ tailWord_7213107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7213107).length < 2 ^ (prefixWord ++ tailWord_7213107).sum := by decide
  have hdescent : baseEnd_7213107 < baseStart_7213107 := by decide
  rcases family_descends (prefixWord ++ tailWord_7213107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7213177 : List Nat := [1, 2, 1, 3, 4, 2, 3, 2, 5]
def baseStart_7213177 : Nat := 118140960795 + 7213177 * 2 ^ 59
def prefixEnd_7213177 : Nat := 4983230072969 + 3 ^ 40 * 7213177 * 2
def baseEnd_7213177 : Nat := 411536316328470016168301

theorem tailTrace_7213177 : CollatzResearch.WordTrace tailWord_7213177 prefixEnd_7213177 411536316328470016168301 := by
  unfold tailWord_7213177
  simp only [CollatzResearch.WordTrace]
  refine ⟨263086178588899116399141785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175390785725932744266094523 263086178588899116399141785)
  ·
    refine ⟨197314633941674337299356339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 263086178588899116399141785 197314633941674337299356339)
    ·
      refine ⟨295971950912511505949034509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197314633941674337299356339 295971950912511505949034509)
      ·
        refine ⟨110989481592191814730887941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 295971950912511505949034509 110989481592191814730887941)
        ·
          refine ⟨20810527798535965262041489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 110989481592191814730887941 20810527798535965262041489)
          ·
            refine ⟨15607895848901973946531117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20810527798535965262041489 15607895848901973946531117)
            ·
              refine ⟨5852960943338240229949169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15607895848901973946531117 5852960943338240229949169)
              ·
                refine ⟨4389720707503680172461877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5852960943338240229949169 4389720707503680172461877)
                ·
                  refine ⟨411536316328470016168301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4389720707503680172461877 411536316328470016168301)
                  ·
                    rfl

theorem cell23_7213177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 3, 2, 5].length) (baseStart_7213177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7213177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7213177 prefixEnd_7213177 := by exact prefixLift 7213177
  have htrace : WordTrace (prefixWord ++ tailWord_7213177) baseStart_7213177 baseEnd_7213177 := by
    simpa [prefixWord, tailWord_7213177, baseEnd_7213177] using wordTrace_append hprefix tailTrace_7213177
  have hstable : (prefixWord ++ tailWord_7213177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7213177).length < 2 ^ (prefixWord ++ tailWord_7213177).sum := by decide
  have hdescent : baseEnd_7213177 < baseStart_7213177 := by decide
  rcases family_descends (prefixWord ++ tailWord_7213177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7213193 : List Nat := [1, 2, 1, 1, 4, 2, 1, 2, 4, 1, 4]
def baseStart_7213193 : Nat := 118140960795 + 7213193 * 2 ^ 59
def prefixEnd_7213193 : Nat := 4983230072969 + 3 ^ 40 * 7213193 * 2
def baseEnd_7213193 : Nat := 3703835062646702082914635

theorem tailTrace_7213193 : CollatzResearch.WordTrace tailWord_7213193 prefixEnd_7213193 3703835062646702082914635 := by
  unfold tailWord_7213193
  simp only [CollatzResearch.WordTrace]
  refine ⟨263086762156841151131724233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175391174771227434087816155 263086762156841151131724233)
  ·
    refine ⟨197315071617630863348793175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 263086762156841151131724233 197315071617630863348793175)
    ·
      refine ⟨295972607426446295023189763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197315071617630863348793175 295972607426446295023189763)
      ·
        refine ⟨443958911139669442534784645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 295972607426446295023189763 443958911139669442534784645)
        ·
          refine ⟨83242295838688020475272121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 443958911139669442534784645 83242295838688020475272121)
          ·
            refine ⟨62431721879016015356454091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83242295838688020475272121 62431721879016015356454091)
            ·
              refine ⟨93647582818524023034681137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62431721879016015356454091 93647582818524023034681137)
              ·
                refine ⟨70235687113893017276010853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 93647582818524023034681137 70235687113893017276010853)
                ·
                  refine ⟨13169191333854940739252035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 70235687113893017276010853 13169191333854940739252035)
                  ·
                    refine ⟨19753787000782411108878053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13169191333854940739252035 19753787000782411108878053)
                    ·
                      refine ⟨3703835062646702082914635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19753787000782411108878053 3703835062646702082914635)
                      ·
                        rfl

theorem cell23_7213193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 2, 4, 1, 4].length) (baseStart_7213193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7213193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7213193 prefixEnd_7213193 := by exact prefixLift 7213193
  have htrace : WordTrace (prefixWord ++ tailWord_7213193) baseStart_7213193 baseEnd_7213193 := by
    simpa [prefixWord, tailWord_7213193, baseEnd_7213193] using wordTrace_append hprefix tailTrace_7213193
  have hstable : (prefixWord ++ tailWord_7213193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7213193).length < 2 ^ (prefixWord ++ tailWord_7213193).sum := by decide
  have hdescent : baseEnd_7213193 < baseStart_7213193 := by decide
  rcases family_descends (prefixWord ++ tailWord_7213193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7213203 : List Nat := [1, 1, 1, 2, 1, 2, 3, 3, 5, 4]
def baseStart_7213203 : Nat := 118140960795 + 7213203 * 2 ^ 59
def prefixEnd_7213203 : Nat := 4983230072969 + 3 ^ 40 * 7213203 * 2
def baseEnd_7213203 : Nat := 1234613399151082347929863

theorem tailTrace_7213203 : CollatzResearch.WordTrace tailWord_7213203 prefixEnd_7213203 1234613399151082347929863 := by
  unfold tailWord_7213203
  simp only [CollatzResearch.WordTrace]
  refine ⟨263087126886804922839588263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175391417924536615226392175 263087126886804922839588263)
  ·
    refine ⟨394630690330207384259382395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263087126886804922839588263 394630690330207384259382395)
    ·
      refine ⟨591946035495311076389073593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 394630690330207384259382395 591946035495311076389073593)
      ·
        refine ⟨443959526621483307291805195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 591946035495311076389073593 443959526621483307291805195)
        ·
          refine ⟨665939289932224960937707793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 443959526621483307291805195 665939289932224960937707793)
          ·
            refine ⟨499454467449168720703280845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 665939289932224960937707793 499454467449168720703280845)
            ·
              refine ⟨187295425293438270263730317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 499454467449168720703280845 187295425293438270263730317)
              ·
                refine ⟨70235784485039351348898869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 187295425293438270263730317 70235784485039351348898869)
                ·
                  refine ⟨6584604795472439188959269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 70235784485039351348898869 6584604795472439188959269)
                  ·
                    refine ⟨1234613399151082347929863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6584604795472439188959269 1234613399151082347929863)
                    ·
                      rfl

theorem cell23_7213203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 3, 5, 4].length) (baseStart_7213203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7213203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7213203 prefixEnd_7213203 := by exact prefixLift 7213203
  have htrace : WordTrace (prefixWord ++ tailWord_7213203) baseStart_7213203 baseEnd_7213203 := by
    simpa [prefixWord, tailWord_7213203, baseEnd_7213203] using wordTrace_append hprefix tailTrace_7213203
  have hstable : (prefixWord ++ tailWord_7213203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7213203).length < 2 ^ (prefixWord ++ tailWord_7213203).sum := by decide
  have hdescent : baseEnd_7213203 < baseStart_7213203 := by decide
  rcases family_descends (prefixWord ++ tailWord_7213203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7213263 : List Nat := [1, 1, 2, 1, 1, 3, 3, 3, 3, 5]
def baseStart_7213263 : Nat := 118140960795 + 7213263 * 2 ^ 59
def prefixEnd_7213263 : Nat := 4983230072969 + 3 ^ 40 * 7213263 * 2
def baseEnd_7213263 : Nat := 1234623668764172269679771

theorem tailTrace_7213263 : CollatzResearch.WordTrace tailWord_7213263 prefixEnd_7213263 1234623668764172269679771 := by
  unfold tailWord_7213263
  simp only [CollatzResearch.WordTrace]
  refine ⟨263089315266587553086772443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175392876844391702057848295 263089315266587553086772443)
  ·
    refine ⟨394633972899881329630158665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263089315266587553086772443 394633972899881329630158665)
    ·
      refine ⟨295975479674910997222618999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 394633972899881329630158665 295975479674910997222618999)
      ·
        refine ⟨443963219512366495833928499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 295975479674910997222618999 443963219512366495833928499)
        ·
          refine ⟨665944829268549743750892749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 443963219512366495833928499 665944829268549743750892749)
          ·
            refine ⟨249729310975706153906584781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 665944829268549743750892749 249729310975706153906584781)
            ·
              refine ⟨93648491615889807714969293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 249729310975706153906584781 93648491615889807714969293)
              ·
                refine ⟨35118184355958677893113485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 93648491615889807714969293 35118184355958677893113485)
                ·
                  refine ⟨13169319133484504209917557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35118184355958677893113485 13169319133484504209917557)
                  ·
                    refine ⟨1234623668764172269679771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13169319133484504209917557 1234623668764172269679771)
                    ·
                      rfl

theorem cell23_7213263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 3, 3, 5].length) (baseStart_7213263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7213263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7213263 prefixEnd_7213263 := by exact prefixLift 7213263
  have htrace : WordTrace (prefixWord ++ tailWord_7213263) baseStart_7213263 baseEnd_7213263 := by
    simpa [prefixWord, tailWord_7213263, baseEnd_7213263] using wordTrace_append hprefix tailTrace_7213263
  have hstable : (prefixWord ++ tailWord_7213263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7213263).length < 2 ^ (prefixWord ++ tailWord_7213263).sum := by decide
  have hdescent : baseEnd_7213263 < baseStart_7213263 := by decide
  rcases family_descends (prefixWord ++ tailWord_7213263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7213280 : List Nat := [2, 1, 1, 3, 1, 3, 3, 3, 1, 5]
def baseStart_7213280 : Nat := 118140960795 + 7213280 * 2 ^ 59
def prefixEnd_7213280 : Nat := 4983230072969 + 3 ^ 40 * 7213280 * 2
def baseEnd_7213280 : Nat := 1234626578487881080842245

theorem tailTrace_7213280 : CollatzResearch.WordTrace tailWord_7213280 prefixEnd_7213280 1234626578487881080842245 := by
  unfold tailWord_7213280
  simp only [CollatzResearch.WordTrace]
  refine ⟨131544967653762982495070647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175393290205017309993427529 131544967653762982495070647)
  ·
    refine ⟨197317451480644473742605971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131544967653762982495070647 197317451480644473742605971)
    ·
      refine ⟨295976177220966710613908957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197317451480644473742605971 295976177220966710613908957)
      ·
        refine ⟨110991066457862516480215859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 295976177220966710613908957 110991066457862516480215859)
        ·
          refine ⟨166486599686793774720323789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110991066457862516480215859 166486599686793774720323789)
          ·
            refine ⟨62432474882547665520121421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 166486599686793774720323789 62432474882547665520121421)
            ·
              refine ⟨23412178080955374570045533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62432474882547665520121421 23412178080955374570045533)
              ·
                refine ⟨8779566780358265463767075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23412178080955374570045533 8779566780358265463767075)
                ·
                  refine ⟨13169350170537398195650613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8779566780358265463767075 13169350170537398195650613)
                  ·
                    refine ⟨1234626578487881080842245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13169350170537398195650613 1234626578487881080842245)
                    ·
                      rfl

theorem cell23_7213280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 3, 3, 1, 5].length) (baseStart_7213280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7213280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7213280 prefixEnd_7213280 := by exact prefixLift 7213280
  have htrace : WordTrace (prefixWord ++ tailWord_7213280) baseStart_7213280 baseEnd_7213280 := by
    simpa [prefixWord, tailWord_7213280, baseEnd_7213280] using wordTrace_append hprefix tailTrace_7213280
  have hstable : (prefixWord ++ tailWord_7213280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7213280).length < 2 ^ (prefixWord ++ tailWord_7213280).sum := by decide
  have hdescent : baseEnd_7213280 < baseStart_7213280 := by decide
  rcases family_descends (prefixWord ++ tailWord_7213280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7213314 : List Nat := [3, 4, 1, 1, 2, 2, 2, 2, 1, 5]
def baseStart_7213314 : Nat := 118140960795 + 7213314 * 2 ^ 59
def prefixEnd_7213314 : Nat := 4983230072969 + 3 ^ 40 * 7213314 * 2
def baseEnd_7213314 : Nat := 1234632397935298703167193

theorem tailTrace_7213314 : CollatzResearch.WordTrace tailWord_7213314 prefixEnd_7213314 1234632397935298703167193 := by
  unfold tailWord_7213314
  simp only [CollatzResearch.WordTrace]
  refine ⟨65772793847350697199219749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175394116926268525864585997 65772793847350697199219749)
  ·
    refine ⟨12332398846378255724853703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 65772793847350697199219749 12332398846378255724853703)
    ·
      refine ⟨18498598269567383587280555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12332398846378255724853703 18498598269567383587280555)
      ·
        refine ⟨27747897404351075380920833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18498598269567383587280555 27747897404351075380920833)
        ·
          refine ⟨20810923053263306535690625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27747897404351075380920833 20810923053263306535690625)
          ·
            refine ⟨15608192289947479901767969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20810923053263306535690625 15608192289947479901767969)
            ·
              refine ⟨11706144217460609926325977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15608192289947479901767969 11706144217460609926325977)
              ·
                refine ⟨8779608163095457444744483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11706144217460609926325977 8779608163095457444744483)
                ·
                  refine ⟨13169412244643186167116725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8779608163095457444744483 13169412244643186167116725)
                  ·
                    refine ⟨1234632397935298703167193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13169412244643186167116725 1234632397935298703167193)
                    ·
                      rfl

theorem cell23_7213314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 2, 2, 1, 5].length) (baseStart_7213314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7213314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7213314 prefixEnd_7213314 := by exact prefixLift 7213314
  have htrace : WordTrace (prefixWord ++ tailWord_7213314) baseStart_7213314 baseEnd_7213314 := by
    simpa [prefixWord, tailWord_7213314, baseEnd_7213314] using wordTrace_append hprefix tailTrace_7213314
  have hstable : (prefixWord ++ tailWord_7213314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7213314).length < 2 ^ (prefixWord ++ tailWord_7213314).sum := by decide
  have hdescent : baseEnd_7213314 < baseStart_7213314 := by decide
  rcases family_descends (prefixWord ++ tailWord_7213314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7213317 : List Nat := [1, 3, 1, 1, 2, 1, 2, 3, 5, 2, 2]
def baseStart_7213317 : Nat := 118140960795 + 7213317 * 2 ^ 59
def prefixEnd_7213317 : Nat := 4983230072969 + 3 ^ 40 * 7213317 * 2
def baseEnd_7213317 : Nat := 3703898734247859597764065

theorem tailTrace_7213317 : CollatzResearch.WordTrace tailWord_7213317 prefixEnd_7213317 3703898734247859597764065 := by
  unfold tailWord_7213317
  simp only [CollatzResearch.WordTrace]
  refine ⟨263091284808391920309238205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175394189872261280206158803 263091284808391920309238205)
  ·
    refine ⟨98659231803146970115964327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 263091284808391920309238205 98659231803146970115964327)
    ·
      refine ⟨147988847704720455173946491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98659231803146970115964327 147988847704720455173946491)
      ·
        refine ⟨221983271557080682760919737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147988847704720455173946491 221983271557080682760919737)
        ·
          refine ⟨166487453667810512070689803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 221983271557080682760919737 166487453667810512070689803)
          ·
            refine ⟨249731180501715768106034705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 166487453667810512070689803 249731180501715768106034705)
            ·
              refine ⟨187298385376286826079526029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 249731180501715768106034705 187298385376286826079526029)
              ·
                refine ⟨70236894516107559779822261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 187298385376286826079526029 70236894516107559779822261)
                ·
                  refine ⟨6584708860885083729358337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 70236894516107559779822261 6584708860885083729358337)
                  ·
                    refine ⟨4938531645663812797018753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6584708860885083729358337 4938531645663812797018753)
                    ·
                      refine ⟨3703898734247859597764065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4938531645663812797018753 3703898734247859597764065)
                      ·
                        rfl

theorem cell23_7213317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 3, 5, 2, 2].length) (baseStart_7213317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7213317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7213317 prefixEnd_7213317 := by exact prefixLift 7213317
  have htrace : WordTrace (prefixWord ++ tailWord_7213317) baseStart_7213317 baseEnd_7213317 := by
    simpa [prefixWord, tailWord_7213317, baseEnd_7213317] using wordTrace_append hprefix tailTrace_7213317
  have hstable : (prefixWord ++ tailWord_7213317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7213317).length < 2 ^ (prefixWord ++ tailWord_7213317).sum := by decide
  have hdescent : baseEnd_7213317 < baseStart_7213317 := by decide
  rcases family_descends (prefixWord ++ tailWord_7213317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7213323 : List Nat := [1, 1, 1, 1, 5, 2, 3, 9]
def baseStart_7213323 : Nat := 118140960795 + 7213323 * 2 ^ 59
def prefixEnd_7213323 : Nat := 4983230072969 + 3 ^ 40 * 7213323 * 2
def baseEnd_7213323 : Nat := 137181548708584687936631

theorem tailTrace_7213323 : CollatzResearch.WordTrace tailWord_7213323 prefixEnd_7213323 137181548708584687936631 := by
  unfold tailWord_7213323
  simp only [CollatzResearch.WordTrace]
  refine ⟨263091503646370183333956623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175394335764246788889304415 263091503646370183333956623)
  ·
    refine ⟨394637255469555275000934935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263091503646370183333956623 394637255469555275000934935)
    ·
      refine ⟨591955883204332912501402403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 394637255469555275000934935 591955883204332912501402403)
      ·
        refine ⟨887933824806499368752103605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 591955883204332912501402403 887933824806499368752103605)
        ·
          refine ⟨83243796075609315820509713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 887933824806499368752103605 83243796075609315820509713)
          ·
            refine ⟨62432847056706986865382285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83243796075609315820509713 62432847056706986865382285)
            ·
              refine ⟨23412317646265120074518357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62432847056706986865382285 23412317646265120074518357)
              ·
                refine ⟨137181548708584687936631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 23412317646265120074518357 137181548708584687936631)
                ·
                  rfl

theorem cell23_7213323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 3, 9].length) (baseStart_7213323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7213323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7213323 prefixEnd_7213323 := by exact prefixLift 7213323
  have htrace : WordTrace (prefixWord ++ tailWord_7213323) baseStart_7213323 baseEnd_7213323 := by
    simpa [prefixWord, tailWord_7213323, baseEnd_7213323] using wordTrace_append hprefix tailTrace_7213323
  have hstable : (prefixWord ++ tailWord_7213323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7213323).length < 2 ^ (prefixWord ++ tailWord_7213323).sum := by decide
  have hdescent : baseEnd_7213323 < baseStart_7213323 := by decide
  rcases family_descends (prefixWord ++ tailWord_7213323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7213361 : List Nat := [1, 2, 2, 3, 4, 2, 2, 1, 2, 4]
def baseStart_7213361 : Nat := 118140960795 + 7213361 * 2 ^ 59
def prefixEnd_7213361 : Nat := 4983230072969 + 3 ^ 40 * 7213361 * 2
def baseEnd_7213361 : Nat := 1234640442465552475204621

theorem tailTrace_7213361 : CollatzResearch.WordTrace tailWord_7213361 prefixEnd_7213361 1234640442465552475204621 := by
  unfold tailWord_7213361
  simp only [CollatzResearch.WordTrace]
  refine ⟨263092889620232515823839937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175395259746821677215893291 263092889620232515823839937)
  ·
    refine ⟨197319667215174386867879953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 263092889620232515823839937 197319667215174386867879953)
    ·
      refine ⟨147989750411380790150909965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 197319667215174386867879953 147989750411380790150909965)
      ·
        refine ⟨55496156404267796306591237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 147989750411380790150909965 55496156404267796306591237)
        ·
          refine ⟨10405529325800211807485857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55496156404267796306591237 10405529325800211807485857)
          ·
            refine ⟨7804146994350158855614393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10405529325800211807485857 7804146994350158855614393)
            ·
              refine ⟨5853110245762619141710795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7804146994350158855614393 5853110245762619141710795)
              ·
                refine ⟨8779665368643928712566193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5853110245762619141710795 8779665368643928712566193)
                ·
                  refine ⟨6584749026482946534424645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8779665368643928712566193 6584749026482946534424645)
                  ·
                    refine ⟨1234640442465552475204621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6584749026482946534424645 1234640442465552475204621)
                    ·
                      rfl

theorem cell23_7213361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 2, 2, 1, 2, 4].length) (baseStart_7213361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7213361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7213361 prefixEnd_7213361 := by exact prefixLift 7213361
  have htrace : WordTrace (prefixWord ++ tailWord_7213361) baseStart_7213361 baseEnd_7213361 := by
    simpa [prefixWord, tailWord_7213361, baseEnd_7213361] using wordTrace_append hprefix tailTrace_7213361
  have hstable : (prefixWord ++ tailWord_7213361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7213361).length < 2 ^ (prefixWord ++ tailWord_7213361).sum := by decide
  have hdescent : baseEnd_7213361 < baseStart_7213361 := by decide
  rcases family_descends (prefixWord ++ tailWord_7213361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7213394 : List Nat := [3, 2, 2, 1, 1, 1, 2, 5, 1, 3, 2]
def baseStart_7213394 : Nat := 118140960795 + 7213394 * 2 ^ 59
def prefixEnd_7213394 : Nat := 4983230072969 + 3 ^ 40 * 7213394 * 2
def baseEnd_7213394 : Nat := 3703938272258255796501211

theorem tailTrace_7213394 : CollatzResearch.WordTrace tailWord_7213394 prefixEnd_7213394 3703938272258255796501211 := by
  unfold tailWord_7213394
  simp only [CollatzResearch.WordTrace]
  refine ⟨65773523307278240614947809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175396062152741974973194157 65773523307278240614947809)
  ·
    refine ⟨49330142480458680461210857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65773523307278240614947809 49330142480458680461210857)
    ·
      refine ⟨36997606860344010345908143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49330142480458680461210857 36997606860344010345908143)
      ·
        refine ⟨55496410290516015518862215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36997606860344010345908143 55496410290516015518862215)
        ·
          refine ⟨83244615435774023278293323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55496410290516015518862215 83244615435774023278293323)
          ·
            refine ⟨124866923153661034917439985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83244615435774023278293323 124866923153661034917439985)
            ·
              refine ⟨93650192365245776188079989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 124866923153661034917439985 93650192365245776188079989)
              ·
                refine ⟨8779705534241791517632499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 93650192365245776188079989 8779705534241791517632499)
                ·
                  refine ⟨13169558301362687276448749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8779705534241791517632499 13169558301362687276448749)
                  ·
                    refine ⟨4938584363011007728668281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13169558301362687276448749 4938584363011007728668281)
                    ·
                      refine ⟨3703938272258255796501211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4938584363011007728668281 3703938272258255796501211)
                      ·
                        rfl

theorem cell23_7213394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 5, 1, 3, 2].length) (baseStart_7213394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7213394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7213394 prefixEnd_7213394 := by exact prefixLift 7213394
  have htrace : WordTrace (prefixWord ++ tailWord_7213394) baseStart_7213394 baseEnd_7213394 := by
    simpa [prefixWord, tailWord_7213394, baseEnd_7213394] using wordTrace_append hprefix tailTrace_7213394
  have hstable : (prefixWord ++ tailWord_7213394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7213394).length < 2 ^ (prefixWord ++ tailWord_7213394).sum := by decide
  have hdescent : baseEnd_7213394 < baseStart_7213394 := by decide
  rcases family_descends (prefixWord ++ tailWord_7213394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7213424 : List Nat := [2, 1, 1, 1, 4, 4, 2, 1, 1, 4, 2]
def baseStart_7213424 : Nat := 118140960795 + 7213424 * 2 ^ 59
def prefixEnd_7213424 : Nat := 4983230072969 + 3 ^ 40 * 7213424 * 2
def baseEnd_7213424 : Nat := 3703953676677890679126073

theorem tailTrace_7213424 : CollatzResearch.WordTrace tailWord_7213424 prefixEnd_7213424 3703953676677890679126073 := by
  unfold tailWord_7213424
  simp only [CollatzResearch.WordTrace]
  refine ⟨131547593709502138791691663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175396791612669518388922217 131547593709502138791691663)
  ·
    refine ⟨197321390564253208187537495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131547593709502138791691663 197321390564253208187537495)
    ·
      refine ⟨295982085846379812281306243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197321390564253208187537495 295982085846379812281306243)
      ·
        refine ⟨443973128769569718421959365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 295982085846379812281306243 443973128769569718421959365)
        ·
          refine ⟨83244961644294322204117381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 443973128769569718421959365 83244961644294322204117381)
          ·
            refine ⟨15608430308305185413272009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 83244961644294322204117381 15608430308305185413272009)
            ·
              refine ⟨11706322731228889059954007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15608430308305185413272009 11706322731228889059954007)
              ·
                refine ⟨17559484096843333589931011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11706322731228889059954007 17559484096843333589931011)
                ·
                  refine ⟨26339226145265000384896517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17559484096843333589931011 26339226145265000384896517)
                  ·
                    refine ⟨4938604902237187572168097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26339226145265000384896517 4938604902237187572168097)
                    ·
                      refine ⟨3703953676677890679126073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4938604902237187572168097 3703953676677890679126073)
                      ·
                        rfl

theorem cell23_7213424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 2, 1, 1, 4, 2].length) (baseStart_7213424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7213424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7213424 prefixEnd_7213424 := by exact prefixLift 7213424
  have htrace : WordTrace (prefixWord ++ tailWord_7213424) baseStart_7213424 baseEnd_7213424 := by
    simpa [prefixWord, tailWord_7213424, baseEnd_7213424] using wordTrace_append hprefix tailTrace_7213424
  have hstable : (prefixWord ++ tailWord_7213424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7213424).length < 2 ^ (prefixWord ++ tailWord_7213424).sum := by decide
  have hdescent : baseEnd_7213424 < baseStart_7213424 := by decide
  rcases family_descends (prefixWord ++ tailWord_7213424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7213464 : List Nat := [2, 1, 2, 5, 1, 1, 2, 4, 5]
def baseStart_7213464 : Nat := 118140960795 + 7213464 * 2 ^ 59
def prefixEnd_7213464 : Nat := 4983230072969 + 3 ^ 40 * 7213464 * 2
def baseEnd_7213464 : Nat := 411552690656007835847321

theorem tailTrace_7213464 : CollatzResearch.WordTrace tailWord_7213464 prefixEnd_7213464 411552690656007835847321 := by
  unfold tailWord_7213464
  simp only [CollatzResearch.WordTrace]
  refine ⟨131548323169429682207419723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175397764225906242943226297 131548323169429682207419723)
  ·
    refine ⟨197322484754144523311129585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131548323169429682207419723 197322484754144523311129585)
    ·
      refine ⟨147991863565608392483347189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 197322484754144523311129585 147991863565608392483347189)
      ·
        refine ⟨13874237209275786795313799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 147991863565608392483347189 13874237209275786795313799)
        ·
          refine ⟨20811355813913680192970699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13874237209275786795313799 20811355813913680192970699)
          ·
            refine ⟨31217033720870520289456049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20811355813913680192970699 31217033720870520289456049)
            ·
              refine ⟨23412775290652890217092037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31217033720870520289456049 23412775290652890217092037)
              ·
                refine ⟨4389895366997416915704757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23412775290652890217092037 4389895366997416915704757)
                ·
                  refine ⟨411552690656007835847321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4389895366997416915704757 411552690656007835847321)
                  ·
                    rfl

theorem cell23_7213464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 2, 4, 5].length) (baseStart_7213464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7213464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7213464 prefixEnd_7213464 := by exact prefixLift 7213464
  have htrace : WordTrace (prefixWord ++ tailWord_7213464) baseStart_7213464 baseEnd_7213464 := by
    simpa [prefixWord, tailWord_7213464, baseEnd_7213464] using wordTrace_append hprefix tailTrace_7213464
  have hstable : (prefixWord ++ tailWord_7213464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7213464).length < 2 ^ (prefixWord ++ tailWord_7213464).sum := by decide
  have hdescent : baseEnd_7213464 < baseStart_7213464 := by decide
  rcases family_descends (prefixWord ++ tailWord_7213464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7213490 : List Nat := [3, 2, 1, 1, 1, 1, 3, 1, 2, 8]
def baseStart_7213490 : Nat := 118140960795 + 7213490 * 2 ^ 59
def prefixEnd_7213490 : Nat := 4983230072969 + 3 ^ 40 * 7213490 * 2
def baseEnd_7213490 : Nat := 1234662522133695806966923

theorem tailTrace_7213490 : CollatzResearch.WordTrace tailWord_7213490 prefixEnd_7213490 1234662522133695806966923 := by
  unfold tailWord_7213490
  simp only [CollatzResearch.WordTrace]
  refine ⟨65774398659191292713821481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175398396424510113903523949 65774398659191292713821481)
  ·
    refine ⟨49330798994393469535366111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65774398659191292713821481 49330798994393469535366111)
    ·
      refine ⟨73996198491590204303049167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49330798994393469535366111 73996198491590204303049167)
      ·
        refine ⟨110994297737385306454573751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73996198491590204303049167 110994297737385306454573751)
        ·
          refine ⟨166491446606077959681860627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110994297737385306454573751 166491446606077959681860627)
          ·
            refine ⟨249737169909116939522790941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 166491446606077959681860627 249737169909116939522790941)
            ·
              refine ⟨93651438715918852321046603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 249737169909116939522790941 93651438715918852321046603)
              ·
                refine ⟨140477158073878278481569905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 93651438715918852321046603 140477158073878278481569905)
                ·
                  refine ⟨105357868555408708861177429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 140477158073878278481569905 105357868555408708861177429)
                  ·
                    refine ⟨1234662522133695806966923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 105357868555408708861177429 1234662522133695806966923)
                    ·
                      rfl

theorem cell23_7213490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 1, 2, 8].length) (baseStart_7213490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7213490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7213490 prefixEnd_7213490 := by exact prefixLift 7213490
  have htrace : WordTrace (prefixWord ++ tailWord_7213490) baseStart_7213490 baseEnd_7213490 := by
    simpa [prefixWord, tailWord_7213490, baseEnd_7213490] using wordTrace_append hprefix tailTrace_7213490
  have hstable : (prefixWord ++ tailWord_7213490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7213490).length < 2 ^ (prefixWord ++ tailWord_7213490).sum := by decide
  have hdescent : baseEnd_7213490 < baseStart_7213490 := by decide
  rcases family_descends (prefixWord ++ tailWord_7213490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7213497 : List Nat := [1, 2, 1, 4, 3, 1, 2, 1, 1, 3, 4]
def baseStart_7213497 : Nat := 118140960795 + 7213497 * 2 ^ 59
def prefixEnd_7213497 : Nat := 4983230072969 + 3 ^ 40 * 7213497 * 2
def baseEnd_7213497 : Nat := 3703991160765668893513237

theorem tailTrace_7213497 : CollatzResearch.WordTrace tailWord_7213497 prefixEnd_7213497 3703991160765668893513237 := by
  unfold tailWord_7213497
  simp only [CollatzResearch.WordTrace]
  refine ⟨263097849947739811050790745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175398566631826540700527163 263097849947739811050790745)
  ·
    refine ⟨197323387460804858288093059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 263097849947739811050790745 197323387460804858288093059)
    ·
      refine ⟨295985081191207287432139589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197323387460804858288093059 295985081191207287432139589)
      ·
        refine ⟨55497202723351366393526173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 295985081191207287432139589 55497202723351366393526173)
        ·
          refine ⟨20811451021256762397572315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55497202723351366393526173 20811451021256762397572315)
          ·
            refine ⟨31217176531885143596358473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20811451021256762397572315 31217176531885143596358473)
            ·
              refine ⟨23412882398913857697268855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31217176531885143596358473 23412882398913857697268855)
              ·
                refine ⟨35119323598370786545903283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23412882398913857697268855 35119323598370786545903283)
                ·
                  refine ⟨52678985397556179818854925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35119323598370786545903283 52678985397556179818854925)
                  ·
                    refine ⟨19754619524083567432070597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 52678985397556179818854925 19754619524083567432070597)
                    ·
                      refine ⟨3703991160765668893513237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19754619524083567432070597 3703991160765668893513237)
                      ·
                        rfl

theorem cell23_7213497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 2, 1, 1, 3, 4].length) (baseStart_7213497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7213497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7213497 prefixEnd_7213497 := by exact prefixLift 7213497
  have htrace : WordTrace (prefixWord ++ tailWord_7213497) baseStart_7213497 baseEnd_7213497 := by
    simpa [prefixWord, tailWord_7213497, baseEnd_7213497] using wordTrace_append hprefix tailTrace_7213497
  have hstable : (prefixWord ++ tailWord_7213497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7213497).length < 2 ^ (prefixWord ++ tailWord_7213497).sum := by decide
  have hdescent : baseEnd_7213497 < baseStart_7213497 := by decide
  rcases family_descends (prefixWord ++ tailWord_7213497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7213537 : List Nat := [1, 2, 3, 1, 2, 2, 3, 3, 6]
def baseStart_7213537 : Nat := 118140960795 + 7213537 * 2 ^ 59
def prefixEnd_7213537 : Nat := 4983230072969 + 3 ^ 40 * 7213537 * 2
def baseEnd_7213537 : Nat := 411556855554649859668117

theorem tailTrace_7213537 : CollatzResearch.WordTrace tailWord_7213537 prefixEnd_7213537 411556855554649859668117 := by
  unfold tailWord_7213537
  simp only [CollatzResearch.WordTrace]
  refine ⟨263099308867594897882246865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175399539245063265254831243 263099308867594897882246865)
  ·
    refine ⟨197324481650696173411685149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 263099308867594897882246865 197324481650696173411685149)
    ·
      refine ⟨73996680619011065029381931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 197324481650696173411685149 73996680619011065029381931)
      ·
        refine ⟨110995020928516597544072897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73996680619011065029381931 110995020928516597544072897)
        ·
          refine ⟨83246265696387448158054673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110995020928516597544072897 83246265696387448158054673)
          ·
            refine ⟨62434699272290586118541005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83246265696387448158054673 62434699272290586118541005)
            ·
              refine ⟨23413012227108969794452877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62434699272290586118541005 23413012227108969794452877)
              ·
                refine ⟨8779879585165863672919829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23413012227108969794452877 8779879585165863672919829)
                ·
                  refine ⟨411556855554649859668117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8779879585165863672919829 411556855554649859668117)
                  ·
                    rfl

theorem cell23_7213537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 3, 3, 6].length) (baseStart_7213537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7213537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7213537 prefixEnd_7213537 := by exact prefixLift 7213537
  have htrace : WordTrace (prefixWord ++ tailWord_7213537) baseStart_7213537 baseEnd_7213537 := by
    simpa [prefixWord, tailWord_7213537, baseEnd_7213537] using wordTrace_append hprefix tailTrace_7213537
  have hstable : (prefixWord ++ tailWord_7213537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7213537).length < 2 ^ (prefixWord ++ tailWord_7213537).sum := by decide
  have hdescent : baseEnd_7213537 < baseStart_7213537 := by decide
  rcases family_descends (prefixWord ++ tailWord_7213537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7213575 : List Nat := [1, 1, 4, 3, 3, 2, 2, 2, 1, 4]
def baseStart_7213575 : Nat := 118140960795 + 7213575 * 2 ^ 59
def prefixEnd_7213575 : Nat := 4983230072969 + 3 ^ 40 * 7213575 * 2
def baseEnd_7213575 : Nat := 1234677070752239862779293

theorem tailTrace_7213575 : CollatzResearch.WordTrace tailWord_7213575 prefixEnd_7213575 1234677070752239862779293 := by
  unfold tailWord_7213575
  simp only [CollatzResearch.WordTrace]
  refine ⟨263100694841457230372130179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175400463227638153581420119 263100694841457230372130179)
  ·
    refine ⟨394651042262185845558195269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263100694841457230372130179 394651042262185845558195269)
    ·
      refine ⟨73997070424159846042161613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 394651042262185845558195269 73997070424159846042161613)
      ·
        refine ⟨27748901409059942265810605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73997070424159846042161613 27748901409059942265810605)
        ·
          refine ⟨10405838028397478349678977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27748901409059942265810605 10405838028397478349678977)
          ·
            refine ⟨7804378521298108762259233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10405838028397478349678977 7804378521298108762259233)
            ·
              refine ⟨5853283890973581571694425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7804378521298108762259233 5853283890973581571694425)
              ·
                refine ⟨4389962918230186178770819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5853283890973581571694425 4389962918230186178770819)
                ·
                  refine ⟨6584944377345279268156229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4389962918230186178770819 6584944377345279268156229)
                  ·
                    refine ⟨1234677070752239862779293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6584944377345279268156229 1234677070752239862779293)
                    ·
                      rfl

theorem cell23_7213575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 2, 2, 2, 1, 4].length) (baseStart_7213575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7213575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7213575 prefixEnd_7213575 := by exact prefixLift 7213575
  have htrace : WordTrace (prefixWord ++ tailWord_7213575) baseStart_7213575 baseEnd_7213575 := by
    simpa [prefixWord, tailWord_7213575, baseEnd_7213575] using wordTrace_append hprefix tailTrace_7213575
  have hstable : (prefixWord ++ tailWord_7213575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7213575).length < 2 ^ (prefixWord ++ tailWord_7213575).sum := by decide
  have hdescent : baseEnd_7213575 < baseStart_7213575 := by decide
  rcases family_descends (prefixWord ++ tailWord_7213575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7213587 : List Nat := [1, 1, 1, 2, 1, 5, 1, 1, 5, 1, 4]
def baseStart_7213587 : Nat := 118140960795 + 7213587 * 2 ^ 59
def prefixEnd_7213587 : Nat := 4983230072969 + 3 ^ 40 * 7213587 * 2
def baseEnd_7213587 : Nat := 3704037374024573541387823

theorem tailTrace_7213587 : CollatzResearch.WordTrace tailWord_7213587 prefixEnd_7213587 3704037374024573541387823 := by
  unfold tailWord_7213587
  simp only [CollatzResearch.WordTrace]
  refine ⟨263101132517413756421567015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175400755011609170947711343 263101132517413756421567015)
  ·
    refine ⟨394651698776120634632350523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263101132517413756421567015 394651698776120634632350523)
    ·
      refine ⟨591977548164180951948525785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 394651698776120634632350523 591977548164180951948525785)
      ·
        refine ⟨443983161123135713961394339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 591977548164180951948525785 443983161123135713961394339)
        ·
          refine ⟨665974741684703570942091509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 443983161123135713961394339 665974741684703570942091509)
          ·
            refine ⟨62435132032940959775821079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 665974741684703570942091509 62435132032940959775821079)
            ·
              refine ⟨93652698049411439663731619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62435132032940959775821079 93652698049411439663731619)
              ·
                refine ⟨140479047074117159495597429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 93652698049411439663731619 140479047074117159495597429)
                ·
                  refine ⟨13169910663198483702712259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 140479047074117159495597429 13169910663198483702712259)
                  ·
                    refine ⟨19754865994797725554068389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13169910663198483702712259 19754865994797725554068389)
                    ·
                      refine ⟨3704037374024573541387823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19754865994797725554068389 3704037374024573541387823)
                      ·
                        rfl

theorem cell23_7213587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 1, 5, 1, 4].length) (baseStart_7213587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7213587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7213587 prefixEnd_7213587 := by exact prefixLift 7213587
  have htrace : WordTrace (prefixWord ++ tailWord_7213587) baseStart_7213587 baseEnd_7213587 := by
    simpa [prefixWord, tailWord_7213587, baseEnd_7213587] using wordTrace_append hprefix tailTrace_7213587
  have hstable : (prefixWord ++ tailWord_7213587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7213587).length < 2 ^ (prefixWord ++ tailWord_7213587).sum := by decide
  have hdescent : baseEnd_7213587 < baseStart_7213587 := by decide
  rcases family_descends (prefixWord ++ tailWord_7213587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7213608 : List Nat := [2, 1, 5, 2, 1, 1, 3, 1, 2, 3, 2]
def baseStart_7213608 : Nat := 118140960795 + 7213608 * 2 ^ 59
def prefixEnd_7213608 : Nat := 4983230072969 + 3 ^ 40 * 7213608 * 2
def baseEnd_7213608 : Nat := 3704048157118317959225227

theorem tailTrace_7213608 : CollatzResearch.WordTrace tailWord_7213608 prefixEnd_7213608 3704048157118317959225227 := by
  unfold tailWord_7213608
  simp only [CollatzResearch.WordTrace]
  refine ⟨131550949225168838504040739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175401265633558451338720985 131550949225168838504040739)
  ·
    refine ⟨197326423837753257756061109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131550949225168838504040739 197326423837753257756061109)
    ·
      refine ⟨18499352234789367914630729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 197326423837753257756061109 18499352234789367914630729)
      ·
        refine ⟨13874514176092025935973047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18499352234789367914630729 13874514176092025935973047)
        ·
          refine ⟨20811771264138038903959571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13874514176092025935973047 20811771264138038903959571)
          ·
            refine ⟨31217656896207058355939357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20811771264138038903959571 31217656896207058355939357)
            ·
              refine ⟨11706621336077646883477259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31217656896207058355939357 11706621336077646883477259)
              ·
                refine ⟨17559932004116470325215889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11706621336077646883477259 17559932004116470325215889)
                ·
                  refine ⟨13169949003087352743911917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17559932004116470325215889 13169949003087352743911917)
                  ·
                    refine ⟨4938730876157757278966969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13169949003087352743911917 4938730876157757278966969)
                    ·
                      refine ⟨3704048157118317959225227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4938730876157757278966969 3704048157118317959225227)
                      ·
                        rfl

theorem cell23_7213608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 3, 1, 2, 3, 2].length) (baseStart_7213608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7213608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7213608 prefixEnd_7213608 := by exact prefixLift 7213608
  have htrace : WordTrace (prefixWord ++ tailWord_7213608) baseStart_7213608 baseEnd_7213608 := by
    simpa [prefixWord, tailWord_7213608, baseEnd_7213608] using wordTrace_append hprefix tailTrace_7213608
  have hstable : (prefixWord ++ tailWord_7213608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7213608).length < 2 ^ (prefixWord ++ tailWord_7213608).sum := by decide
  have hdescent : baseEnd_7213608 < baseStart_7213608 := by decide
  rcases family_descends (prefixWord ++ tailWord_7213608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7213621 : List Nat := [1, 3, 3, 1, 1, 2, 1, 2, 5, 2, 2]
def baseStart_7213621 : Nat := 118140960795 + 7213621 * 2 ^ 59
def prefixEnd_7213621 : Nat := 4983230072969 + 3 ^ 40 * 7213621 * 2
def baseEnd_7213621 : Nat := 3704054832366826408362667

theorem tailTrace_7213621 : CollatzResearch.WordTrace tailWord_7213621 prefixEnd_7213621 3704054832366826408362667 := by
  unfold tailWord_7213621
  simp only [CollatzResearch.WordTrace]
  refine ⟨263102372599290580228304717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175401581732860386818869811 263102372599290580228304717)
  ·
    refine ⟨98663389724733967585614269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 263102372599290580228304717 98663389724733967585614269)
    ·
      refine ⟨36998771146775237844605351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98663389724733967585614269 36998771146775237844605351)
      ·
        refine ⟨55498156720162856766908027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36998771146775237844605351 55498156720162856766908027)
        ·
          refine ⟨83247235080244285150362041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55498156720162856766908027 83247235080244285150362041)
          ·
            refine ⟨62435426310183213862771531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83247235080244285150362041 62435426310183213862771531)
            ·
              refine ⟨93653139465274820794157297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62435426310183213862771531 93653139465274820794157297)
              ·
                refine ⟨70239854598956115595617973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 93653139465274820794157297 70239854598956115595617973)
                ·
                  refine ⟨6584986368652135837089185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 70239854598956115595617973 6584986368652135837089185)
                  ·
                    refine ⟨4938739776489101877816889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6584986368652135837089185 4938739776489101877816889)
                    ·
                      refine ⟨3704054832366826408362667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4938739776489101877816889 3704054832366826408362667)
                      ·
                        rfl

theorem cell23_7213621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 2, 5, 2, 2].length) (baseStart_7213621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7213621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7213621 prefixEnd_7213621 := by exact prefixLift 7213621
  have htrace : WordTrace (prefixWord ++ tailWord_7213621) baseStart_7213621 baseEnd_7213621 := by
    simpa [prefixWord, tailWord_7213621, baseEnd_7213621] using wordTrace_append hprefix tailTrace_7213621
  have hstable : (prefixWord ++ tailWord_7213621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7213621).length < 2 ^ (prefixWord ++ tailWord_7213621).sum := by decide
  have hdescent : baseEnd_7213621 < baseStart_7213621 := by decide
  rcases family_descends (prefixWord ++ tailWord_7213621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7213667 : List Nat := [1, 1, 1, 5, 1, 2, 1, 1, 1, 4, 5]
def baseStart_7213667 : Nat := 118140960795 + 7213667 * 2 ^ 59
def prefixEnd_7213667 : Nat := 4983230072969 + 3 ^ 40 * 7213667 * 2
def baseEnd_7213667 : Nat := 3704078452476933228387455

theorem tailTrace_7213667 : CollatzResearch.WordTrace tailWord_7213667 prefixEnd_7213667 3704078452476933228387455 := by
  unfold tailWord_7213667
  simp only [CollatzResearch.WordTrace]
  refine ⟨263104050357123930084479255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175402700238082620056319503 263104050357123930084479255)
  ·
    refine ⟨394656075535685895126718883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263104050357123930084479255 394656075535685895126718883)
    ·
      refine ⟨591984113303528842690078325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 394656075535685895126718883 591984113303528842690078325)
      ·
        refine ⟨55498510622205829002194843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 591984113303528842690078325 55498510622205829002194843)
        ·
          refine ⟨83247765933308743503292265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55498510622205829002194843 83247765933308743503292265)
          ·
            refine ⟨62435824449981557627469199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83247765933308743503292265 62435824449981557627469199)
            ·
              refine ⟨93653736674972336441203799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62435824449981557627469199 93653736674972336441203799)
              ·
                refine ⟨140480605012458504661805699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 93653736674972336441203799 140480605012458504661805699)
                ·
                  refine ⟨210720907518687756992708549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 140480605012458504661805699 210720907518687756992708549)
                  ·
                    refine ⟨39510170159753954436132853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 210720907518687756992708549 39510170159753954436132853)
                    ·
                      refine ⟨3704078452476933228387455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39510170159753954436132853 3704078452476933228387455)
                      ·
                        rfl

theorem cell23_7213667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 1, 1, 4, 5].length) (baseStart_7213667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7213667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7213667 prefixEnd_7213667 := by exact prefixLift 7213667
  have htrace : WordTrace (prefixWord ++ tailWord_7213667) baseStart_7213667 baseEnd_7213667 := by
    simpa [prefixWord, tailWord_7213667, baseEnd_7213667] using wordTrace_append hprefix tailTrace_7213667
  have hstable : (prefixWord ++ tailWord_7213667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7213667).length < 2 ^ (prefixWord ++ tailWord_7213667).sum := by decide
  have hdescent : baseEnd_7213667 < baseStart_7213667 := by decide
  rcases family_descends (prefixWord ++ tailWord_7213667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7213687 : List Nat := [1, 1, 3, 1, 1, 3, 2, 1, 4, 6]
def baseStart_7213687 : Nat := 118140960795 + 7213687 * 2 ^ 59
def prefixEnd_7213687 : Nat := 4983230072969 + 3 ^ 40 * 7213687 * 2
def baseEnd_7213687 : Nat := 1234696240696674383379121

theorem tailTrace_7213687 : CollatzResearch.WordTrace tailWord_7213687 prefixEnd_7213687 1234696240696674383379121 := by
  unfold tailWord_7213687
  simp only [CollatzResearch.WordTrace]
  refine ⟨263104779817051473500207315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175403186544700982333471543 263104779817051473500207315)
  ·
    refine ⟨394657169725577210250310973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263104779817051473500207315 394657169725577210250310973)
    ·
      refine ⟨147996438647091453843866615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 394657169725577210250310973 147996438647091453843866615)
      ·
        refine ⟨221994657970637180765799923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147996438647091453843866615 221994657970637180765799923)
        ·
          refine ⟨332991986955955771148699885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 221994657970637180765799923 332991986955955771148699885)
          ·
            refine ⟨124871995108483414180762457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 332991986955955771148699885 124871995108483414180762457)
            ·
              refine ⟨93653996331362560635571843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 124871995108483414180762457 93653996331362560635571843)
              ·
                refine ⟨140480994497043840953357765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 93653996331362560635571843 140480994497043840953357765)
                ·
                  refine ⟨26340186468195720178754581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 140480994497043840953357765 26340186468195720178754581)
                  ·
                    refine ⟨1234696240696674383379121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26340186468195720178754581 1234696240696674383379121)
                    ·
                      rfl

theorem cell23_7213687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 1, 4, 6].length) (baseStart_7213687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7213687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7213687 prefixEnd_7213687 := by exact prefixLift 7213687
  have htrace : WordTrace (prefixWord ++ tailWord_7213687) baseStart_7213687 baseEnd_7213687 := by
    simpa [prefixWord, tailWord_7213687, baseEnd_7213687] using wordTrace_append hprefix tailTrace_7213687
  have hstable : (prefixWord ++ tailWord_7213687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7213687).length < 2 ^ (prefixWord ++ tailWord_7213687).sum := by decide
  have hdescent : baseEnd_7213687 < baseStart_7213687 := by decide
  rcases family_descends (prefixWord ++ tailWord_7213687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7213728 : List Nat := [2, 1, 1, 4, 4, 1, 1, 2, 1, 4, 2]
def baseStart_7213728 : Nat := 118140960795 + 7213728 * 2 ^ 59
def prefixEnd_7213728 : Nat := 4983230072969 + 3 ^ 40 * 7213728 * 2
def baseEnd_7213728 : Nat := 3704109774796857489724675

theorem tailTrace_7213728 : CollatzResearch.WordTrace tailWord_7213728 prefixEnd_7213728 3704109774796857489724675 := by
  unfold tailWord_7213728
  simp only [CollatzResearch.WordTrace]
  refine ⟨131553137604951468751224919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175404183473268625001633225 131553137604951468751224919)
  ·
    refine ⟨197329706407427203126837379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131553137604951468751224919 197329706407427203126837379)
    ·
      refine ⟨295994559611140804690256069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197329706407427203126837379 295994559611140804690256069)
      ·
        refine ⟨55498979927088900879423013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 295994559611140804690256069 55498979927088900879423013)
        ·
          refine ⟨10406058736329168914891815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55498979927088900879423013 10406058736329168914891815)
          ·
            refine ⟨15609088104493753372337723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10406058736329168914891815 15609088104493753372337723)
            ·
              refine ⟨23413632156740630058506585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15609088104493753372337723 23413632156740630058506585)
              ·
                refine ⟨17560224117555472543879939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23413632156740630058506585 17560224117555472543879939)
                ·
                  refine ⟨26340336176333208815819909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17560224117555472543879939 26340336176333208815819909)
                  ·
                    refine ⟨4938813033062476652966233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26340336176333208815819909 4938813033062476652966233)
                    ·
                      refine ⟨3704109774796857489724675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4938813033062476652966233 3704109774796857489724675)
                      ·
                        rfl

theorem cell23_7213728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 1, 2, 1, 4, 2].length) (baseStart_7213728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7213728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7213728 prefixEnd_7213728 := by exact prefixLift 7213728
  have htrace : WordTrace (prefixWord ++ tailWord_7213728) baseStart_7213728 baseEnd_7213728 := by
    simpa [prefixWord, tailWord_7213728, baseEnd_7213728] using wordTrace_append hprefix tailTrace_7213728
  have hstable : (prefixWord ++ tailWord_7213728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7213728).length < 2 ^ (prefixWord ++ tailWord_7213728).sum := by decide
  have hdescent : baseEnd_7213728 < baseStart_7213728 := by decide
  rcases family_descends (prefixWord ++ tailWord_7213728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7213744 : List Nat := [2, 1, 1, 1, 2, 1, 3, 4, 2, 3, 3]
def baseStart_7213744 : Nat := 118140960795 + 7213744 * 2 ^ 59
def prefixEnd_7213744 : Nat := 4983230072969 + 3 ^ 40 * 7213744 * 2
def baseEnd_7213744 : Nat := 3704117990487329427124601

theorem tailTrace_7213744 : CollatzResearch.WordTrace tailWord_7213744 prefixEnd_7213744 3704117990487329427124601 := by
  unfold tailWord_7213744
  simp only [CollatzResearch.WordTrace]
  refine ⟨131553429388922486117516143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175404572518563314823354857 131553429388922486117516143)
  ·
    refine ⟨197330144083383729176274215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131553429388922486117516143 197330144083383729176274215)
    ·
      refine ⟨295995216125075593764411323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197330144083383729176274215 295995216125075593764411323)
      ·
        refine ⟨443992824187613390646616985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 295995216125075593764411323 443992824187613390646616985)
        ·
          refine ⟨332994618140710042984962739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 443992824187613390646616985 332994618140710042984962739)
          ·
            refine ⟨499491927211065064477444109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 332994618140710042984962739 499491927211065064477444109)
            ·
              refine ⟨187309472704149399179041541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 499491927211065064477444109 187309472704149399179041541)
              ·
                refine ⟨35120526132028012346070289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 187309472704149399179041541 35120526132028012346070289)
                ·
                  refine ⟨26340394599021009259552717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35120526132028012346070289 26340394599021009259552717)
                  ·
                    refine ⟨9877647974632878472332269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26340394599021009259552717 9877647974632878472332269)
                    ·
                      refine ⟨3704117990487329427124601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9877647974632878472332269 3704117990487329427124601)
                      ·
                        rfl

theorem cell23_7213744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 4, 2, 3, 3].length) (baseStart_7213744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7213744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7213744 prefixEnd_7213744 := by exact prefixLift 7213744
  have htrace : WordTrace (prefixWord ++ tailWord_7213744) baseStart_7213744 baseEnd_7213744 := by
    simpa [prefixWord, tailWord_7213744, baseEnd_7213744] using wordTrace_append hprefix tailTrace_7213744
  have hstable : (prefixWord ++ tailWord_7213744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7213744).length < 2 ^ (prefixWord ++ tailWord_7213744).sum := by decide
  have hdescent : baseEnd_7213744 < baseStart_7213744 := by decide
  rcases family_descends (prefixWord ++ tailWord_7213744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7213801 : List Nat := [1, 2, 1, 1, 1, 2, 5, 2, 2, 4, 2]
def baseStart_7213801 : Nat := 118140960795 + 7213801 * 2 ^ 59
def prefixEnd_7213801 : Nat := 4983230072969 + 3 ^ 40 * 7213801 * 2
def baseEnd_7213801 : Nat := 3704147258884635704111839

theorem tailTrace_7213801 : CollatzResearch.WordTrace tailWord_7213801 prefixEnd_7213801 3704147258884635704111839 := by
  unfold tailWord_7213801
  simp only [CollatzResearch.WordTrace]
  refine ⟨263108937738638470969857257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175405958492425647313238171 263108937738638470969857257)
  ·
    refine ⟨197331703303978853227392943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 263108937738638470969857257 197331703303978853227392943)
    ·
      refine ⟨295997554955968279841089415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197331703303978853227392943 295997554955968279841089415)
      ·
        refine ⟨443996332433952419761634123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 295997554955968279841089415 443996332433952419761634123)
        ·
          refine ⟨665994498650928629642451185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 443996332433952419761634123 665994498650928629642451185)
          ·
            refine ⟨499495873988196472231838389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 665994498650928629642451185 499495873988196472231838389)
            ·
              refine ⟨46827738186393419271734849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 499495873988196472231838389 46827738186393419271734849)
              ·
                refine ⟨35120803639795064453801137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46827738186393419271734849 35120803639795064453801137)
                ·
                  refine ⟨26340602729846298340350853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35120803639795064453801137 26340602729846298340350853)
                  ·
                    refine ⟨4938863011846180938815785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26340602729846298340350853 4938863011846180938815785)
                    ·
                      refine ⟨3704147258884635704111839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4938863011846180938815785 3704147258884635704111839)
                      ·
                        rfl

theorem cell23_7213801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 5, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 5, 2, 2, 4, 2].length) (baseStart_7213801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7213801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7213801 prefixEnd_7213801 := by exact prefixLift 7213801
  have htrace : WordTrace (prefixWord ++ tailWord_7213801) baseStart_7213801 baseEnd_7213801 := by
    simpa [prefixWord, tailWord_7213801, baseEnd_7213801] using wordTrace_append hprefix tailTrace_7213801
  have hstable : (prefixWord ++ tailWord_7213801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7213801).length < 2 ^ (prefixWord ++ tailWord_7213801).sum := by decide
  have hdescent : baseEnd_7213801 < baseStart_7213801 := by decide
  rcases family_descends (prefixWord ++ tailWord_7213801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7213891 : List Nat := [1, 1, 1, 3, 1, 4, 3, 1, 3, 1, 4]
def baseStart_7213891 : Nat := 118140960795 + 7213891 * 2 ^ 59
def prefixEnd_7213891 : Nat := 4983230072969 + 3 ^ 40 * 7213891 * 2
def baseEnd_7213891 : Nat := 3704193472143540351986425

theorem tailTrace_7213891 : CollatzResearch.WordTrace tailWord_7213891 prefixEnd_7213891 3704193472143540351986425 := by
  unfold tailWord_7213891
  simp only [CollatzResearch.WordTrace]
  refine ⟨263112220308312416340633527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175408146872208277560422351 263112220308312416340633527)
  ·
    refine ⟨394668330462468624510950291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263112220308312416340633527 394668330462468624510950291)
    ·
      refine ⟨592002495693702936766425437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 394668330462468624510950291 592002495693702936766425437)
      ·
        refine ⟨222000935885138601287409539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 592002495693702936766425437 222000935885138601287409539)
        ·
          refine ⟨333001403827707901931114309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 222000935885138601287409539 333001403827707901931114309)
          ·
            refine ⟨62437763217695231612083933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 333001403827707901931114309 62437763217695231612083933)
            ·
              refine ⟨23414161206635711854531475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62437763217695231612083933 23414161206635711854531475)
              ·
                refine ⟨35121241809953567781797213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23414161206635711854531475 35121241809953567781797213)
                ·
                  refine ⟨13170465678732587918173955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35121241809953567781797213 13170465678732587918173955)
                  ·
                    refine ⟨19755698518098881877260933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13170465678732587918173955 19755698518098881877260933)
                    ·
                      refine ⟨3704193472143540351986425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19755698518098881877260933 3704193472143540351986425)
                      ·
                        rfl

theorem cell23_7213891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 3, 1, 3, 1, 4].length) (baseStart_7213891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7213891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7213891 prefixEnd_7213891 := by exact prefixLift 7213891
  have htrace : WordTrace (prefixWord ++ tailWord_7213891) baseStart_7213891 baseEnd_7213891 := by
    simpa [prefixWord, tailWord_7213891, baseEnd_7213891] using wordTrace_append hprefix tailTrace_7213891
  have hstable : (prefixWord ++ tailWord_7213891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7213891).length < 2 ^ (prefixWord ++ tailWord_7213891).sum := by decide
  have hdescent : baseEnd_7213891 < baseStart_7213891 := by decide
  rcases family_descends (prefixWord ++ tailWord_7213891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7213905 : List Nat := [1, 2, 2, 1, 6, 1, 3, 1, 1, 5]
def baseStart_7213905 : Nat := 118140960795 + 7213905 * 2 ^ 59
def prefixEnd_7213905 : Nat := 4983230072969 + 3 ^ 40 * 7213905 * 2
def baseEnd_7213905 : Nat := 1234733553624234432403787

theorem tailTrace_7213905 : CollatzResearch.WordTrace tailWord_7213905 prefixEnd_7213905 1234733553624234432403787 := by
  unfold tailWord_7213905
  simp only [CollatzResearch.WordTrace]
  refine ⟨263112730930261696731643169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175408487286841131154428779 263112730930261696731643169)
  ·
    refine ⟨197334548197696272548732377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 263112730930261696731643169 197334548197696272548732377)
    ·
      refine ⟨148000911148272204411549283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 197334548197696272548732377 148000911148272204411549283)
      ·
        refine ⟨222001366722408306617323925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148000911148272204411549283 222001366722408306617323925)
        ·
          refine ⟨10406314065112889372687059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 222001366722408306617323925 10406314065112889372687059)
          ·
            refine ⟨15609471097669334059030589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10406314065112889372687059 15609471097669334059030589)
            ·
              refine ⟨5853551661626000272136471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15609471097669334059030589 5853551661626000272136471)
              ·
                refine ⟨8780327492439000408204707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5853551661626000272136471 8780327492439000408204707)
                ·
                  refine ⟨13170491238658500612307061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8780327492439000408204707 13170491238658500612307061)
                  ·
                    refine ⟨1234733553624234432403787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13170491238658500612307061 1234733553624234432403787)
                    ·
                      rfl

theorem cell23_7213905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 3, 1, 1, 5].length) (baseStart_7213905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7213905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7213905 prefixEnd_7213905 := by exact prefixLift 7213905
  have htrace : WordTrace (prefixWord ++ tailWord_7213905) baseStart_7213905 baseEnd_7213905 := by
    simpa [prefixWord, tailWord_7213905, baseEnd_7213905] using wordTrace_append hprefix tailTrace_7213905
  have hstable : (prefixWord ++ tailWord_7213905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7213905).length < 2 ^ (prefixWord ++ tailWord_7213905).sum := by decide
  have hdescent : baseEnd_7213905 < baseStart_7213905 := by decide
  rcases family_descends (prefixWord ++ tailWord_7213905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7213914 : List Nat := [3, 1, 1, 2, 1, 15]
def baseStart_7213914 : Nat := 118140960795 + 7213914 * 2 ^ 59
def prefixEnd_7213914 : Nat := 4983230072969 + 3 ^ 40 * 7213914 * 2
def baseEnd_7213914 : Nat := 15243643136619727415633

theorem tailTrace_7213914 : CollatzResearch.WordTrace tailWord_7213914 prefixEnd_7213914 15243643136619727415633 := by
  unfold tailWord_7213914
  simp only [CollatzResearch.WordTrace]
  refine ⟨65778264796807272817180199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175408706124819394179147197 65778264796807272817180199)
  ·
    refine ⟨98667397195210909225770299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65778264796807272817180199 98667397195210909225770299)
    ·
      refine ⟨148001095792816363838655449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98667397195210909225770299 148001095792816363838655449)
      ·
        refine ⟨111000821844612272878991587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148001095792816363838655449 111000821844612272878991587)
        ·
          refine ⟨166501232766918409318487381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111000821844612272878991587 166501232766918409318487381)
          ·
            refine ⟨15243643136619727415633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 15 166501232766918409318487381 15243643136619727415633)
            ·
              rfl

theorem cell23_7213914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 15].length) (baseStart_7213914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7213914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7213914 prefixEnd_7213914 := by exact prefixLift 7213914
  have htrace : WordTrace (prefixWord ++ tailWord_7213914) baseStart_7213914 baseEnd_7213914 := by
    simpa [prefixWord, tailWord_7213914, baseEnd_7213914] using wordTrace_append hprefix tailTrace_7213914
  have hstable : (prefixWord ++ tailWord_7213914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7213914).length < 2 ^ (prefixWord ++ tailWord_7213914).sum := by decide
  have hdescent : baseEnd_7213914 < baseStart_7213914 := by decide
  rcases family_descends (prefixWord ++ tailWord_7213914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7213928 : List Nat := [2, 1, 4, 2, 1, 2, 1, 2, 3, 2, 3]
def baseStart_7213928 : Nat := 118140960795 + 7213928 * 2 ^ 59
def prefixEnd_7213928 : Nat := 4983230072969 + 3 ^ 40 * 7213928 * 2
def baseEnd_7213928 : Nat := 3704212470927756707223755

theorem tailTrace_7213928 : CollatzResearch.WordTrace tailWord_7213928 prefixEnd_7213928 3704212470927756707223755 := by
  unfold tailWord_7213928
  simp only [CollatzResearch.WordTrace]
  refine ⟨131556784904589185829865219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175409046539452247773153625 131556784904589185829865219)
  ·
    refine ⟨197335177356883778744797829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131556784904589185829865219 197335177356883778744797829)
    ·
      refine ⟨37000345754415708514649593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 197335177356883778744797829 37000345754415708514649593)
      ·
        refine ⟨27750259315811781385987195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37000345754415708514649593 27750259315811781385987195)
        ·
          refine ⟨41625388973717672078980793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27750259315811781385987195 41625388973717672078980793)
          ·
            refine ⟨31219041730288254059235595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41625388973717672078980793 31219041730288254059235595)
            ·
              refine ⟨46828562595432381088853393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31219041730288254059235595 46828562595432381088853393)
              ·
                refine ⟨35121421946574285816640045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46828562595432381088853393 35121421946574285816640045)
                ·
                  refine ⟨13170533229965357181240017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35121421946574285816640045 13170533229965357181240017)
                  ·
                    refine ⟨9877899922474017885930013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13170533229965357181240017 9877899922474017885930013)
                    ·
                      refine ⟨3704212470927756707223755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9877899922474017885930013 3704212470927756707223755)
                      ·
                        rfl

theorem cell23_7213928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 1, 2, 3, 2, 3].length) (baseStart_7213928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7213928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7213928 prefixEnd_7213928 := by exact prefixLift 7213928
  have htrace : WordTrace (prefixWord ++ tailWord_7213928) baseStart_7213928 baseEnd_7213928 := by
    simpa [prefixWord, tailWord_7213928, baseEnd_7213928] using wordTrace_append hprefix tailTrace_7213928
  have hstable : (prefixWord ++ tailWord_7213928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7213928).length < 2 ^ (prefixWord ++ tailWord_7213928).sum := by decide
  have hdescent : baseEnd_7213928 < baseStart_7213928 := by decide
  rcases family_descends (prefixWord ++ tailWord_7213928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7213942 : List Nat := [5, 1, 1, 3, 1, 1, 1, 1, 5, 2, 2]
def baseStart_7213942 : Nat := 118140960795 + 7213942 * 2 ^ 59
def prefixEnd_7213942 : Nat := 4983230072969 + 3 ^ 40 * 7213942 * 2
def baseEnd_7213942 : Nat := 3704219659656919652448691

theorem tailTrace_7213942 : CollatzResearch.WordTrace tailWord_7213942 prefixEnd_7213942 3704219659656919652448691 := by
  unfold tailWord_7213942
  simp only [CollatzResearch.WordTrace]
  refine ⟨16444630026945478253171255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 175409386954085101367160053 16444630026945478253171255)
  ·
    refine ⟨24666945040418217379756883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16444630026945478253171255 24666945040418217379756883)
    ·
      refine ⟨37000417560627326069635325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24666945040418217379756883 37000417560627326069635325)
      ·
        refine ⟨13875156585235247276113247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37000417560627326069635325 13875156585235247276113247)
        ·
          refine ⟨20812734877852870914169871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13875156585235247276113247 20812734877852870914169871)
          ·
            refine ⟨31219102316779306371254807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20812734877852870914169871 31219102316779306371254807)
            ·
              refine ⟨46828653475168959556882211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31219102316779306371254807 46828653475168959556882211)
              ·
                refine ⟨70242980212753439335323317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46828653475168959556882211 70242980212753439335323317)
                ·
                  refine ⟨6585279394945634937686561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 70242980212753439335323317 6585279394945634937686561)
                  ·
                    refine ⟨4938959546209226203264921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6585279394945634937686561 4938959546209226203264921)
                    ·
                      refine ⟨3704219659656919652448691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4938959546209226203264921 3704219659656919652448691)
                      ·
                        rfl

theorem cell23_7213942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 1, 1, 5, 2, 2].length) (baseStart_7213942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7213942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7213942 prefixEnd_7213942 := by exact prefixLift 7213942
  have htrace : WordTrace (prefixWord ++ tailWord_7213942) baseStart_7213942 baseEnd_7213942 := by
    simpa [prefixWord, tailWord_7213942, baseEnd_7213942] using wordTrace_append hprefix tailTrace_7213942
  have hstable : (prefixWord ++ tailWord_7213942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7213942).length < 2 ^ (prefixWord ++ tailWord_7213942).sum := by decide
  have hdescent : baseEnd_7213942 < baseStart_7213942 := by decide
  rcases family_descends (prefixWord ++ tailWord_7213942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7213959 : List Nat := [1, 1, 4, 2, 3, 2, 2, 3, 1, 2, 2]
def baseStart_7213959 : Nat := 118140960795 + 7213959 * 2 ^ 59
def prefixEnd_7213959 : Nat := 4983230072969 + 3 ^ 40 * 7213959 * 2
def baseEnd_7213959 : Nat := 3704228388828046085936113

theorem tailTrace_7213959 : CollatzResearch.WordTrace tailWord_7213959 prefixEnd_7213959 3704228388828046085936113 := by
  unfold tailWord_7213959
  simp only [CollatzResearch.WordTrace]
  refine ⟨263114700472066063954108931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175409800314710709302739287 263114700472066063954108931)
  ·
    refine ⟨394672050708099095931163397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263114700472066063954108931 394672050708099095931163397)
    ·
      refine ⟨74001009507768580487093137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 394672050708099095931163397 74001009507768580487093137)
      ·
        refine ⟨55500757130826435365319853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74001009507768580487093137 55500757130826435365319853)
        ·
          refine ⟨20812783924059913261994945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55500757130826435365319853 20812783924059913261994945)
          ·
            refine ⟨15609587943044934946496209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20812783924059913261994945 15609587943044934946496209)
            ·
              refine ⟨11707190957283701209872157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15609587943044934946496209 11707190957283701209872157)
              ·
                refine ⟨4390196608981387953702059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11707190957283701209872157 4390196608981387953702059)
                ·
                  refine ⟨6585294913472081930553089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4390196608981387953702059 6585294913472081930553089)
                  ·
                    refine ⟨4938971185104061447914817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6585294913472081930553089 4938971185104061447914817)
                    ·
                      refine ⟨3704228388828046085936113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4938971185104061447914817 3704228388828046085936113)
                      ·
                        rfl

theorem cell23_7213959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 2, 3, 1, 2, 2].length) (baseStart_7213959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7213959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7213959 prefixEnd_7213959 := by exact prefixLift 7213959
  have htrace : WordTrace (prefixWord ++ tailWord_7213959) baseStart_7213959 baseEnd_7213959 := by
    simpa [prefixWord, tailWord_7213959, baseEnd_7213959] using wordTrace_append hprefix tailTrace_7213959
  have hstable : (prefixWord ++ tailWord_7213959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7213959).length < 2 ^ (prefixWord ++ tailWord_7213959).sum := by decide
  have hdescent : baseEnd_7213959 < baseStart_7213959 := by decide
  rcases family_descends (prefixWord ++ tailWord_7213959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7213962 : List Nat := [3, 1, 2, 4, 1, 1, 4, 1, 1, 2, 3]
def baseStart_7213962 : Nat := 118140960795 + 7213962 * 2 ^ 59
def prefixEnd_7213962 : Nat := 4983230072969 + 3 ^ 40 * 7213962 * 2
def baseEnd_7213962 : Nat := 3704229929270009574198599

theorem tailTrace_7213962 : CollatzResearch.WordTrace tailWord_7213962 prefixEnd_7213962 3704229929270009574198599 := by
  unfold tailWord_7213962
  simp only [CollatzResearch.WordTrace]
  refine ⟨65778702472763798866617035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175409873260703463644312093 65778702472763798866617035)
  ·
    refine ⟨98668053709145698299925553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65778702472763798866617035 98668053709145698299925553)
    ·
      refine ⟨74001040281859273724944165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98668053709145698299925553 74001040281859273724944165)
      ·
        refine ⟨13875195052848613823427031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 74001040281859273724944165 13875195052848613823427031)
        ·
          refine ⟨20812792579272920735140547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13875195052848613823427031 20812792579272920735140547)
          ·
            refine ⟨31219188868909381102710821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20812792579272920735140547 31219188868909381102710821)
            ·
              refine ⟨5853597912920508956758279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31219188868909381102710821 5853597912920508956758279)
              ·
                refine ⟨8780396869380763435137419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5853597912920508956758279 8780396869380763435137419)
                ·
                  refine ⟨13170595304071145152706129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8780396869380763435137419 13170595304071145152706129)
                  ·
                    refine ⟨9877946478053358864529597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13170595304071145152706129 9877946478053358864529597)
                    ·
                      refine ⟨3704229929270009574198599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9877946478053358864529597 3704229929270009574198599)
                      ·
                        rfl

theorem cell23_7213962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 4, 1, 1, 2, 3].length) (baseStart_7213962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7213962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7213962 prefixEnd_7213962 := by exact prefixLift 7213962
  have htrace : WordTrace (prefixWord ++ tailWord_7213962) baseStart_7213962 baseEnd_7213962 := by
    simpa [prefixWord, tailWord_7213962, baseEnd_7213962] using wordTrace_append hprefix tailTrace_7213962
  have hstable : (prefixWord ++ tailWord_7213962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7213962).length < 2 ^ (prefixWord ++ tailWord_7213962).sum := by decide
  have hdescent : baseEnd_7213962 < baseStart_7213962 := by decide
  rcases family_descends (prefixWord ++ tailWord_7213962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7214115 : List Nat := [1, 1, 1, 4, 3, 3, 1, 2, 3, 4]
def baseStart_7214115 : Nat := 118140960795 + 7214115 * 2 ^ 59
def prefixEnd_7214115 : Nat := 4983230072969 + 3 ^ 40 * 7214115 * 2
def baseEnd_7214115 : Nat := 1234769497270049158528465

theorem tailTrace_7214115 : CollatzResearch.WordTrace tailWord_7214115 prefixEnd_7214115 1234769497270049158528465 := by
  unfold tailWord_7214115
  simp only [CollatzResearch.WordTrace]
  refine ⟨263120390259500902596787799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175413593506333935064525199 263120390259500902596787799)
  ·
    refine ⟨394680585389251353895181699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263120390259500902596787799 394680585389251353895181699)
    ·
      refine ⟨592020878083877030842772549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 394680585389251353895181699 592020878083877030842772549)
      ·
        refine ⟨111003914640726943283019853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 592020878083877030842772549 111003914640726943283019853)
        ·
          refine ⟨41626467990272603731132445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 111003914640726943283019853 41626467990272603731132445)
          ·
            refine ⟨15609925496352226399174667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41626467990272603731132445 15609925496352226399174667)
            ·
              refine ⟨23414888244528339598762001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15609925496352226399174667 23414888244528339598762001)
              ·
                refine ⟨17561166183396254699071501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23414888244528339598762001 17561166183396254699071501)
                ·
                  refine ⟨6585437318773595512151813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17561166183396254699071501 6585437318773595512151813)
                  ·
                    refine ⟨1234769497270049158528465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6585437318773595512151813 1234769497270049158528465)
                    ·
                      rfl

theorem cell23_7214115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 1, 2, 3, 4].length) (baseStart_7214115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7214115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7214115 prefixEnd_7214115 := by exact prefixLift 7214115
  have htrace : WordTrace (prefixWord ++ tailWord_7214115) baseStart_7214115 baseEnd_7214115 := by
    simpa [prefixWord, tailWord_7214115, baseEnd_7214115] using wordTrace_append hprefix tailTrace_7214115
  have hstable : (prefixWord ++ tailWord_7214115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7214115).length < 2 ^ (prefixWord ++ tailWord_7214115).sum := by decide
  have hdescent : baseEnd_7214115 < baseStart_7214115 := by decide
  rcases family_descends (prefixWord ++ tailWord_7214115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7214145 : List Nat := [1, 2, 5, 1, 3, 1, 1, 1, 8]
def baseStart_7214145 : Nat := 118140960795 + 7214145 * 2 ^ 59
def prefixEnd_7214145 : Nat := 4983230072969 + 3 ^ 40 * 7214145 * 2
def baseEnd_7214145 : Nat := 411591544025531373134473

theorem tailTrace_7214145 : CollatzResearch.WordTrace tailWord_7214145 prefixEnd_7214145 411591544025531373134473 := by
  unfold tailWord_7214145
  simp only [CollatzResearch.WordTrace]
  refine ⟨263121484449392217720379889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175414322966261478480253259 263121484449392217720379889)
  ·
    refine ⟨197341113337044163290284917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 263121484449392217720379889 197341113337044163290284917)
    ·
      refine ⟨18500729375347890308464211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 197341113337044163290284917 18500729375347890308464211)
      ·
        refine ⟨27751094063021835462696317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18500729375347890308464211 27751094063021835462696317)
        ·
          refine ⟨10406660273633188298511119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27751094063021835462696317 10406660273633188298511119)
          ·
            refine ⟨15609990410449782447766679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10406660273633188298511119 15609990410449782447766679)
            ·
              refine ⟨23414985615674673671650019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15609990410449782447766679 23414985615674673671650019)
              ·
                refine ⟨35122478423512010507475029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23414985615674673671650019 35122478423512010507475029)
                ·
                  refine ⟨411591544025531373134473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 35122478423512010507475029 411591544025531373134473)
                  ·
                    rfl

theorem cell23_7214145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 1, 1, 8].length) (baseStart_7214145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7214145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7214145 prefixEnd_7214145 := by exact prefixLift 7214145
  have htrace : WordTrace (prefixWord ++ tailWord_7214145) baseStart_7214145 baseEnd_7214145 := by
    simpa [prefixWord, tailWord_7214145, baseEnd_7214145] using wordTrace_append hprefix tailTrace_7214145
  have hstable : (prefixWord ++ tailWord_7214145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7214145).length < 2 ^ (prefixWord ++ tailWord_7214145).sum := by decide
  have hdescent : baseEnd_7214145 < baseStart_7214145 := by decide
  rcases family_descends (prefixWord ++ tailWord_7214145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7214162 : List Nat := [3, 2, 2, 1, 3, 2, 3, 1, 6]
def baseStart_7214162 : Nat := 118140960795 + 7214162 * 2 ^ 59
def prefixEnd_7214162 : Nat := 4983230072969 + 3 ^ 40 * 7214162 * 2
def baseEnd_7214162 : Nat := 411592513933434310188631

theorem tailTrace_7214162 : CollatzResearch.WordTrace tailWord_7214162 prefixEnd_7214162 411592513933434310188631 := by
  unfold tailWord_7214162
  simp only [CollatzResearch.WordTrace]
  refine ⟨65780526122582657405937185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175414736326887086415832493 65780526122582657405937185)
  ·
    refine ⟨49335394591936993054452889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65780526122582657405937185 49335394591936993054452889)
    ·
      refine ⟨37001545943952744790839667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49335394591936993054452889 37001545943952744790839667)
      ·
        refine ⟨55502318915929117186259501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37001545943952744790839667 55502318915929117186259501)
        ·
          refine ⟨20813369593473418944847313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55502318915929117186259501 20813369593473418944847313)
          ·
            refine ⟨15610027195105064208635485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20813369593473418944847313 15610027195105064208635485)
            ·
              refine ⟨5853760198164399078238307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15610027195105064208635485 5853760198164399078238307)
              ·
                refine ⟨8780640297246598617357461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5853760198164399078238307 8780640297246598617357461)
                ·
                  refine ⟨411592513933434310188631, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8780640297246598617357461 411592513933434310188631)
                  ·
                    rfl

theorem cell23_7214162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 3, 1, 6].length) (baseStart_7214162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7214162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7214162 prefixEnd_7214162 := by exact prefixLift 7214162
  have htrace : WordTrace (prefixWord ++ tailWord_7214162) baseStart_7214162 baseEnd_7214162 := by
    simpa [prefixWord, tailWord_7214162, baseEnd_7214162] using wordTrace_append hprefix tailTrace_7214162
  have hstable : (prefixWord ++ tailWord_7214162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7214162).length < 2 ^ (prefixWord ++ tailWord_7214162).sum := by decide
  have hdescent : baseEnd_7214162 < baseStart_7214162 := by decide
  rcases family_descends (prefixWord ++ tailWord_7214162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7214165 : List Nat := [1, 3, 2, 2, 1, 2, 1, 1, 3, 5, 2]
def baseStart_7214165 : Nat := 118140960795 + 7214165 * 2 ^ 59
def prefixEnd_7214165 : Nat := 4983230072969 + 3 ^ 40 * 7214165 * 2
def baseEnd_7214165 : Nat := 3704334165842872279960165

theorem tailTrace_7214165 : CollatzResearch.WordTrace tailWord_7214165 prefixEnd_7214165 3704334165842872279960165 := by
  unfold tailWord_7214165
  simp only [CollatzResearch.WordTrace]
  refine ⟨263122213909319761136107949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175414809272879840757405299 263122213909319761136107949)
  ·
    refine ⟨98670830215994910426040481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 263122213909319761136107949 98670830215994910426040481)
    ·
      refine ⟨74003122661996182819530361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98670830215994910426040481 74003122661996182819530361)
      ·
        refine ⟨55502341996497137114647771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74003122661996182819530361 55502341996497137114647771)
        ·
          refine ⟨83253512994745705671971657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55502341996497137114647771 83253512994745705671971657)
          ·
            refine ⟨62440134746059279253978743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83253512994745705671971657 62440134746059279253978743)
            ·
              refine ⟨93660202119088918880968115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62440134746059279253978743 93660202119088918880968115)
              ·
                refine ⟨140490303178633378321452173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 93660202119088918880968115 140490303178633378321452173)
                ·
                  refine ⟨52683863691987516870544565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 140490303178633378321452173 52683863691987516870544565)
                  ·
                    refine ⟨4939112221123829706613553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 52683863691987516870544565 4939112221123829706613553)
                    ·
                      refine ⟨3704334165842872279960165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4939112221123829706613553 3704334165842872279960165)
                      ·
                        rfl

theorem cell23_7214165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 1, 3, 5, 2].length) (baseStart_7214165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7214165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7214165 prefixEnd_7214165 := by exact prefixLift 7214165
  have htrace : WordTrace (prefixWord ++ tailWord_7214165) baseStart_7214165 baseEnd_7214165 := by
    simpa [prefixWord, tailWord_7214165, baseEnd_7214165] using wordTrace_append hprefix tailTrace_7214165
  have hstable : (prefixWord ++ tailWord_7214165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7214165).length < 2 ^ (prefixWord ++ tailWord_7214165).sum := by decide
  have hdescent : baseEnd_7214165 < baseStart_7214165 := by decide
  rcases family_descends (prefixWord ++ tailWord_7214165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7214172 : List Nat := [2, 2, 4, 1, 1, 1, 1, 4, 3, 1, 3]
def baseStart_7214172 : Nat := 118140960795 + 7214172 * 2 ^ 59
def prefixEnd_7214172 : Nat := 4983230072969 + 3 ^ 40 * 7214172 * 2
def baseEnd_7214172 : Nat := 3704337760207453752572633

theorem tailTrace_7214172 : CollatzResearch.WordTrace tailWord_7214172 prefixEnd_7214172 3704337760207453752572633 := by
  unfold tailWord_7214172
  simp only [CollatzResearch.WordTrace]
  refine ⟨131561234610147200665806385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175414979480196267554408513 131561234610147200665806385)
  ·
    refine ⟨98670925957610400499354789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131561234610147200665806385 98670925957610400499354789)
    ·
      refine ⟨18500798617051950093629023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 98670925957610400499354789 18500798617051950093629023)
      ·
        refine ⟨27751197925577925140443535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18500798617051950093629023 27751197925577925140443535)
        ·
          refine ⟨41626796888366887710665303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27751197925577925140443535 41626796888366887710665303)
          ·
            refine ⟨62440195332550331565997955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41626796888366887710665303 62440195332550331565997955)
            ·
              refine ⟨93660292998825497348996933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62440195332550331565997955 93660292998825497348996933)
              ·
                refine ⟨17561304937279780752936925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 93660292998825497348996933 17561304937279780752936925)
                ·
                  refine ⟨6585489351479917782351347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17561304937279780752936925 6585489351479917782351347)
                  ·
                    refine ⟨9878234027219876673527021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6585489351479917782351347 9878234027219876673527021)
                    ·
                      refine ⟨3704337760207453752572633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9878234027219876673527021 3704337760207453752572633)
                      ·
                        rfl

theorem cell23_7214172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 4, 3, 1, 3].length) (baseStart_7214172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7214172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7214172 prefixEnd_7214172 := by exact prefixLift 7214172
  have htrace : WordTrace (prefixWord ++ tailWord_7214172) baseStart_7214172 baseEnd_7214172 := by
    simpa [prefixWord, tailWord_7214172, baseEnd_7214172] using wordTrace_append hprefix tailTrace_7214172
  have hstable : (prefixWord ++ tailWord_7214172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7214172).length < 2 ^ (prefixWord ++ tailWord_7214172).sum := by decide
  have hdescent : baseEnd_7214172 < baseStart_7214172 := by decide
  rcases family_descends (prefixWord ++ tailWord_7214172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7214175 : List Nat := [1, 1, 2, 3, 1, 1, 6, 2, 1, 5]
def baseStart_7214175 : Nat := 118140960795 + 7214175 * 2 ^ 59
def prefixEnd_7214175 : Nat := 4983230072969 + 3 ^ 40 * 7214175 * 2
def baseEnd_7214175 : Nat := 1234779766883139080278373

theorem tailTrace_7214175 : CollatzResearch.WordTrace tailWord_7214175 prefixEnd_7214175 1234779766883139080278373 := by
  unfold tailWord_7214175
  simp only [CollatzResearch.WordTrace]
  refine ⟨263122578639283532843971979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175415052426189021895981319 263122578639283532843971979)
  ·
    refine ⟨394683867958925299265957969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263122578639283532843971979 394683867958925299265957969)
    ·
      refine ⟨296012900969193974449468477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 394683867958925299265957969 296012900969193974449468477)
      ·
        refine ⟨111004837863447740418550679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 296012900969193974449468477 111004837863447740418550679)
        ·
          refine ⟨166507256795171610627826019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111004837863447740418550679 166507256795171610627826019)
          ·
            refine ⟨249760885192757415941739029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 166507256795171610627826019 249760885192757415941739029)
            ·
              refine ⟨11707541493410503872269017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 249760885192757415941739029 11707541493410503872269017)
              ·
                refine ⟨8780656120057877904201763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11707541493410503872269017 8780656120057877904201763)
                ·
                  refine ⟨13170984180086816856302645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8780656120057877904201763 13170984180086816856302645)
                  ·
                    refine ⟨1234779766883139080278373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13170984180086816856302645 1234779766883139080278373)
                    ·
                      rfl

theorem cell23_7214175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 6, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 6, 2, 1, 5].length) (baseStart_7214175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7214175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7214175 prefixEnd_7214175 := by exact prefixLift 7214175
  have htrace : WordTrace (prefixWord ++ tailWord_7214175) baseStart_7214175 baseEnd_7214175 := by
    simpa [prefixWord, tailWord_7214175, baseEnd_7214175] using wordTrace_append hprefix tailTrace_7214175
  have hstable : (prefixWord ++ tailWord_7214175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7214175).length < 2 ^ (prefixWord ++ tailWord_7214175).sum := by decide
  have hdescent : baseEnd_7214175 < baseStart_7214175 := by decide
  rcases family_descends (prefixWord ++ tailWord_7214175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7214188 : List Nat := [2, 2, 1, 1, 3, 2, 2, 1, 3, 6]
def baseStart_7214188 : Nat := 118140960795 + 7214188 * 2 ^ 59
def prefixEnd_7214188 : Nat := 4983230072969 + 3 ^ 40 * 7214188 * 2
def baseEnd_7214188 : Nat := 1234781991965975229990853

theorem tailTrace_7214188 : CollatzResearch.WordTrace tailWord_7214188 prefixEnd_7214188 1234781991965975229990853 := by
  unfold tailWord_7214188
  simp only [CollatzResearch.WordTrace]
  refine ⟨131561526394118218032097609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175415368525490957376130145 131561526394118218032097609)
  ·
    refine ⟨98671144795588663524073207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131561526394118218032097609 98671144795588663524073207)
    ·
      refine ⟨148006717193382995286109811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98671144795588663524073207 148006717193382995286109811)
      ·
        refine ⟨222010075790074492929164717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148006717193382995286109811 222010075790074492929164717)
        ·
          refine ⟨83253778421277934848436769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 222010075790074492929164717 83253778421277934848436769)
          ·
            refine ⟨62440333815958451136327577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83253778421277934848436769 62440333815958451136327577)
            ·
              refine ⟨46830250361968838352245683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62440333815958451136327577 46830250361968838352245683)
              ·
                refine ⟨70245375542953257528368525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46830250361968838352245683 70245375542953257528368525)
                ·
                  refine ⟨26342015828607471573138197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 70245375542953257528368525 26342015828607471573138197)
                  ·
                    refine ⟨1234781991965975229990853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26342015828607471573138197 1234781991965975229990853)
                    ·
                      rfl

theorem cell23_7214188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 6].length) (baseStart_7214188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7214188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7214188 prefixEnd_7214188 := by exact prefixLift 7214188
  have htrace : WordTrace (prefixWord ++ tailWord_7214188) baseStart_7214188 baseEnd_7214188 := by
    simpa [prefixWord, tailWord_7214188, baseEnd_7214188] using wordTrace_append hprefix tailTrace_7214188
  have hstable : (prefixWord ++ tailWord_7214188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7214188).length < 2 ^ (prefixWord ++ tailWord_7214188).sum := by decide
  have hdescent : baseEnd_7214188 < baseStart_7214188 := by decide
  rcases family_descends (prefixWord ++ tailWord_7214188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7214205 : List Nat := [1, 4, 1, 1, 3, 1, 1, 3, 4, 4]
def baseStart_7214205 : Nat := 118140960795 + 7214205 * 2 ^ 59
def prefixEnd_7214205 : Nat := 4983230072969 + 3 ^ 40 * 7214205 * 2
def baseEnd_7214205 : Nat := 1234784901689684041153327

theorem tailTrace_7214205 : CollatzResearch.WordTrace tailWord_7214205 prefixEnd_7214205 1234784901689684041153327 := by
  unfold tailWord_7214205
  simp only [CollatzResearch.WordTrace]
  refine ⟨263123672829174847967564069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175415781886116565311709379 263123672829174847967564069)
  ·
    refine ⟨49335688655470283993918263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 263123672829174847967564069 49335688655470283993918263)
    ·
      refine ⟨74003532983205425990877395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49335688655470283993918263 74003532983205425990877395)
      ·
        refine ⟨111005299474808138986316093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74003532983205425990877395 111005299474808138986316093)
        ·
          refine ⟨41626987303053052119868535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 111005299474808138986316093 41626987303053052119868535)
          ·
            refine ⟨62440480954579578179802803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41626987303053052119868535 62440480954579578179802803)
            ·
              refine ⟨93660721431869367269704205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62440480954579578179802803 93660721431869367269704205)
              ·
                refine ⟨35122770536951012726139077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 93660721431869367269704205 35122770536951012726139077)
                ·
                  refine ⟨6585519475678314886151077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35122770536951012726139077 6585519475678314886151077)
                  ·
                    refine ⟨1234784901689684041153327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6585519475678314886151077 1234784901689684041153327)
                    ·
                      rfl

theorem cell23_7214205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 3, 4, 4].length) (baseStart_7214205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7214205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7214205 prefixEnd_7214205 := by exact prefixLift 7214205
  have htrace : WordTrace (prefixWord ++ tailWord_7214205) baseStart_7214205 baseEnd_7214205 := by
    simpa [prefixWord, tailWord_7214205, baseEnd_7214205] using wordTrace_append hprefix tailTrace_7214205
  have hstable : (prefixWord ++ tailWord_7214205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7214205).length < 2 ^ (prefixWord ++ tailWord_7214205).sum := by decide
  have hdescent : baseEnd_7214205 < baseStart_7214205 := by decide
  rcases family_descends (prefixWord ++ tailWord_7214205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7214208 : List Nat := [2, 1, 1, 2, 1, 3, 3, 2, 1, 1, 6]
def baseStart_7214208 : Nat := 118140960795 + 7214208 * 2 ^ 59
def prefixEnd_7214208 : Nat := 4983230072969 + 3 ^ 40 * 7214208 * 2
def baseEnd_7214208 : Nat := 3704356245511015611722467

theorem tailTrace_7214208 : CollatzResearch.WordTrace tailWord_7214208 prefixEnd_7214208 3704356245511015611722467 := by
  unfold tailWord_7214208
  simp only [CollatzResearch.WordTrace]
  refine ⟨131561891124081989739961639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175415854832109319653282185 131561891124081989739961639)
  ·
    refine ⟨197342836686122984609942459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131561891124081989739961639 197342836686122984609942459)
    ·
      refine ⟨296014255029184476914913689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197342836686122984609942459 296014255029184476914913689)
      ·
        refine ⟨222010691271888357686185267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 296014255029184476914913689 222010691271888357686185267)
        ·
          refine ⟨333016036907832536529277901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 222010691271888357686185267 333016036907832536529277901)
          ·
            refine ⟨124881013840437201198479213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 333016036907832536529277901 124881013840437201198479213)
            ·
              refine ⟨46830380190163950449429705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 124881013840437201198479213 46830380190163950449429705)
              ·
                refine ⟨35122785142622962837072279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46830380190163950449429705 35122785142622962837072279)
                ·
                  refine ⟨52684177713934444255608419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35122785142622962837072279 52684177713934444255608419)
                  ·
                    refine ⟨79026266570901666383412629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 52684177713934444255608419 79026266570901666383412629)
                    ·
                      refine ⟨3704356245511015611722467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 79026266570901666383412629 3704356245511015611722467)
                      ·
                        rfl

theorem cell23_7214208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 3, 2, 1, 1, 6].length) (baseStart_7214208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7214208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7214208 prefixEnd_7214208 := by exact prefixLift 7214208
  have htrace : WordTrace (prefixWord ++ tailWord_7214208) baseStart_7214208 baseEnd_7214208 := by
    simpa [prefixWord, tailWord_7214208, baseEnd_7214208] using wordTrace_append hprefix tailTrace_7214208
  have hstable : (prefixWord ++ tailWord_7214208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7214208).length < 2 ^ (prefixWord ++ tailWord_7214208).sum := by decide
  have hdescent : baseEnd_7214208 < baseStart_7214208 := by decide
  rcases family_descends (prefixWord ++ tailWord_7214208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7214215 : List Nat := [1, 1, 4, 2, 1, 1, 1, 4, 3, 2, 3]
def baseStart_7214215 : Nat := 118140960795 + 7214215 * 2 ^ 59
def prefixEnd_7214215 : Nat := 4983230072969 + 3 ^ 40 * 7214215 * 2
def baseEnd_7214215 : Nat := 3704359839875597084334935

theorem tailTrace_7214215 : CollatzResearch.WordTrace tailWord_7214215 prefixEnd_7214215 3704359839875597084334935 := by
  unfold tailWord_7214215
  simp only [CollatzResearch.WordTrace]
  refine ⟨263124037559138619675428099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175416025039425746450285399 263124037559138619675428099)
  ·
    refine ⟨394686056338707929513142149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263124037559138619675428099 394686056338707929513142149)
    ·
      refine ⟨74003635563507736783714153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 394686056338707929513142149 74003635563507736783714153)
      ·
        refine ⟨55502726672630802587785615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74003635563507736783714153 55502726672630802587785615)
        ·
          refine ⟨83254090008946203881678423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55502726672630802587785615 83254090008946203881678423)
          ·
            refine ⟨124881135013419305822517635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83254090008946203881678423 124881135013419305822517635)
            ·
              refine ⟨187321702520128958733776453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 124881135013419305822517635 187321702520128958733776453)
              ·
                refine ⟨35122819222524179762583085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 187321702520128958733776453 35122819222524179762583085)
                ·
                  refine ⟨13171057208446567410968657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35122819222524179762583085 13171057208446567410968657)
                  ·
                    refine ⟨9878292906334925558226493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13171057208446567410968657 9878292906334925558226493)
                    ·
                      refine ⟨3704359839875597084334935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9878292906334925558226493 3704359839875597084334935)
                      ·
                        rfl

theorem cell23_7214215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 4, 3, 2, 3].length) (baseStart_7214215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7214215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7214215 prefixEnd_7214215 := by exact prefixLift 7214215
  have htrace : WordTrace (prefixWord ++ tailWord_7214215) baseStart_7214215 baseEnd_7214215 := by
    simpa [prefixWord, tailWord_7214215, baseEnd_7214215] using wordTrace_append hprefix tailTrace_7214215
  have hstable : (prefixWord ++ tailWord_7214215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7214215).length < 2 ^ (prefixWord ++ tailWord_7214215).sum := by decide
  have hdescent : baseEnd_7214215 < baseStart_7214215 := by decide
  rcases family_descends (prefixWord ++ tailWord_7214215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7214232 : List Nat := [2, 1, 2, 4, 2, 2, 1, 1, 3, 2, 3]
def baseStart_7214232 : Nat := 118140960795 + 7214232 * 2 ^ 59
def prefixEnd_7214232 : Nat := 4983230072969 + 3 ^ 40 * 7214232 * 2
def baseEnd_7214232 : Nat := 3704368569046723517822357

theorem tailTrace_7214232 : CollatzResearch.WordTrace tailWord_7214232 prefixEnd_7214232 3704368569046723517822357 := by
  unfold tailWord_7214232
  simp only [CollatzResearch.WordTrace]
  refine ⟨131562328800038515789398475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175416438400051354385864633 131562328800038515789398475)
  ·
    refine ⟨197343493200057773684097713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131562328800038515789398475 197343493200057773684097713)
    ·
      refine ⟨148007619900043330263073285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 197343493200057773684097713 148007619900043330263073285)
      ·
        refine ⟨27751428731258124424326241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 148007619900043330263073285 27751428731258124424326241)
        ·
          refine ⟨20813571548443593318244681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27751428731258124424326241 20813571548443593318244681)
          ·
            refine ⟨15610178661332694988683511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20813571548443593318244681 15610178661332694988683511)
            ·
              refine ⟨23415267991999042483025267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15610178661332694988683511 23415267991999042483025267)
              ·
                refine ⟨35122901987998563724537901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23415267991999042483025267 35122901987998563724537901)
                ·
                  refine ⟨13171088245499461396701713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35122901987998563724537901 13171088245499461396701713)
                  ·
                    refine ⟨9878316184124596047526285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13171088245499461396701713 9878316184124596047526285)
                    ·
                      refine ⟨3704368569046723517822357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9878316184124596047526285 3704368569046723517822357)
                      ·
                        rfl

theorem cell23_7214232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 1, 1, 3, 2, 3].length) (baseStart_7214232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7214232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7214232 prefixEnd_7214232 := by exact prefixLift 7214232
  have htrace : WordTrace (prefixWord ++ tailWord_7214232) baseStart_7214232 baseEnd_7214232 := by
    simpa [prefixWord, tailWord_7214232, baseEnd_7214232] using wordTrace_append hprefix tailTrace_7214232
  have hstable : (prefixWord ++ tailWord_7214232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7214232).length < 2 ^ (prefixWord ++ tailWord_7214232).sum := by decide
  have hdescent : baseEnd_7214232 < baseStart_7214232 := by decide
  rcases family_descends (prefixWord ++ tailWord_7214232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7214245 : List Nat := [1, 3, 1, 2, 1, 4, 1, 1, 3, 3, 3]
def baseStart_7214245 : Nat := 118140960795 + 7214245 * 2 ^ 59
def prefixEnd_7214245 : Nat := 4983230072969 + 3 ^ 40 * 7214245 * 2
def baseEnd_7214245 : Nat := 3704375244295231966959797

theorem tailTrace_7214245 : CollatzResearch.WordTrace tailWord_7214245 prefixEnd_7214245 3704375244295231966959797 := by
  unfold tailWord_7214245
  simp only [CollatzResearch.WordTrace]
  refine ⟨263125131749029934799020189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175416754499353289866013459 263125131749029934799020189)
  ·
    refine ⟨98671924405886225549632571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 263125131749029934799020189 98671924405886225549632571)
    ·
      refine ⟨148007886608829338324448857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98671924405886225549632571 148007886608829338324448857)
      ·
        refine ⟨111005914956622003743336643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148007886608829338324448857 111005914956622003743336643)
        ·
          refine ⟨166508872434933005615004965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111005914956622003743336643 166508872434933005615004965)
          ·
            refine ⟨31220413581549938552813431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 166508872434933005615004965 31220413581549938552813431)
            ·
              refine ⟨46830620372324907829220147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31220413581549938552813431 46830620372324907829220147)
              ·
                refine ⟨70245930558487361743830221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46830620372324907829220147 70245930558487361743830221)
                ·
                  refine ⟨26342223959432760653936333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 70245930558487361743830221 26342223959432760653936333)
                  ·
                    refine ⟨9878333984787285245226125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26342223959432760653936333 9878333984787285245226125)
                    ·
                      refine ⟨3704375244295231966959797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9878333984787285245226125 3704375244295231966959797)
                      ·
                        rfl

theorem cell23_7214245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 1, 1, 3, 3, 3].length) (baseStart_7214245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7214245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7214245 prefixEnd_7214245 := by exact prefixLift 7214245
  have htrace : WordTrace (prefixWord ++ tailWord_7214245) baseStart_7214245 baseEnd_7214245 := by
    simpa [prefixWord, tailWord_7214245, baseEnd_7214245] using wordTrace_append hprefix tailTrace_7214245
  have hstable : (prefixWord ++ tailWord_7214245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7214245).length < 2 ^ (prefixWord ++ tailWord_7214245).sum := by decide
  have hdescent : baseEnd_7214245 < baseStart_7214245 := by decide
  rcases family_descends (prefixWord ++ tailWord_7214245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7214315 : List Nat := [1, 1, 1, 1, 2, 6, 1, 2, 2, 2, 4]
def baseStart_7214315 : Nat := 118140960795 + 7214315 * 2 ^ 59
def prefixEnd_7214315 : Nat := 4983230072969 + 3 ^ 40 * 7214315 * 2
def baseEnd_7214315 : Nat := 3704411187941046693084475

theorem tailTrace_7214315 : CollatzResearch.WordTrace tailWord_7214315 prefixEnd_7214315 3704411187941046693084475 := by
  unfold tailWord_7214315
  simp only [CollatzResearch.WordTrace]
  refine ⟨263127684858776336754068399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175418456572517557836045599 263127684858776336754068399)
  ·
    refine ⟨394691527288164505131102599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263127684858776336754068399 394691527288164505131102599)
    ·
      refine ⟨592037290932246757696653899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 394691527288164505131102599 592037290932246757696653899)
      ·
        refine ⟨888055936398370136544980849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 592037290932246757696653899 888055936398370136544980849)
        ·
          refine ⟨666041952298777602408735637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 888055936398370136544980849 666041952298777602408735637)
          ·
            refine ⟨31220716514005200112909483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 666041952298777602408735637 31220716514005200112909483)
            ·
              refine ⟨46831074771007800169364225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31220716514005200112909483 46831074771007800169364225)
              ·
                refine ⟨35123306078255850127023169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46831074771007800169364225 35123306078255850127023169)
                ·
                  refine ⟨26342479558691887595267377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35123306078255850127023169 26342479558691887595267377)
                  ·
                    refine ⟨19756859669018915696450533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26342479558691887595267377 19756859669018915696450533)
                    ·
                      refine ⟨3704411187941046693084475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19756859669018915696450533 3704411187941046693084475)
                      ·
                        rfl

theorem cell23_7214315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 1, 2, 2, 2, 4].length) (baseStart_7214315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7214315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7214315 prefixEnd_7214315 := by exact prefixLift 7214315
  have htrace : WordTrace (prefixWord ++ tailWord_7214315) baseStart_7214315 baseEnd_7214315 := by
    simpa [prefixWord, tailWord_7214315, baseEnd_7214315] using wordTrace_append hprefix tailTrace_7214315
  have hstable : (prefixWord ++ tailWord_7214315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7214315).length < 2 ^ (prefixWord ++ tailWord_7214315).sum := by decide
  have hdescent : baseEnd_7214315 < baseStart_7214315 := by decide
  rcases family_descends (prefixWord ++ tailWord_7214315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7214372 : List Nat := [2, 3, 1, 3, 1, 1, 3, 2, 2, 5]
def baseStart_7214372 : Nat := 118140960795 + 7214372 * 2 ^ 59
def prefixEnd_7214372 : Nat := 4983230072969 + 3 ^ 40 * 7214372 * 2
def baseEnd_7214372 : Nat := 1234813485446117656690571

theorem tailTrace_7214372 : CollatzResearch.WordTrace tailWord_7214372 prefixEnd_7214372 1234813485446117656690571 := by
  unfold tailWord_7214372
  simp only [CollatzResearch.WordTrace]
  refine ⟨131564881909784917744446685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175419842546379890325928913 131564881909784917744446685)
  ·
    refine ⟨49336830716169344154167507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 131564881909784917744446685 49336830716169344154167507)
    ·
      refine ⟨74005246074254016231251261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49336830716169344154167507 74005246074254016231251261)
      ·
        refine ⟨27751967277845256086719223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74005246074254016231251261 27751967277845256086719223)
        ·
          refine ⟨41627950916767884130078835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27751967277845256086719223 41627950916767884130078835)
          ·
            refine ⟨62441926375151826195118253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41627950916767884130078835 62441926375151826195118253)
            ·
              refine ⟨23415722390681934823169345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62441926375151826195118253 23415722390681934823169345)
              ·
                refine ⟨17561791793011451117377009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23415722390681934823169345 17561791793011451117377009)
                ·
                  refine ⟨13171343844758588338032757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17561791793011451117377009 13171343844758588338032757)
                  ·
                    refine ⟨1234813485446117656690571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13171343844758588338032757 1234813485446117656690571)
                    ·
                      rfl

theorem cell23_7214372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 3, 2, 2, 5].length) (baseStart_7214372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7214372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7214372 prefixEnd_7214372 := by exact prefixLift 7214372
  have htrace : WordTrace (prefixWord ++ tailWord_7214372) baseStart_7214372 baseEnd_7214372 := by
    simpa [prefixWord, tailWord_7214372, baseEnd_7214372] using wordTrace_append hprefix tailTrace_7214372
  have hstable : (prefixWord ++ tailWord_7214372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7214372).length < 2 ^ (prefixWord ++ tailWord_7214372).sum := by decide
  have hdescent : baseEnd_7214372 < baseStart_7214372 := by decide
  rcases family_descends (prefixWord ++ tailWord_7214372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7214376 : List Nat := [2, 1, 5, 1, 2, 2, 3, 2, 5]
def baseStart_7214376 : Nat := 118140960795 + 7214376 * 2 ^ 59
def prefixEnd_7214376 : Nat := 4983230072969 + 3 ^ 40 * 7214376 * 2
def baseEnd_7214376 : Nat := 411604723362330106046855

theorem tailTrace_7214376 : CollatzResearch.WordTrace tailWord_7214376 prefixEnd_7214376 411604723362330106046855 := by
  unfold tailWord_7214376
  simp only [CollatzResearch.WordTrace]
  refine ⟨131564954855777672086019491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175419939807703562781359321 131564954855777672086019491)
  ·
    refine ⟨197347432283666508129029237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131564954855777672086019491 197347432283666508129029237)
    ·
      refine ⟨18501321776593735137096491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 197347432283666508129029237 18501321776593735137096491)
      ·
        refine ⟨27751982664890602705644737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18501321776593735137096491 27751982664890602705644737)
        ·
          refine ⟨20813986998667952029233553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27751982664890602705644737 20813986998667952029233553)
          ·
            refine ⟨15610490249000964021925165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20813986998667952029233553 15610490249000964021925165)
            ·
              refine ⟨5853933843375361508221937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15610490249000964021925165 5853933843375361508221937)
              ·
                refine ⟨4390450382531521131166453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5853933843375361508221937 4390450382531521131166453)
                ·
                  refine ⟨411604723362330106046855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4390450382531521131166453 411604723362330106046855)
                  ·
                    rfl

theorem cell23_7214376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 3, 2, 5].length) (baseStart_7214376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7214376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7214376 prefixEnd_7214376 := by exact prefixLift 7214376
  have htrace : WordTrace (prefixWord ++ tailWord_7214376) baseStart_7214376 baseEnd_7214376 := by
    simpa [prefixWord, tailWord_7214376, baseEnd_7214376] using wordTrace_append hprefix tailTrace_7214376
  have hstable : (prefixWord ++ tailWord_7214376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7214376).length < 2 ^ (prefixWord ++ tailWord_7214376).sum := by decide
  have hdescent : baseEnd_7214376 < baseStart_7214376 := by decide
  rcases family_descends (prefixWord ++ tailWord_7214376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7214392 : List Nat := [2, 1, 2, 1, 3, 1, 1, 3, 1, 6, 2]
def baseStart_7214392 : Nat := 118140960795 + 7214392 * 2 ^ 59
def prefixEnd_7214392 : Nat := 4983230072969 + 3 ^ 40 * 7214392 * 2
def baseEnd_7214392 : Nat := 3704450725951442891821621

theorem tailTrace_7214392 : CollatzResearch.WordTrace tailWord_7214392 prefixEnd_7214392 3704450725951442891821621 := by
  unfold tailWord_7214392
  simp only [CollatzResearch.WordTrace]
  refine ⟨131565246639748689452310715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175420328852998252603080953 131565246639748689452310715)
  ·
    refine ⟨197347869959623034178466073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131565246639748689452310715 197347869959623034178466073)
    ·
      refine ⟨148010902469717275633849555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 197347869959623034178466073 148010902469717275633849555)
      ·
        refine ⟨222016353704575913450774333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148010902469717275633849555 222016353704575913450774333)
        ·
          refine ⟨83256132639215967544040375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 222016353704575913450774333 83256132639215967544040375)
          ·
            refine ⟨124884198958823951316060563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83256132639215967544040375 124884198958823951316060563)
            ·
              refine ⟨187326298438235926974090845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 124884198958823951316060563 187326298438235926974090845)
              ·
                refine ⟨70247361914338472615284067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 187326298438235926974090845 70247361914338472615284067)
                ·
                  refine ⟨105371042871507708922926101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70247361914338472615284067 105371042871507708922926101)
                  ·
                    refine ⟨4939267634601923855762161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 105371042871507708922926101 4939267634601923855762161)
                    ·
                      refine ⟨3704450725951442891821621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4939267634601923855762161 3704450725951442891821621)
                      ·
                        rfl

theorem cell23_7214392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 3, 1, 6, 2].length) (baseStart_7214392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7214392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7214392 prefixEnd_7214392 := by exact prefixLift 7214392
  have htrace : WordTrace (prefixWord ++ tailWord_7214392) baseStart_7214392 baseEnd_7214392 := by
    simpa [prefixWord, tailWord_7214392, baseEnd_7214392] using wordTrace_append hprefix tailTrace_7214392
  have hstable : (prefixWord ++ tailWord_7214392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7214392).length < 2 ^ (prefixWord ++ tailWord_7214392).sum := by decide
  have hdescent : baseEnd_7214392 < baseStart_7214392 := by decide
  rcases family_descends (prefixWord ++ tailWord_7214392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7214405 : List Nat := [1, 3, 1, 1, 1, 2, 1, 3, 2, 4, 4]
def baseStart_7214405 : Nat := 118140960795 + 7214405 * 2 ^ 59
def prefixEnd_7214405 : Nat := 4983230072969 + 3 ^ 40 * 7214405 * 2
def baseEnd_7214405 : Nat := 3704457401199951340959061

theorem tailTrace_7214405 : CollatzResearch.WordTrace tailWord_7214405 prefixEnd_7214405 3704457401199951340959061 := by
  unfold tailWord_7214405
  simp only [CollatzResearch.WordTrace]
  refine ⟨263130967428450282124844669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175420644952300188083229779 263130967428450282124844669)
  ·
    refine ⟨98674112785668855796816751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 263130967428450282124844669 98674112785668855796816751)
    ·
      refine ⟨148011169178503283695225127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98674112785668855796816751 148011169178503283695225127)
      ·
        refine ⟨222016753767754925542837691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148011169178503283695225127 222016753767754925542837691)
        ·
          refine ⟨333025130651632388314256537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 222016753767754925542837691 333025130651632388314256537)
          ·
            refine ⟨249768847988724291235692403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 333025130651632388314256537 249768847988724291235692403)
            ·
              refine ⟨374653271983086436853538605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 249768847988724291235692403 374653271983086436853538605)
              ·
                refine ⟨140494976993657413820076977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 374653271983086436853538605 140494976993657413820076977)
                ·
                  refine ⟨105371232745243060365057733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 140494976993657413820076977 105371232745243060365057733)
                  ·
                    refine ⟨19757106139733073818448325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 105371232745243060365057733 19757106139733073818448325)
                    ·
                      refine ⟨3704457401199951340959061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19757106139733073818448325 3704457401199951340959061)
                      ·
                        rfl

theorem cell23_7214405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 3, 2, 4, 4].length) (baseStart_7214405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7214405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7214405 prefixEnd_7214405 := by exact prefixLift 7214405
  have htrace : WordTrace (prefixWord ++ tailWord_7214405) baseStart_7214405 baseEnd_7214405 := by
    simpa [prefixWord, tailWord_7214405, baseEnd_7214405] using wordTrace_append hprefix tailTrace_7214405
  have hstable : (prefixWord ++ tailWord_7214405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7214405).length < 2 ^ (prefixWord ++ tailWord_7214405).sum := by decide
  have hdescent : baseEnd_7214405 < baseStart_7214405 := by decide
  rcases family_descends (prefixWord ++ tailWord_7214405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7214419 : List Nat := [1, 1, 1, 2, 1, 1, 6, 5, 1, 4]
def baseStart_7214419 : Nat := 118140960795 + 7214419 * 2 ^ 59
def prefixEnd_7214419 : Nat := 4983230072969 + 3 ^ 40 * 7214419 * 2
def baseEnd_7214419 : Nat := 1234821529976371428727999

theorem tailTrace_7214419 : CollatzResearch.WordTrace tailWord_7214419 prefixEnd_7214419 1234821529976371428727999 := by
  unfold tailWord_7214419
  simp only [CollatzResearch.WordTrace]
  refine ⟨263131478050399562515854311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175420985366933041677236207 263131478050399562515854311)
  ·
    refine ⟨394697217075599343773781467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263131478050399562515854311 394697217075599343773781467)
    ·
      refine ⟨592045825613399015660672201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 394697217075599343773781467 592045825613399015660672201)
      ·
        refine ⟨444034369210049261745504151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 592045825613399015660672201 444034369210049261745504151)
        ·
          refine ⟨666051553815073892618256227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 444034369210049261745504151 666051553815073892618256227)
          ·
            refine ⟨999077330722610838927384341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 666051553815073892618256227 999077330722610838927384341)
            ·
              refine ⟨46831749877622383074721141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 999077330722610838927384341 46831749877622383074721141)
              ·
                refine ⟨4390476551027098413255107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 46831749877622383074721141 4390476551027098413255107)
                ·
                  refine ⟨6585714826540647619882661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4390476551027098413255107 6585714826540647619882661)
                  ·
                    refine ⟨1234821529976371428727999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6585714826540647619882661 1234821529976371428727999)
                    ·
                      rfl

theorem cell23_7214419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 6, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 6, 5, 1, 4].length) (baseStart_7214419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7214419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7214419 prefixEnd_7214419 := by exact prefixLift 7214419
  have htrace : WordTrace (prefixWord ++ tailWord_7214419) baseStart_7214419 baseEnd_7214419 := by
    simpa [prefixWord, tailWord_7214419, baseEnd_7214419] using wordTrace_append hprefix tailTrace_7214419
  have hstable : (prefixWord ++ tailWord_7214419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7214419).length < 2 ^ (prefixWord ++ tailWord_7214419).sum := by decide
  have hdescent : baseEnd_7214419 < baseStart_7214419 := by decide
  rcases family_descends (prefixWord ++ tailWord_7214419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7214432 : List Nat := [2, 1, 1, 3, 4, 1, 1, 4, 6]
def baseStart_7214432 : Nat := 118140960795 + 7214432 * 2 ^ 59
def prefixEnd_7214432 : Nat := 4983230072969 + 3 ^ 40 * 7214432 * 2
def baseEnd_7214432 : Nat := 411607918353069192813493

theorem tailTrace_7214432 : CollatzResearch.WordTrace tailWord_7214432 prefixEnd_7214432 411607918353069192813493 := by
  unfold tailWord_7214432
  simp only [CollatzResearch.WordTrace]
  refine ⟨131565976099676232868038775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175421301466234977157385033 131565976099676232868038775)
  ·
    refine ⟨197348964149514349302058163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131565976099676232868038775 197348964149514349302058163)
    ·
      refine ⟨296023446224271523953087245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197348964149514349302058163 296023446224271523953087245)
      ·
        refine ⟨111008792334101821482407717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 296023446224271523953087245 111008792334101821482407717)
        ·
          refine ⟨20814148562644091527951447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 111008792334101821482407717 20814148562644091527951447)
          ·
            refine ⟨31221222843966137291927171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20814148562644091527951447 31221222843966137291927171)
            ·
              refine ⟨46831834265949205937890757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31221222843966137291927171 46831834265949205937890757)
              ·
                refine ⟨8780968924865476113354517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46831834265949205937890757 8780968924865476113354517)
                ·
                  refine ⟨411607918353069192813493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8780968924865476113354517 411607918353069192813493)
                  ·
                    rfl

theorem cell23_7214432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 1, 4, 6].length) (baseStart_7214432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7214432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7214432 prefixEnd_7214432 := by exact prefixLift 7214432
  have htrace : WordTrace (prefixWord ++ tailWord_7214432) baseStart_7214432 baseEnd_7214432 := by
    simpa [prefixWord, tailWord_7214432, baseEnd_7214432] using wordTrace_append hprefix tailTrace_7214432
  have hstable : (prefixWord ++ tailWord_7214432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7214432).length < 2 ^ (prefixWord ++ tailWord_7214432).sum := by decide
  have hdescent : baseEnd_7214432 < baseStart_7214432 := by decide
  rcases family_descends (prefixWord ++ tailWord_7214432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7214436 : List Nat := [2, 3, 1, 1, 3, 3, 1, 4, 1, 4]
def baseStart_7214436 : Nat := 118140960795 + 7214436 * 2 ^ 59
def prefixEnd_7214436 : Nat := 4983230072969 + 3 ^ 40 * 7214436 * 2
def baseEnd_7214436 : Nat := 1234824439700080239890473

theorem tailTrace_7214436 : CollatzResearch.WordTrace tailWord_7214436 prefixEnd_7214436 1234824439700080239890473 := by
  unfold tailWord_7214436
  simp only [CollatzResearch.WordTrace]
  refine ⟨131566049045668987209611581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175421398727558649612815441 131566049045668987209611581)
  ·
    refine ⟨49337268392125870203604343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 131566049045668987209611581 49337268392125870203604343)
    ·
      refine ⟨74005902588188805305406515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49337268392125870203604343 74005902588188805305406515)
      ·
        refine ⟨111008853882283207958109773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74005902588188805305406515 111008853882283207958109773)
        ·
          refine ⟨41628320205856202984291165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 111008853882283207958109773 41628320205856202984291165)
          ·
            refine ⟨15610620077196076119109187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41628320205856202984291165 15610620077196076119109187)
            ·
              refine ⟨23415930115794114178663781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15610620077196076119109187 23415930115794114178663781)
              ·
                refine ⟨4390486896711396408499459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23415930115794114178663781 4390486896711396408499459)
                ·
                  refine ⟨6585730345067094612749189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4390486896711396408499459 6585730345067094612749189)
                  ·
                    refine ⟨1234824439700080239890473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6585730345067094612749189 1234824439700080239890473)
                    ·
                      rfl

theorem cell23_7214436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 1, 4, 1, 4].length) (baseStart_7214436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7214436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7214436 prefixEnd_7214436 := by exact prefixLift 7214436
  have htrace : WordTrace (prefixWord ++ tailWord_7214436) baseStart_7214436 baseEnd_7214436 := by
    simpa [prefixWord, tailWord_7214436, baseEnd_7214436] using wordTrace_append hprefix tailTrace_7214436
  have hstable : (prefixWord ++ tailWord_7214436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7214436).length < 2 ^ (prefixWord ++ tailWord_7214436).sum := by decide
  have hdescent : baseEnd_7214436 < baseStart_7214436 := by decide
  rcases family_descends (prefixWord ++ tailWord_7214436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7214455 : List Nat := [1, 1, 3, 1, 1, 2, 3, 1, 2, 1, 7]
def baseStart_7214455 : Nat := 118140960795 + 7214455 * 2 ^ 59
def prefixEnd_7214455 : Nat := 4983230072969 + 3 ^ 40 * 7214455 * 2
def baseEnd_7214455 : Nat := 3704483075232676145333831

theorem tailTrace_7214455 : CollatzResearch.WordTrace tailWord_7214455 prefixEnd_7214455 3704483075232676145333831 := by
  unfold tailWord_7214455
  simp only [CollatzResearch.WordTrace]
  refine ⟨263132791078269140664164819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175421860718846093776109879 263132791078269140664164819)
  ·
    refine ⟨394699186617403710996247229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263132791078269140664164819 394699186617403710996247229)
    ·
      refine ⟨148012194981526391623592711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 394699186617403710996247229 148012194981526391623592711)
      ·
        refine ⟨222018292472289587435389067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148012194981526391623592711 222018292472289587435389067)
        ·
          refine ⟨333027438708434381153083601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 222018292472289587435389067 333027438708434381153083601)
          ·
            refine ⟨249770579031325785864812701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 333027438708434381153083601 249770579031325785864812701)
            ·
              refine ⟨93663967136747169699304763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 249770579031325785864812701 93663967136747169699304763)
              ·
                refine ⟨140495950705120754548957145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 93663967136747169699304763 140495950705120754548957145)
                ·
                  refine ⟨105371963028840565911717859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 140495950705120754548957145 105371963028840565911717859)
                  ·
                    refine ⟨158057944543260848867576789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 105371963028840565911717859 158057944543260848867576789)
                    ·
                      refine ⟨3704483075232676145333831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 158057944543260848867576789 3704483075232676145333831)
                      ·
                        rfl

theorem cell23_7214455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 1, 2, 1, 7].length) (baseStart_7214455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7214455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7214455 prefixEnd_7214455 := by exact prefixLift 7214455
  have htrace : WordTrace (prefixWord ++ tailWord_7214455) baseStart_7214455 baseEnd_7214455 := by
    simpa [prefixWord, tailWord_7214455, baseEnd_7214455] using wordTrace_append hprefix tailTrace_7214455
  have hstable : (prefixWord ++ tailWord_7214455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7214455).length < 2 ^ (prefixWord ++ tailWord_7214455).sum := by decide
  have hdescent : baseEnd_7214455 < baseStart_7214455 := by decide
  rcases family_descends (prefixWord ++ tailWord_7214455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7214459 : List Nat := [1, 1, 1, 1, 1, 6, 3, 2, 3, 1, 3]
def baseStart_7214459 : Nat := 118140960795 + 7214459 * 2 ^ 59
def prefixEnd_7214459 : Nat := 4983230072969 + 3 ^ 40 * 7214459 * 2
def baseEnd_7214459 : Nat := 3704485129155294129683813

theorem tailTrace_7214459 : CollatzResearch.WordTrace tailWord_7214459 prefixEnd_7214459 3704485129155294129683813 := by
  unfold tailWord_7214459
  simp only [CollatzResearch.WordTrace]
  refine ⟨263132936970254649347310431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175421957980169766231540287 263132936970254649347310431)
  ·
    refine ⟨394699405455381974020965647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263132936970254649347310431 394699405455381974020965647)
    ·
      refine ⟨592049108183072961031448471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 394699405455381974020965647 592049108183072961031448471)
      ·
        refine ⟨888073662274609441547172707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 592049108183072961031448471 888073662274609441547172707)
        ·
          refine ⟨1332110493411914162320759061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 888073662274609441547172707 1332110493411914162320759061)
          ·
            refine ⟨62442679378683476358785581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 1332110493411914162320759061 62442679378683476358785581)
            ·
              refine ⟨23416004767006303634544593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62442679378683476358785581 23416004767006303634544593)
              ·
                refine ⟨17562003575254727725908445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23416004767006303634544593 17562003575254727725908445)
                ·
                  refine ⟨6585751340720522897215667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17562003575254727725908445 6585751340720522897215667)
                  ·
                    refine ⟨9878627011080784345823501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6585751340720522897215667 9878627011080784345823501)
                    ·
                      refine ⟨3704485129155294129683813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9878627011080784345823501 3704485129155294129683813)
                      ·
                        rfl

theorem cell23_7214459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 3, 2, 3, 1, 3].length) (baseStart_7214459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7214459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7214459 prefixEnd_7214459 := by exact prefixLift 7214459
  have htrace : WordTrace (prefixWord ++ tailWord_7214459) baseStart_7214459 baseEnd_7214459 := by
    simpa [prefixWord, tailWord_7214459, baseEnd_7214459] using wordTrace_append hprefix tailTrace_7214459
  have hstable : (prefixWord ++ tailWord_7214459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7214459).length < 2 ^ (prefixWord ++ tailWord_7214459).sum := by decide
  have hdescent : baseEnd_7214459 < baseStart_7214459 := by decide
  rcases family_descends (prefixWord ++ tailWord_7214459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7214493 : List Nat := [1, 4, 2, 1, 3, 1, 2, 4, 1, 1, 3]
def baseStart_7214493 : Nat := 118140960795 + 7214493 * 2 ^ 59
def prefixEnd_7214493 : Nat := 4983230072969 + 3 ^ 40 * 7214493 * 2
def baseEnd_7214493 : Nat := 3704502587497546996658657

theorem tailTrace_7214493 : CollatzResearch.WordTrace tailWord_7214493 prefixEnd_7214493 3704502587497546996658657 := by
  unfold tailWord_7214493
  simp only [CollatzResearch.WordTrace]
  refine ⟨263134177052131473154048133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175422784701420982102698755 263134177052131473154048133)
  ·
    refine ⟨49337658197274651216384025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 263134177052131473154048133 49337658197274651216384025)
    ·
      refine ⟨37003243647955988412288019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49337658197274651216384025 37003243647955988412288019)
      ·
        refine ⟨55504865471933982618432029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37003243647955988412288019 55504865471933982618432029)
        ·
          refine ⟨20814324551975243481912011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55504865471933982618432029 20814324551975243481912011)
          ·
            refine ⟨31221486827962865222868017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20814324551975243481912011 31221486827962865222868017)
            ·
              refine ⟨23416115120972148917151013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31221486827962865222868017 23416115120972148917151013)
              ·
                refine ⟨4390521585182277921965815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23416115120972148917151013 4390521585182277921965815)
                ·
                  refine ⟨6585782377773416882948723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4390521585182277921965815 6585782377773416882948723)
                  ·
                    refine ⟨9878673566660125324423085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6585782377773416882948723 9878673566660125324423085)
                    ·
                      refine ⟨3704502587497546996658657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9878673566660125324423085 3704502587497546996658657)
                      ·
                        rfl

theorem cell23_7214493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 2, 4, 1, 1, 3].length) (baseStart_7214493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7214493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7214493 prefixEnd_7214493 := by exact prefixLift 7214493
  have htrace : WordTrace (prefixWord ++ tailWord_7214493) baseStart_7214493 baseEnd_7214493 := by
    simpa [prefixWord, tailWord_7214493, baseEnd_7214493] using wordTrace_append hprefix tailTrace_7214493
  have hstable : (prefixWord ++ tailWord_7214493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7214493).length < 2 ^ (prefixWord ++ tailWord_7214493).sum := by decide
  have hdescent : baseEnd_7214493 < baseStart_7214493 := by decide
  rcases family_descends (prefixWord ++ tailWord_7214493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7214512 : List Nat := [2, 1, 1, 1, 2, 1, 1, 7, 1, 2, 4]
def baseStart_7214512 : Nat := 118140960795 + 7214512 * 2 ^ 59
def prefixEnd_7214512 : Nat := 4983230072969 + 3 ^ 40 * 7214512 * 2
def baseEnd_7214512 : Nat := 3704512343629982422321069

theorem tailTrace_7214512 : CollatzResearch.WordTrace tailWord_7214512 prefixEnd_7214512 3704512343629982422321069 := by
  unfold tailWord_7214512
  simp only [CollatzResearch.WordTrace]
  refine ⟨131567435019531319699494895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175423246692708426265993193 131567435019531319699494895)
  ·
    refine ⟨197351152529296979549242343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131567435019531319699494895 197351152529296979549242343)
    ·
      refine ⟨296026728793945469323863515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197351152529296979549242343 296026728793945469323863515)
      ·
        refine ⟨444040093190918203985795273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 296026728793945469323863515 444040093190918203985795273)
        ·
          refine ⟨333030069893188652989346455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 444040093190918203985795273 333030069893188652989346455)
          ·
            refine ⟨499545104839782979484019683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 333030069893188652989346455 499545104839782979484019683)
            ·
              refine ⟨749317657259674469226029525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 499545104839782979484019683 749317657259674469226029525)
              ·
                refine ⟨17562132592023620372485067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 749317657259674469226029525 17562132592023620372485067)
                ·
                  refine ⟨26343198888035430558727601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17562132592023620372485067 26343198888035430558727601)
                  ·
                    refine ⟨19757399166026572919045701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26343198888035430558727601 19757399166026572919045701)
                    ·
                      refine ⟨3704512343629982422321069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19757399166026572919045701 3704512343629982422321069)
                      ·
                        rfl

theorem cell23_7214512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 7, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 7, 1, 2, 4].length) (baseStart_7214512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7214512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7214512 prefixEnd_7214512 := by exact prefixLift 7214512
  have htrace : WordTrace (prefixWord ++ tailWord_7214512) baseStart_7214512 baseEnd_7214512 := by
    simpa [prefixWord, tailWord_7214512, baseEnd_7214512] using wordTrace_append hprefix tailTrace_7214512
  have hstable : (prefixWord ++ tailWord_7214512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7214512).length < 2 ^ (prefixWord ++ tailWord_7214512).sum := by decide
  have hdescent : baseEnd_7214512 < baseStart_7214512 := by decide
  rcases family_descends (prefixWord ++ tailWord_7214512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7214550 : List Nat := [5, 2, 1, 1, 1, 2, 3, 1, 3, 2, 2]
def baseStart_7214550 : Nat := 118140960795 + 7214550 * 2 ^ 59
def prefixEnd_7214550 : Nat := 4983230072969 + 3 ^ 40 * 7214550 * 2
def baseEnd_7214550 : Nat := 3704531855894853273645895

theorem tailTrace_7214550 : CollatzResearch.WordTrace tailWord_7214550 prefixEnd_7214550 3704531855894853273645895 := by
  unfold tailWord_7214550
  simp only [CollatzResearch.WordTrace]
  refine ⟨16446016000807810743054569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 175424170675283314592582069 16446016000807810743054569)
  ·
    refine ⟨12334512000605858057290927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16446016000807810743054569 12334512000605858057290927)
    ·
      refine ⟨18501768000908787085936391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12334512000605858057290927 18501768000908787085936391)
      ·
        refine ⟨27752652001363180628904587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18501768000908787085936391 27752652001363180628904587)
        ·
          refine ⟨41628978002044770943356881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27752652001363180628904587 41628978002044770943356881)
          ·
            refine ⟨31221733501533578207517661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41628978002044770943356881 31221733501533578207517661)
            ·
              refine ⟨11708150063075091827819123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31221733501533578207517661 11708150063075091827819123)
              ·
                refine ⟨17562225094612637741728685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11708150063075091827819123 17562225094612637741728685)
                ·
                  refine ⟨6585834410479739153148257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17562225094612637741728685 6585834410479739153148257)
                  ·
                    refine ⟨4939375807859804364861193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6585834410479739153148257 4939375807859804364861193)
                    ·
                      refine ⟨3704531855894853273645895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4939375807859804364861193 3704531855894853273645895)
                      ·
                        rfl

theorem cell23_7214550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 3, 1, 3, 2, 2].length) (baseStart_7214550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7214550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7214550 prefixEnd_7214550 := by exact prefixLift 7214550
  have htrace : WordTrace (prefixWord ++ tailWord_7214550) baseStart_7214550 baseEnd_7214550 := by
    simpa [prefixWord, tailWord_7214550, baseEnd_7214550] using wordTrace_append hprefix tailTrace_7214550
  have hstable : (prefixWord ++ tailWord_7214550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7214550).length < 2 ^ (prefixWord ++ tailWord_7214550).sum := by decide
  have hdescent : baseEnd_7214550 < baseStart_7214550 := by decide
  rcases family_descends (prefixWord ++ tailWord_7214550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7214570 : List Nat := [3, 1, 3, 1, 5, 1, 1, 2, 1, 2, 3]
def baseStart_7214570 : Nat := 118140960795 + 7214570 * 2 ^ 59
def prefixEnd_7214570 : Nat := 4983230072969 + 3 ^ 40 * 7214570 * 2
def baseEnd_7214570 : Nat := 3704542125507943195395803

theorem tailTrace_7214570 : CollatzResearch.WordTrace tailWord_7214570 prefixEnd_7214570 3704542125507943195395803 := by
  unfold tailWord_7214570
  simp only [CollatzResearch.WordTrace]
  refine ⟨65784246368213128826150291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175424656981901676869734109 65784246368213128826150291)
  ·
    refine ⟨98676369552319693239225437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65784246368213128826150291 98676369552319693239225437)
    ·
      refine ⟨37003638582119884964709539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98676369552319693239225437 37003638582119884964709539)
      ·
        refine ⟨55505457873179827447064309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37003638582119884964709539 55505457873179827447064309)
        ·
          refine ⟨5203636675610608823162279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 55505457873179827447064309 5203636675610608823162279)
          ·
            refine ⟨7805455013415913234743419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5203636675610608823162279 7805455013415913234743419)
            ·
              refine ⟨11708182520123869852115129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7805455013415913234743419 11708182520123869852115129)
              ·
                refine ⟨8781136890092902389086347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11708182520123869852115129 8781136890092902389086347)
                ·
                  refine ⟨13171705335139353583629521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8781136890092902389086347 13171705335139353583629521)
                  ·
                    refine ⟨9878779001354515187722141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13171705335139353583629521 9878779001354515187722141)
                    ·
                      refine ⟨3704542125507943195395803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9878779001354515187722141 3704542125507943195395803)
                      ·
                        rfl

theorem cell23_7214570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 5, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 5, 1, 1, 2, 1, 2, 3].length) (baseStart_7214570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7214570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7214570 prefixEnd_7214570 := by exact prefixLift 7214570
  have htrace : WordTrace (prefixWord ++ tailWord_7214570) baseStart_7214570 baseEnd_7214570 := by
    simpa [prefixWord, tailWord_7214570, baseEnd_7214570] using wordTrace_append hprefix tailTrace_7214570
  have hstable : (prefixWord ++ tailWord_7214570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7214570).length < 2 ^ (prefixWord ++ tailWord_7214570).sum := by decide
  have hdescent : baseEnd_7214570 < baseStart_7214570 := by decide
  rcases family_descends (prefixWord ++ tailWord_7214570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7214572 : List Nat := [2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 4]
def baseStart_7214572 : Nat := 118140960795 + 7214572 * 2 ^ 59
def prefixEnd_7214572 : Nat := 4983230072969 + 3 ^ 40 * 7214572 * 2
def baseEnd_7214572 : Nat := 3704543152469252187570793

theorem tailTrace_7214572 : CollatzResearch.WordTrace tailWord_7214572 prefixEnd_7214572 3704543152469252187570793 := by
  unfold tailWord_7214572
  simp only [CollatzResearch.WordTrace]
  refine ⟨131568529209422634823086985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175424705612563513097449313 131568529209422634823086985)
  ·
    refine ⟨98676396907066976117315239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131568529209422634823086985 98676396907066976117315239)
    ·
      refine ⟨148014595360600464175972859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98676396907066976117315239 148014595360600464175972859)
      ·
        refine ⟨222021893040900696263959289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148014595360600464175972859 222021893040900696263959289)
        ·
          refine ⟨166516419780675522197969467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 222021893040900696263959289 166516419780675522197969467)
          ·
            refine ⟨249774629671013283296954201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 166516419780675522197969467 249774629671013283296954201)
            ·
              refine ⟨187330972253259962472715651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 249774629671013283296954201 187330972253259962472715651)
              ·
                refine ⟨280996458379889943709073477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 187330972253259962472715651 280996458379889943709073477)
                ·
                  refine ⟨52686835946229364445451277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 280996458379889943709073477 52686835946229364445451277)
                  ·
                    refine ⟨19757563479836011667044229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 52686835946229364445451277 19757563479836011667044229)
                    ·
                      refine ⟨3704543152469252187570793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19757563479836011667044229 3704543152469252187570793)
                      ·
                        rfl

theorem cell23_7214572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 4].length) (baseStart_7214572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7214572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7214572 prefixEnd_7214572 := by exact prefixLift 7214572
  have htrace : WordTrace (prefixWord ++ tailWord_7214572) baseStart_7214572 baseEnd_7214572 := by
    simpa [prefixWord, tailWord_7214572, baseEnd_7214572] using wordTrace_append hprefix tailTrace_7214572
  have hstable : (prefixWord ++ tailWord_7214572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7214572).length < 2 ^ (prefixWord ++ tailWord_7214572).sum := by decide
  have hdescent : baseEnd_7214572 < baseStart_7214572 := by decide
  rcases family_descends (prefixWord ++ tailWord_7214572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7214576 : List Nat := [2, 1, 1, 1, 3, 5, 1, 1, 3, 3, 2]
def baseStart_7214576 : Nat := 118140960795 + 7214576 * 2 ^ 59
def prefixEnd_7214576 : Nat := 4983230072969 + 3 ^ 40 * 7214576 * 2
def baseEnd_7214576 : Nat := 3704545206391870171920775

theorem tailTrace_7214576 : CollatzResearch.WordTrace tailWord_7214576 prefixEnd_7214576 3704545206391870171920775 := by
  unfold tailWord_7214576
  simp only [CollatzResearch.WordTrace]
  refine ⟨131568602155415389164659791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175424802873887185552879721 131568602155415389164659791)
  ·
    refine ⟨197352903233123083746989687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131568602155415389164659791 197352903233123083746989687)
    ·
      refine ⟨296029354849684625620484531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197352903233123083746989687 296029354849684625620484531)
      ·
        refine ⟨444044032274526938430726797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 296029354849684625620484531 444044032274526938430726797)
        ·
          refine ⟨166516512102947601911522549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 444044032274526938430726797 166516512102947601911522549)
          ·
            refine ⟨15610923009651337679205239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 166516512102947601911522549 15610923009651337679205239)
            ·
              refine ⟨23416384514477006518807859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15610923009651337679205239 23416384514477006518807859)
              ·
                refine ⟨35124576771715509778211789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23416384514477006518807859 35124576771715509778211789)
                ·
                  refine ⟨13171716289393316166829421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35124576771715509778211789 13171716289393316166829421)
                  ·
                    refine ⟨4939393608522493562561033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13171716289393316166829421 4939393608522493562561033)
                    ·
                      refine ⟨3704545206391870171920775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4939393608522493562561033 3704545206391870171920775)
                      ·
                        rfl

theorem cell23_7214576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 1, 1, 3, 3, 2].length) (baseStart_7214576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7214576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7214576 prefixEnd_7214576 := by exact prefixLift 7214576
  have htrace : WordTrace (prefixWord ++ tailWord_7214576) baseStart_7214576 baseEnd_7214576 := by
    simpa [prefixWord, tailWord_7214576, baseEnd_7214576] using wordTrace_append hprefix tailTrace_7214576
  have hstable : (prefixWord ++ tailWord_7214576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7214576).length < 2 ^ (prefixWord ++ tailWord_7214576).sum := by decide
  have hdescent : baseEnd_7214576 < baseStart_7214576 := by decide
  rcases family_descends (prefixWord ++ tailWord_7214576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7214623 : List Nat := [1, 1, 2, 4, 1, 1, 4, 3, 2, 2, 2]
def baseStart_7214623 : Nat := 118140960795 + 7214623 * 2 ^ 59
def prefixEnd_7214623 : Nat := 4983230072969 + 3 ^ 40 * 7214623 * 2
def baseEnd_7214623 : Nat := 3704569339982631488033059

theorem tailTrace_7214623 : CollatzResearch.WordTrace tailWord_7214623 prefixEnd_7214623 3704569339982631488033059 := by
  unfold tailWord_7214623
  simp only [CollatzResearch.WordTrace]
  refine ⟨263138918541660505356280523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175425945694440336904187015 263138918541660505356280523)
  ·
    refine ⟨394708377812490758034420785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263138918541660505356280523 394708377812490758034420785)
    ·
      refine ⟨296031283359368068525815589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 394708377812490758034420785 296031283359368068525815589)
      ·
        refine ⟨55505865629881512848590423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 296031283359368068525815589 55505865629881512848590423)
        ·
          refine ⟨83258798444822269272885635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55505865629881512848590423 83258798444822269272885635)
          ·
            refine ⟨124888197667233403909328453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83258798444822269272885635 124888197667233403909328453)
            ·
              refine ⟨23416537062606263232999085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 124888197667233403909328453 23416537062606263232999085)
              ·
                refine ⟨8781201398477348712374657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23416537062606263232999085 8781201398477348712374657)
                ·
                  refine ⟨6585901048858011534280993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8781201398477348712374657 6585901048858011534280993)
                  ·
                    refine ⟨4939425786643508650710745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6585901048858011534280993 4939425786643508650710745)
                    ·
                      refine ⟨3704569339982631488033059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4939425786643508650710745 3704569339982631488033059)
                      ·
                        rfl

theorem cell23_7214623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 4, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 4, 3, 2, 2, 2].length) (baseStart_7214623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7214623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7214623 prefixEnd_7214623 := by exact prefixLift 7214623
  have htrace : WordTrace (prefixWord ++ tailWord_7214623) baseStart_7214623 baseEnd_7214623 := by
    simpa [prefixWord, tailWord_7214623, baseEnd_7214623] using wordTrace_append hprefix tailTrace_7214623
  have hstable : (prefixWord ++ tailWord_7214623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7214623).length < 2 ^ (prefixWord ++ tailWord_7214623).sum := by decide
  have hdescent : baseEnd_7214623 < baseStart_7214623 := by decide
  rcases family_descends (prefixWord ++ tailWord_7214623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7214679 : List Nat := [1, 1, 3, 2, 2, 3, 1, 2, 1, 3, 4]
def baseStart_7214679 : Nat := 118140960795 + 7214679 * 2 ^ 59
def prefixEnd_7214679 : Nat := 4983230072969 + 3 ^ 40 * 7214679 * 2
def baseEnd_7214679 : Nat := 3704598094899283268932801

theorem tailTrace_7214679 : CollatzResearch.WordTrace tailWord_7214679 prefixEnd_7214679 3704598094899283268932801 := by
  unfold tailWord_7214679
  simp only [CollatzResearch.WordTrace]
  refine ⟨263140961029457626920319091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175427307352971751280212727 263140961029457626920319091)
  ·
    refine ⟨394711441544186440380478637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263140961029457626920319091 394711441544186440380478637)
    ·
      refine ⟨148016790579069915142679489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 394711441544186440380478637 148016790579069915142679489)
      ·
        refine ⟨111012592934302436357009617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148016790579069915142679489 111012592934302436357009617)
        ·
          refine ⟨83259444700726827267757213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111012592934302436357009617 83259444700726827267757213)
          ·
            refine ⟨31222291762772560225408955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 83259444700726827267757213 31222291762772560225408955)
            ·
              refine ⟨46833437644158840338113433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31222291762772560225408955 46833437644158840338113433)
              ·
                refine ⟨35125078233119130253585075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46833437644158840338113433 35125078233119130253585075)
                ·
                  refine ⟨52687617349678695380377613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35125078233119130253585075 52687617349678695380377613)
                  ·
                    refine ⟨19757856506129510767641605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 52687617349678695380377613 19757856506129510767641605)
                    ·
                      refine ⟨3704598094899283268932801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19757856506129510767641605 3704598094899283268932801)
                      ·
                        rfl

theorem cell23_7214679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 1, 2, 1, 3, 4].length) (baseStart_7214679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7214679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7214679 prefixEnd_7214679 := by exact prefixLift 7214679
  have htrace : WordTrace (prefixWord ++ tailWord_7214679) baseStart_7214679 baseEnd_7214679 := by
    simpa [prefixWord, tailWord_7214679, baseEnd_7214679] using wordTrace_append hprefix tailTrace_7214679
  have hstable : (prefixWord ++ tailWord_7214679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7214679).length < 2 ^ (prefixWord ++ tailWord_7214679).sum := by decide
  have hdescent : baseEnd_7214679 < baseStart_7214679 := by decide
  rcases family_descends (prefixWord ++ tailWord_7214679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7214696 : List Nat := [2, 1, 4, 3, 1, 1, 2, 1, 1, 3, 4]
def baseStart_7214696 : Nat := 118140960795 + 7214696 * 2 ^ 59
def prefixEnd_7214696 : Nat := 4983230072969 + 3 ^ 40 * 7214696 * 2
def baseEnd_7214696 : Nat := 3704606824070409702420223

theorem tailTrace_7214696 : CollatzResearch.WordTrace tailWord_7214696 prefixEnd_7214696 3704606824070409702420223 := by
  unfold tailWord_7214696
  simp only [CollatzResearch.WordTrace]
  refine ⟨131570790535198019411843971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175427720713597359215791961 131570790535198019411843971)
  ·
    refine ⟨197356185802797029117765957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131570790535198019411843971 197356185802797029117765957)
    ·
      refine ⟨37004284838024442959581117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 197356185802797029117765957 37004284838024442959581117)
      ·
        refine ⟨13876606814259166109842919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37004284838024442959581117 13876606814259166109842919)
        ·
          refine ⟨20814910221388749164764379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13876606814259166109842919 20814910221388749164764379)
          ·
            refine ⟨31222365332083123747146569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20814910221388749164764379 31222365332083123747146569)
            ·
              refine ⟨23416773999062342810359927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31222365332083123747146569 23416773999062342810359927)
              ·
                refine ⟨35125160998593514215539891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23416773999062342810359927 35125160998593514215539891)
                ·
                  refine ⟨52687741497890271323309837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35125160998593514215539891 52687741497890271323309837)
                  ·
                    refine ⟨19757903061708851746241189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 52687741497890271323309837 19757903061708851746241189)
                    ·
                      refine ⟨3704606824070409702420223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19757903061708851746241189 3704606824070409702420223)
                      ·
                        rfl

theorem cell23_7214696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 2, 1, 1, 3, 4].length) (baseStart_7214696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7214696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7214696 prefixEnd_7214696 := by exact prefixLift 7214696
  have htrace : WordTrace (prefixWord ++ tailWord_7214696) baseStart_7214696 baseEnd_7214696 := by
    simpa [prefixWord, tailWord_7214696, baseEnd_7214696] using wordTrace_append hprefix tailTrace_7214696
  have hstable : (prefixWord ++ tailWord_7214696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7214696).length < 2 ^ (prefixWord ++ tailWord_7214696).sum := by decide
  have hdescent : baseEnd_7214696 < baseStart_7214696 := by decide
  rcases family_descends (prefixWord ++ tailWord_7214696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7214750 : List Nat := [4, 3, 1, 1, 1, 3, 2, 1, 2, 2, 3]
def baseStart_7214750 : Nat := 118140960795 + 7214750 * 2 ^ 59
def prefixEnd_7214750 : Nat := 4983230072969 + 3 ^ 40 * 7214750 * 2
def baseEnd_7214750 : Nat := 3704634552025752491144975

theorem tailTrace_7214750 : CollatzResearch.WordTrace tailWord_7214750 prefixEnd_7214750 3704634552025752491144975 := by
  unfold tailWord_7214750
  simp only [CollatzResearch.WordTrace]
  refine ⟨32892943826525050755769213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 175429033741466937364102469 32892943826525050755769213)
  ·
    refine ⟨12334853934946894033413455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32892943826525050755769213 12334853934946894033413455)
    ·
      refine ⟨18502280902420341050120183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12334853934946894033413455 18502280902420341050120183)
      ·
        refine ⟨27753421353630511575180275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18502280902420341050120183 27753421353630511575180275)
        ·
          refine ⟨41630132030445767362770413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27753421353630511575180275 41630132030445767362770413)
          ·
            refine ⟨15611299511417162761038905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41630132030445767362770413 15611299511417162761038905)
            ·
              refine ⟨11708474633562872070779179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15611299511417162761038905 11708474633562872070779179)
              ·
                refine ⟨17562711950344308106168769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11708474633562872070779179 17562711950344308106168769)
                ·
                  refine ⟨13172033962758231079626577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17562711950344308106168769 13172033962758231079626577)
                  ·
                    refine ⟨9879025472068673309719933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13172033962758231079626577 9879025472068673309719933)
                    ·
                      refine ⟨3704634552025752491144975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9879025472068673309719933 3704634552025752491144975)
                      ·
                        rfl

theorem cell23_7214750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 2, 1, 2, 2, 3].length) (baseStart_7214750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7214750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7214750 prefixEnd_7214750 := by exact prefixLift 7214750
  have htrace : WordTrace (prefixWord ++ tailWord_7214750) baseStart_7214750 baseEnd_7214750 := by
    simpa [prefixWord, tailWord_7214750, baseEnd_7214750] using wordTrace_append hprefix tailTrace_7214750
  have hstable : (prefixWord ++ tailWord_7214750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7214750).length < 2 ^ (prefixWord ++ tailWord_7214750).sum := by decide
  have hdescent : baseEnd_7214750 < baseStart_7214750 := by decide
  rcases family_descends (prefixWord ++ tailWord_7214750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7214774 : List Nat := [5, 1, 3, 1, 1, 1, 4, 2, 1, 4]
def baseStart_7214774 : Nat := 118140960795 + 7214774 * 2 ^ 59
def prefixEnd_7214774 : Nat := 4983230072969 + 3 ^ 40 * 7214774 * 2
def baseEnd_7214774 : Nat := 1234882291853820132414955

theorem tailTrace_7214774 : CollatzResearch.WordTrace tailWord_7214774 prefixEnd_7214774 1234882291853820132414955 := by
  unfold tailWord_7214774
  simp only [CollatzResearch.WordTrace]
  refine ⟨16446526622757091134064211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 175429617309408972096684917 16446526622757091134064211)
  ·
    refine ⟨24669789934135636701096317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16446526622757091134064211 24669789934135636701096317)
    ·
      refine ⟨9251171225300863762911119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24669789934135636701096317 9251171225300863762911119)
      ·
        refine ⟨13876756837951295644366679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9251171225300863762911119 13876756837951295644366679)
        ·
          refine ⟨20815135256926943466550019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13876756837951295644366679 20815135256926943466550019)
          ·
            refine ⟨31222702885390415199825029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20815135256926943466550019 31222702885390415199825029)
            ·
              refine ⟨5854256791010702849967193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31222702885390415199825029 5854256791010702849967193)
              ·
                refine ⟨4390692593258027137475395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5854256791010702849967193 4390692593258027137475395)
                ·
                  refine ⟨6586038889887040706213093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4390692593258027137475395 6586038889887040706213093)
                  ·
                    refine ⟨1234882291853820132414955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6586038889887040706213093 1234882291853820132414955)
                    ·
                      rfl

theorem cell23_7214774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 4, 2, 1, 4].length) (baseStart_7214774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7214774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7214774 prefixEnd_7214774 := by exact prefixLift 7214774
  have htrace : WordTrace (prefixWord ++ tailWord_7214774) baseStart_7214774 baseEnd_7214774 := by
    simpa [prefixWord, tailWord_7214774, baseEnd_7214774] using wordTrace_append hprefix tailTrace_7214774
  have hstable : (prefixWord ++ tailWord_7214774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7214774).length < 2 ^ (prefixWord ++ tailWord_7214774).sum := by decide
  have hdescent : baseEnd_7214774 < baseStart_7214774 := by decide
  rcases family_descends (prefixWord ++ tailWord_7214774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7214797 : List Nat := [1, 6, 2, 1, 1, 2, 1, 2, 3, 1, 3]
def baseStart_7214797 : Nat := 118140960795 + 7214797 * 2 ^ 59
def prefixEnd_7214797 : Nat := 4983230072969 + 3 ^ 40 * 7214797 * 2
def baseEnd_7214797 : Nat := 3704658685616513807257259

theorem tailTrace_7214797 : CollatzResearch.WordTrace tailWord_7214797 prefixEnd_7214797 3704658685616513807257259 := by
  unfold tailWord_7214797
  simp only [CollatzResearch.WordTrace]
  refine ⟨263145264843030133073114645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175430176562020088715409763 263145264843030133073114645)
  ·
    refine ⟨12334934289517037487802249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 263145264843030133073114645 12334934289517037487802249)
    ·
      refine ⟨9251200717137778115851687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12334934289517037487802249 9251200717137778115851687)
      ·
        refine ⟨13876801075706667173777531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9251200717137778115851687 13876801075706667173777531)
        ·
          refine ⟨20815201613560000760666297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13876801075706667173777531 20815201613560000760666297)
          ·
            refine ⟨15611401210170000570499723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20815201613560000760666297 15611401210170000570499723)
            ·
              refine ⟨23417101815255000855749585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15611401210170000570499723 23417101815255000855749585)
              ·
                refine ⟨17562826361441250641812189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23417101815255000855749585 17562826361441250641812189)
                ·
                  refine ⟨6586059885540468990679571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17562826361441250641812189 6586059885540468990679571)
                  ·
                    refine ⟨9879089828310703486019357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6586059885540468990679571 9879089828310703486019357)
                    ·
                      refine ⟨3704658685616513807257259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9879089828310703486019357 3704658685616513807257259)
                      ·
                        rfl

theorem cell23_7214797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 1, 2, 3, 1, 3].length) (baseStart_7214797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7214797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7214797 prefixEnd_7214797 := by exact prefixLift 7214797
  have htrace : WordTrace (prefixWord ++ tailWord_7214797) baseStart_7214797 baseEnd_7214797 := by
    simpa [prefixWord, tailWord_7214797, baseEnd_7214797] using wordTrace_append hprefix tailTrace_7214797
  have hstable : (prefixWord ++ tailWord_7214797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7214797).length < 2 ^ (prefixWord ++ tailWord_7214797).sum := by decide
  have hdescent : baseEnd_7214797 < baseStart_7214797 := by decide
  rcases family_descends (prefixWord ++ tailWord_7214797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7214799 : List Nat := [1, 1, 2, 1, 1, 3, 1, 5, 1, 1, 6]
def baseStart_7214799 : Nat := 118140960795 + 7214799 * 2 ^ 59
def prefixEnd_7214799 : Nat := 4983230072969 + 3 ^ 40 * 7214799 * 2
def baseEnd_7214799 : Nat := 3704659712577822799432249

theorem tailTrace_7214799 : CollatzResearch.WordTrace tailWord_7214799 prefixEnd_7214799 3704659712577822799432249 := by
  unfold tailWord_7214799
  simp only [CollatzResearch.WordTrace]
  refine ⟨263145337789022887414687451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175430225192681924943124967 263145337789022887414687451)
  ·
    refine ⟨394718006683534331122031177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263145337789022887414687451 394718006683534331122031177)
    ·
      refine ⟨296038505012650748341523383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 394718006683534331122031177 296038505012650748341523383)
      ·
        refine ⟨444057757518976122512285075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 296038505012650748341523383 444057757518976122512285075)
        ·
          refine ⟨666086636278464183768427613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 444057757518976122512285075 666086636278464183768427613)
          ·
            refine ⟨249782488604424068913160355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 666086636278464183768427613 249782488604424068913160355)
            ·
              refine ⟨374673732906636103369740533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 249782488604424068913160355 374673732906636103369740533)
              ·
                refine ⟨35125662459997134690913175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 374673732906636103369740533 35125662459997134690913175)
                ·
                  refine ⟨52688493689995702036369763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35125662459997134690913175 52688493689995702036369763)
                  ·
                    refine ⟨79032740534993553054554645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 52688493689995702036369763 79032740534993553054554645)
                    ·
                      refine ⟨3704659712577822799432249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 79032740534993553054554645 3704659712577822799432249)
                      ·
                        rfl

theorem cell23_7214799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 5, 1, 1, 6].length) (baseStart_7214799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7214799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7214799 prefixEnd_7214799 := by exact prefixLift 7214799
  have htrace : WordTrace (prefixWord ++ tailWord_7214799) baseStart_7214799 baseEnd_7214799 := by
    simpa [prefixWord, tailWord_7214799, baseEnd_7214799] using wordTrace_append hprefix tailTrace_7214799
  have hstable : (prefixWord ++ tailWord_7214799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7214799).length < 2 ^ (prefixWord ++ tailWord_7214799).sum := by decide
  have hdescent : baseEnd_7214799 < baseStart_7214799 := by decide
  rcases family_descends (prefixWord ++ tailWord_7214799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7214816 : List Nat := [2, 1, 1, 3, 1, 2, 4, 2, 1, 2, 4]
def baseStart_7214816 : Nat := 118140960795 + 7214816 * 2 ^ 59
def prefixEnd_7214816 : Nat := 4983230072969 + 3 ^ 40 * 7214816 * 2
def baseEnd_7214816 : Nat := 3704668441748949232919671

theorem tailTrace_7214816 : CollatzResearch.WordTrace tailWord_7214816 prefixEnd_7214816 3704668441748949232919671 := by
  unfold tailWord_7214816
  simp only [CollatzResearch.WordTrace]
  refine ⟨131572978914980649659028151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175430638553307532878704201 131572978914980649659028151)
  ·
    refine ⟨197359468372470974488542227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131572978914980649659028151 197359468372470974488542227)
    ·
      refine ⟨296039202558706461732813341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197359468372470974488542227 296039202558706461732813341)
      ·
        refine ⟨111014700959514923149805003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 296039202558706461732813341 111014700959514923149805003)
        ·
          refine ⟨166522051439272384724707505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111014700959514923149805003 166522051439272384724707505)
          ·
            refine ⟨124891538579454288543530629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 166522051439272384724707505 124891538579454288543530629)
            ·
              refine ⟨23417163483647679101911993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 124891538579454288543530629 23417163483647679101911993)
              ·
                refine ⟨17562872612735759326433995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23417163483647679101911993 17562872612735759326433995)
                ·
                  refine ⟨26344308919103638989650993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17562872612735759326433995 26344308919103638989650993)
                  ·
                    refine ⟨19758231689327729242238245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26344308919103638989650993 19758231689327729242238245)
                    ·
                      refine ⟨3704668441748949232919671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19758231689327729242238245 3704668441748949232919671)
                      ·
                        rfl

theorem cell23_7214816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 4, 2, 1, 2, 4].length) (baseStart_7214816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7214816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7214816 prefixEnd_7214816 := by exact prefixLift 7214816
  have htrace : WordTrace (prefixWord ++ tailWord_7214816) baseStart_7214816 baseEnd_7214816 := by
    simpa [prefixWord, tailWord_7214816, baseEnd_7214816] using wordTrace_append hprefix tailTrace_7214816
  have hstable : (prefixWord ++ tailWord_7214816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7214816).length < 2 ^ (prefixWord ++ tailWord_7214816).sum := by decide
  have hdescent : baseEnd_7214816 < baseStart_7214816 := by decide
  rcases family_descends (prefixWord ++ tailWord_7214816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7214817 : List Nat := [1, 2, 3, 1, 6, 1, 2, 1, 1, 5]
def baseStart_7214817 : Nat := 118140960795 + 7214817 * 2 ^ 59
def prefixEnd_7214817 : Nat := 4983230072969 + 3 ^ 40 * 7214817 * 2
def baseEnd_7214817 : Nat := 1234889651743201243002389

theorem tailTrace_7214817 : CollatzResearch.WordTrace tailWord_7214817 prefixEnd_7214817 1234889651743201243002389 := by
  unfold tailWord_7214817
  simp only [CollatzResearch.WordTrace]
  refine ⟨263145994302957676488842705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175430662868638450992561803 263145994302957676488842705)
  ·
    refine ⟨197359495727218257366632029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 263145994302957676488842705 197359495727218257366632029)
    ·
      refine ⟨74009810897706846512487011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 197359495727218257366632029 74009810897706846512487011)
      ·
        refine ⟨111014716346560269768730517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74009810897706846512487011 111014716346560269768730517)
        ·
          refine ⟨5203814828745012645409243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 111014716346560269768730517 5203814828745012645409243)
          ·
            refine ⟨7805722243117518968113865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5203814828745012645409243 7805722243117518968113865)
            ·
              refine ⟨5854291682338139226085399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7805722243117518968113865 5854291682338139226085399)
              ·
                refine ⟨8781437523507208839128099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5854291682338139226085399 8781437523507208839128099)
                ·
                  refine ⟨13172156285260813258692149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8781437523507208839128099 13172156285260813258692149)
                  ·
                    refine ⟨1234889651743201243002389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13172156285260813258692149 1234889651743201243002389)
                    ·
                      rfl

theorem cell23_7214817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 6, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 6, 1, 2, 1, 1, 5].length) (baseStart_7214817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7214817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7214817 prefixEnd_7214817 := by exact prefixLift 7214817
  have htrace : WordTrace (prefixWord ++ tailWord_7214817) baseStart_7214817 baseEnd_7214817 := by
    simpa [prefixWord, tailWord_7214817, baseEnd_7214817] using wordTrace_append hprefix tailTrace_7214817
  have hstable : (prefixWord ++ tailWord_7214817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7214817).length < 2 ^ (prefixWord ++ tailWord_7214817).sum := by decide
  have hdescent : baseEnd_7214817 < baseStart_7214817 := by decide
  rcases family_descends (prefixWord ++ tailWord_7214817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7214839 : List Nat := [1, 1, 3, 1, 1, 1, 4, 1, 1, 9]
def baseStart_7214839 : Nat := 118140960795 + 7214839 * 2 ^ 59
def prefixEnd_7214839 : Nat := 4983230072969 + 3 ^ 40 * 7214839 * 2
def baseEnd_7214839 : Nat := 1234893417268000880977355

theorem tailTrace_7214839 : CollatzResearch.WordTrace tailWord_7214839 prefixEnd_7214839 1234893417268000880977355 := by
  unfold tailWord_7214839
  simp only [CollatzResearch.WordTrace]
  refine ⟨263146796708877974246143571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175431197805918649497429047 263146796708877974246143571)
  ·
    refine ⟨394720195063316961369215357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263146796708877974246143571 394720195063316961369215357)
    ·
      refine ⟨148020073148743860513455759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 394720195063316961369215357 148020073148743860513455759)
      ·
        refine ⟨222030109723115790770183639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148020073148743860513455759 222030109723115790770183639)
        ·
          refine ⟨333045164584673686155275459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 222030109723115790770183639 333045164584673686155275459)
          ·
            refine ⟨499567746877010529232913189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 333045164584673686155275459 499567746877010529232913189)
            ·
              refine ⟨93668952539439474231171223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 499567746877010529232913189 93668952539439474231171223)
              ·
                refine ⟨140503428809159211346756835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 93668952539439474231171223 140503428809159211346756835)
                ·
                  refine ⟨210755143213738817020135253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 140503428809159211346756835 210755143213738817020135253)
                  ·
                    refine ⟨1234893417268000880977355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 210755143213738817020135253 1234893417268000880977355)
                    ·
                      rfl

theorem cell23_7214839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 1, 1, 9].length) (baseStart_7214839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7214839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7214839 prefixEnd_7214839 := by exact prefixLift 7214839
  have htrace : WordTrace (prefixWord ++ tailWord_7214839) baseStart_7214839 baseEnd_7214839 := by
    simpa [prefixWord, tailWord_7214839, baseEnd_7214839] using wordTrace_append hprefix tailTrace_7214839
  have hstable : (prefixWord ++ tailWord_7214839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7214839).length < 2 ^ (prefixWord ++ tailWord_7214839).sum := by decide
  have hdescent : baseEnd_7214839 < baseStart_7214839 := by decide
  rcases family_descends (prefixWord ++ tailWord_7214839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7214880 : List Nat := [2, 1, 1, 5, 1, 1, 1, 5, 1, 3, 2]
def baseStart_7214880 : Nat := 118140960795 + 7214880 * 2 ^ 59
def prefixEnd_7214880 : Nat := 4983230072969 + 3 ^ 40 * 7214880 * 2
def baseEnd_7214880 : Nat := 3704701304510836982519377

theorem tailTrace_7214880 : CollatzResearch.WordTrace tailWord_7214880 prefixEnd_7214880 3704701304510836982519377 := by
  unfold tailWord_7214880
  simp only [CollatzResearch.WordTrace]
  refine ⟨131574146050864719124193047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175432194734486292165590729 131574146050864719124193047)
  ·
    refine ⟨197361219076297078686289571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131574146050864719124193047 197361219076297078686289571)
    ·
      refine ⟨296041828614445618029434357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197361219076297078686289571 296041828614445618029434357)
      ·
        refine ⟨27753921432604276690259471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 296041828614445618029434357 27753921432604276690259471)
        ·
          refine ⟨41630882148906415035389207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27753921432604276690259471 41630882148906415035389207)
          ·
            refine ⟨62446323223359622553083811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41630882148906415035389207 62446323223359622553083811)
            ·
              refine ⟨93669484835039433829625717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62446323223359622553083811 93669484835039433829625717)
              ·
                refine ⟨8781514203284946921527411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 93669484835039433829625717 8781514203284946921527411)
                ·
                  refine ⟨13172271304927420382291117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8781514203284946921527411 13172271304927420382291117)
                  ·
                    refine ⟨4939601739347782643359169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13172271304927420382291117 4939601739347782643359169)
                    ·
                      refine ⟨3704701304510836982519377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4939601739347782643359169 3704701304510836982519377)
                      ·
                        rfl

theorem cell23_7214880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 5, 1, 3, 2].length) (baseStart_7214880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7214880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7214880 prefixEnd_7214880 := by exact prefixLift 7214880
  have htrace : WordTrace (prefixWord ++ tailWord_7214880) baseStart_7214880 baseEnd_7214880 := by
    simpa [prefixWord, tailWord_7214880, baseEnd_7214880] using wordTrace_append hprefix tailTrace_7214880
  have hstable : (prefixWord ++ tailWord_7214880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7214880).length < 2 ^ (prefixWord ++ tailWord_7214880).sum := by decide
  have hdescent : baseEnd_7214880 < baseStart_7214880 := by decide
  rcases family_descends (prefixWord ++ tailWord_7214880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7215033 : List Nat := [1, 2, 1, 4, 2, 1, 1, 1, 2, 5, 3]
def baseStart_7215033 : Nat := 118140960795 + 7215033 * 2 ^ 59
def prefixEnd_7215033 : Nat := 4983230072969 + 3 ^ 40 * 7215033 * 2
def baseEnd_7215033 : Nat := 3704779867050974883906173

theorem tailTrace_7215033 : CollatzResearch.WordTrace tailWord_7215033 prefixEnd_7215033 3704779867050974883906173 := by
  unfold tailWord_7215033
  simp only [CollatzResearch.WordTrace]
  refine ⟨263153872470175145378705753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175435914980116763585803835 263153872470175145378705753)
  ·
    refine ⟨197365404352631359034029315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 263153872470175145378705753 197365404352631359034029315)
    ·
      refine ⟨296048106528947038551043973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197365404352631359034029315 296048106528947038551043973)
      ·
        refine ⟨55509019974177569728320745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 296048106528947038551043973 55509019974177569728320745)
        ·
          refine ⟨41631764980633177296240559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55509019974177569728320745 41631764980633177296240559)
          ·
            refine ⟨62447647470949765944360839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41631764980633177296240559 62447647470949765944360839)
            ·
              refine ⟨93671471206424648916541259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62447647470949765944360839 93671471206424648916541259)
              ·
                refine ⟨140507206809636973374811889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 93671471206424648916541259 140507206809636973374811889)
                ·
                  refine ⟨105380405107227730031108917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 140507206809636973374811889 105380405107227730031108917)
                  ·
                    refine ⟨9879412978802599690416461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 105380405107227730031108917 9879412978802599690416461)
                    ·
                      refine ⟨3704779867050974883906173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9879412978802599690416461 3704779867050974883906173)
                      ·
                        rfl

theorem cell23_7215033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 1, 2, 5, 3].length) (baseStart_7215033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7215033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7215033 prefixEnd_7215033 := by exact prefixLift 7215033
  have htrace : WordTrace (prefixWord ++ tailWord_7215033) baseStart_7215033 baseEnd_7215033 := by
    simpa [prefixWord, tailWord_7215033, baseEnd_7215033] using wordTrace_append hprefix tailTrace_7215033
  have hstable : (prefixWord ++ tailWord_7215033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7215033).length < 2 ^ (prefixWord ++ tailWord_7215033).sum := by decide
  have hdescent : baseEnd_7215033 < baseStart_7215033 := by decide
  rcases family_descends (prefixWord ++ tailWord_7215033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7215050 : List Nat := [3, 1, 2, 1, 2, 1, 2, 2, 5, 1, 3]
def baseStart_7215050 : Nat := 118140960795 + 7215050 * 2 ^ 59
def prefixEnd_7215050 : Nat := 4983230072969 + 3 ^ 40 * 7215050 * 2
def baseEnd_7215050 : Nat := 3704788596222101317393595

theorem tailTrace_7215050 : CollatzResearch.WordTrace tailWord_7215050 prefixEnd_7215050 3704788596222101317393595 := by
  unfold tailWord_7215050
  simp only [CollatzResearch.WordTrace]
  refine ⟨65788623127778389320518651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175436328340742371521383069 65788623127778389320518651)
  ·
    refine ⟨98682934691667583980777977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65788623127778389320518651 98682934691667583980777977)
    ·
      refine ⟨74012201018750687985583483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98682934691667583980777977 74012201018750687985583483)
      ·
        refine ⟨111018301528126031978375225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74012201018750687985583483 111018301528126031978375225)
        ·
          refine ⟨83263726146094523983781419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111018301528126031978375225 83263726146094523983781419)
          ·
            refine ⟨124895589219141785975672129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83263726146094523983781419 124895589219141785975672129)
            ·
              refine ⟨93671691914356339481754097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 124895589219141785975672129 93671691914356339481754097)
              ·
                refine ⟨70253768935767254611315573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 93671691914356339481754097 70253768935767254611315573)
                ·
                  refine ⟨6586290837728180119810835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 70253768935767254611315573 6586290837728180119810835)
                  ·
                    refine ⟨9879436256592270179716253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6586290837728180119810835 9879436256592270179716253)
                    ·
                      refine ⟨3704788596222101317393595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9879436256592270179716253 3704788596222101317393595)
                      ·
                        rfl

theorem cell23_7215050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 2, 5, 1, 3].length) (baseStart_7215050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7215050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7215050 prefixEnd_7215050 := by exact prefixLift 7215050
  have htrace : WordTrace (prefixWord ++ tailWord_7215050) baseStart_7215050 baseEnd_7215050 := by
    simpa [prefixWord, tailWord_7215050, baseEnd_7215050] using wordTrace_append hprefix tailTrace_7215050
  have hstable : (prefixWord ++ tailWord_7215050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7215050).length < 2 ^ (prefixWord ++ tailWord_7215050).sum := by decide
  have hdescent : baseEnd_7215050 < baseStart_7215050 := by decide
  rcases family_descends (prefixWord ++ tailWord_7215050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7215130 : List Nat := [3, 1, 1, 3, 1, 5, 1, 8]
def baseStart_7215130 : Nat := 118140960795 + 7215130 * 2 ^ 59
def prefixEnd_7215130 : Nat := 4983230072969 + 3 ^ 40 * 7215130 * 2
def baseEnd_7215130 : Nat := 137215913876831889051601

theorem tailTrace_7215130 : CollatzResearch.WordTrace tailWord_7215130 prefixEnd_7215130 137215913876831889051601 := by
  unfold tailWord_7215130
  simp only [CollatzResearch.WordTrace]
  refine ⟨65789352587705932736246711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175438273567215820629991229 65789352587705932736246711)
  ·
    refine ⟨98684028881558899104370067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65789352587705932736246711 98684028881558899104370067)
    ·
      refine ⟨148026043322338348656555101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98684028881558899104370067 148026043322338348656555101)
      ·
        refine ⟨55509766245876880746208163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 148026043322338348656555101 55509766245876880746208163)
        ·
          refine ⟨83264649368815321119312245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55509766245876880746208163 83264649368815321119312245)
          ·
            refine ⟨7806060878326436354935523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 83264649368815321119312245 7806060878326436354935523)
            ·
              refine ⟨11709091317489654532403285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7806060878326436354935523 11709091317489654532403285)
              ·
                refine ⟨137215913876831889051601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11709091317489654532403285 137215913876831889051601)
                ·
                  rfl

theorem cell23_7215130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 5, 1, 8].length) (baseStart_7215130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7215130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7215130 prefixEnd_7215130 := by exact prefixLift 7215130
  have htrace : WordTrace (prefixWord ++ tailWord_7215130) baseStart_7215130 baseEnd_7215130 := by
    simpa [prefixWord, tailWord_7215130, baseEnd_7215130] using wordTrace_append hprefix tailTrace_7215130
  have hstable : (prefixWord ++ tailWord_7215130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7215130).length < 2 ^ (prefixWord ++ tailWord_7215130).sum := by decide
  have hdescent : baseEnd_7215130 < baseStart_7215130 := by decide
  rcases family_descends (prefixWord ++ tailWord_7215130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7215137 : List Nat := [1, 2, 3, 2, 4, 1, 2, 1, 1, 2, 4]
def baseStart_7215137 : Nat := 118140960795 + 7215137 * 2 ^ 59
def prefixEnd_7215137 : Nat := 4983230072969 + 3 ^ 40 * 7215137 * 2
def baseEnd_7215137 : Nat := 3704833269039042477005695

theorem tailTrace_7215137 : CollatzResearch.WordTrace tailWord_7215137 prefixEnd_7215137 3704833269039042477005695 := by
  unfold tailWord_7215137
  simp only [CollatzResearch.WordTrace]
  refine ⟨263157665661798371140491665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175438443774532247426994443 263157665661798371140491665)
  ·
    refine ⟨197368249246348778355368749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 263157665661798371140491665 197368249246348778355368749)
    ·
      refine ⟨74013093467380791883263281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 197368249246348778355368749 74013093467380791883263281)
      ·
        refine ⟨55509820100535593912447461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74013093467380791883263281 55509820100535593912447461)
        ·
          refine ⟨10408091268850423858583899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55509820100535593912447461 10408091268850423858583899)
          ·
            refine ⟨15612136903275635787875849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10408091268850423858583899 15612136903275635787875849)
            ·
              refine ⟨11709102677456726840906887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15612136903275635787875849 11709102677456726840906887)
              ·
                refine ⟨17563654016185090261360331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11709102677456726840906887 17563654016185090261360331)
                ·
                  refine ⟨26345481024277635392040497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17563654016185090261360331 26345481024277635392040497)
                  ·
                    refine ⟨19759110768208226544030373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26345481024277635392040497 19759110768208226544030373)
                    ·
                      refine ⟨3704833269039042477005695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19759110768208226544030373 3704833269039042477005695)
                      ·
                        rfl

theorem cell23_7215137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 2, 1, 1, 2, 4].length) (baseStart_7215137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7215137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7215137 prefixEnd_7215137 := by exact prefixLift 7215137
  have htrace : WordTrace (prefixWord ++ tailWord_7215137) baseStart_7215137 baseEnd_7215137 := by
    simpa [prefixWord, tailWord_7215137, baseEnd_7215137] using wordTrace_append hprefix tailTrace_7215137
  have hstable : (prefixWord ++ tailWord_7215137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7215137).length < 2 ^ (prefixWord ++ tailWord_7215137).sum := by decide
  have hdescent : baseEnd_7215137 < baseStart_7215137 := by decide
  rcases family_descends (prefixWord ++ tailWord_7215137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7215158 : List Nat := [5, 1, 2, 1, 1, 1, 4, 3, 1, 2, 2]
def baseStart_7215158 : Nat := 118140960795 + 7215158 * 2 ^ 59
def prefixEnd_7215158 : Nat := 4983230072969 + 3 ^ 40 * 7215158 * 2
def baseEnd_7215158 : Nat := 3704844052132786894843099

theorem tailTrace_7215158 : CollatzResearch.WordTrace tailWord_7215158 prefixEnd_7215158 3704844052132786894843099 := by
  unfold tailWord_7215158
  simp only [CollatzResearch.WordTrace]
  refine ⟨16447401974670143232937883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 175438954396481527818004085 16447401974670143232937883)
  ·
    refine ⟨24671102962005214849406825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16447401974670143232937883 24671102962005214849406825)
    ·
      refine ⟨18503327221503911137055119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24671102962005214849406825 18503327221503911137055119)
      ·
        refine ⟨27754990832255866705582679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18503327221503911137055119 27754990832255866705582679)
        ·
          refine ⟨41632486248383800058374019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27754990832255866705582679 41632486248383800058374019)
          ·
            refine ⟨62448729372575700087561029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41632486248383800058374019 62448729372575700087561029)
            ·
              refine ⟨11709136757357943766417693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 62448729372575700087561029 11709136757357943766417693)
              ·
                refine ⟨4390926284009228912406635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11709136757357943766417693 4390926284009228912406635)
                ·
                  refine ⟨6586389426013843368609953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4390926284009228912406635 6586389426013843368609953)
                  ·
                    refine ⟨4939792069510382526457465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6586389426013843368609953 4939792069510382526457465)
                    ·
                      refine ⟨3704844052132786894843099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4939792069510382526457465 3704844052132786894843099)
                      ·
                        rfl

theorem cell23_7215158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 4, 3, 1, 2, 2].length) (baseStart_7215158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7215158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7215158 prefixEnd_7215158 := by exact prefixLift 7215158
  have htrace : WordTrace (prefixWord ++ tailWord_7215158) baseStart_7215158 baseEnd_7215158 := by
    simpa [prefixWord, tailWord_7215158, baseEnd_7215158] using wordTrace_append hprefix tailTrace_7215158
  have hstable : (prefixWord ++ tailWord_7215158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7215158).length < 2 ^ (prefixWord ++ tailWord_7215158).sum := by decide
  have hdescent : baseEnd_7215158 < baseStart_7215158 := by decide
  rcases family_descends (prefixWord ++ tailWord_7215158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7215161 : List Nat := [1, 2, 1, 5, 3, 2, 2, 1, 1, 2, 3]
def baseStart_7215161 : Nat := 118140960795 + 7215161 * 2 ^ 59
def prefixEnd_7215161 : Nat := 4983230072969 + 3 ^ 40 * 7215161 * 2
def baseEnd_7215161 : Nat := 3704845592574750383105585

theorem tailTrace_7215161 : CollatzResearch.WordTrace tailWord_7215161 prefixEnd_7215161 3704845592574750383105585 := by
  unfold tailWord_7215161
  simp only [CollatzResearch.WordTrace]
  refine ⟨263158541013711423239365337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175439027342474282159576891 263158541013711423239365337)
  ·
    refine ⟨197368905760283567429524003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 263158541013711423239365337 197368905760283567429524003)
    ·
      refine ⟨296053358640425351144286005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197368905760283567429524003 296053358640425351144286005)
      ·
        refine ⟨27755002372539876669776813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 296053358640425351144286005 27755002372539876669776813)
        ·
          refine ⟨10408125889702453751166305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27755002372539876669776813 10408125889702453751166305)
          ·
            refine ⟨7806094417276840313374729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10408125889702453751166305 7806094417276840313374729)
            ·
              refine ⟨5854570812957630235031047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7806094417276840313374729 5854570812957630235031047)
              ·
                refine ⟨8781856219436445352546571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5854570812957630235031047 8781856219436445352546571)
                ·
                  refine ⟨13172784329154668028819857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8781856219436445352546571 13172784329154668028819857)
                  ·
                    refine ⟨9879588246866001021614893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13172784329154668028819857 9879588246866001021614893)
                    ·
                      refine ⟨3704845592574750383105585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9879588246866001021614893 3704845592574750383105585)
                      ·
                        rfl

theorem cell23_7215161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 2, 2, 1, 1, 2, 3].length) (baseStart_7215161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7215161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7215161 prefixEnd_7215161 := by exact prefixLift 7215161
  have htrace : WordTrace (prefixWord ++ tailWord_7215161) baseStart_7215161 baseEnd_7215161 := by
    simpa [prefixWord, tailWord_7215161, baseEnd_7215161] using wordTrace_append hprefix tailTrace_7215161
  have hstable : (prefixWord ++ tailWord_7215161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7215161).length < 2 ^ (prefixWord ++ tailWord_7215161).sum := by decide
  have hdescent : baseEnd_7215161 < baseStart_7215161 := by decide
  rcases family_descends (prefixWord ++ tailWord_7215161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7215163 : List Nat := [1, 1, 1, 1, 1, 2, 1, 4, 4, 3, 4]
def baseStart_7215163 : Nat := 118140960795 + 7215163 * 2 ^ 59
def prefixEnd_7215163 : Nat := 4983230072969 + 3 ^ 40 * 7215163 * 2
def baseEnd_7215163 : Nat := 3704846619536059375280575

theorem tailTrace_7215163 : CollatzResearch.WordTrace tailWord_7215163 prefixEnd_7215163 3704846619536059375280575 := by
  unfold tailWord_7215163
  simp only [CollatzResearch.WordTrace]
  refine ⟨263158613959704177580938143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175439075973136118387292095 263158613959704177580938143)
  ·
    refine ⟨394737920939556266371407215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263158613959704177580938143 394737920939556266371407215)
    ·
      refine ⟨592106881409334399557110823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 394737920939556266371407215 592106881409334399557110823)
      ·
        refine ⟨888160322114001599335666235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 592106881409334399557110823 888160322114001599335666235)
        ·
          refine ⟨1332240483171002399003499353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 888160322114001599335666235 1332240483171002399003499353)
          ·
            refine ⟨999180362378251799252624515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1332240483171002399003499353 999180362378251799252624515)
            ·
              refine ⟨1498770543567377698878936773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 999180362378251799252624515 1498770543567377698878936773)
              ·
                refine ⟨281019476918883318539800645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1498770543567377698878936773 281019476918883318539800645)
                ·
                  refine ⟨52691151922290622226212621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 281019476918883318539800645 52691151922290622226212621)
                  ·
                    refine ⟨19759181970858983334829733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 52691151922290622226212621 19759181970858983334829733)
                    ·
                      refine ⟨3704846619536059375280575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19759181970858983334829733 3704846619536059375280575)
                      ·
                        rfl

theorem cell23_7215163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 4, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 4, 4, 3, 4].length) (baseStart_7215163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7215163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7215163 prefixEnd_7215163 := by exact prefixLift 7215163
  have htrace : WordTrace (prefixWord ++ tailWord_7215163) baseStart_7215163 baseEnd_7215163 := by
    simpa [prefixWord, tailWord_7215163, baseEnd_7215163] using wordTrace_append hprefix tailTrace_7215163
  have hstable : (prefixWord ++ tailWord_7215163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7215163).length < 2 ^ (prefixWord ++ tailWord_7215163).sum := by decide
  have hdescent : baseEnd_7215163 < baseStart_7215163 := by decide
  rcases family_descends (prefixWord ++ tailWord_7215163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7215183 : List Nat := [1, 1, 2, 1, 1, 2, 2, 4, 1, 3, 5]
def baseStart_7215183 : Nat := 118140960795 + 7215183 * 2 ^ 59
def prefixEnd_7215183 : Nat := 4983230072969 + 3 ^ 40 * 7215183 * 2
def baseEnd_7215183 : Nat := 3704856889149149297030483

theorem tailTrace_7215183 : CollatzResearch.WordTrace tailWord_7215183 prefixEnd_7215183 3704856889149149297030483 := by
  unfold tailWord_7215183
  simp only [CollatzResearch.WordTrace]
  refine ⟨263159343419631720996666203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175439562279754480664444135 263159343419631720996666203)
  ·
    refine ⟨394739015129447581494999305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263159343419631720996666203 394739015129447581494999305)
    ·
      refine ⟨296054261347085686121249479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 394739015129447581494999305 296054261347085686121249479)
      ·
        refine ⟨444081392020628529181874219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 296054261347085686121249479 444081392020628529181874219)
        ·
          refine ⟨666122088030942793772811329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 444081392020628529181874219 666122088030942793772811329)
          ·
            refine ⟨499591566023207095329608497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 666122088030942793772811329 499591566023207095329608497)
            ·
              refine ⟨374693674517405321497206373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 499591566023207095329608497 374693674517405321497206373)
              ·
                refine ⟨70255063972013497780726195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 374693674517405321497206373 70255063972013497780726195)
                ·
                  refine ⟨105382595958020246671089293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70255063972013497780726195 105382595958020246671089293)
                  ·
                    refine ⟨39518473484257592501658485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 105382595958020246671089293 39518473484257592501658485)
                    ·
                      refine ⟨3704856889149149297030483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39518473484257592501658485 3704856889149149297030483)
                      ·
                        rfl

theorem cell23_7215183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 4, 1, 3, 5].length) (baseStart_7215183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7215183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7215183 prefixEnd_7215183 := by exact prefixLift 7215183
  have htrace : WordTrace (prefixWord ++ tailWord_7215183) baseStart_7215183 baseEnd_7215183 := by
    simpa [prefixWord, tailWord_7215183, baseEnd_7215183] using wordTrace_append hprefix tailTrace_7215183
  have hstable : (prefixWord ++ tailWord_7215183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7215183).length < 2 ^ (prefixWord ++ tailWord_7215183).sum := by decide
  have hdescent : baseEnd_7215183 < baseStart_7215183 := by decide
  rcases family_descends (prefixWord ++ tailWord_7215183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7215198 : List Nat := [4, 4, 1, 1, 3, 1, 2, 7]
def baseStart_7215198 : Nat := 118140960795 + 7215198 * 2 ^ 59
def prefixEnd_7215198 : Nat := 4983230072969 + 3 ^ 40 * 7215198 * 2
def baseEnd_7215198 : Nat := 137217207087369138457145

theorem tailTrace_7215198 : CollatzResearch.WordTrace tailWord_7215198 prefixEnd_7215198 137217207087369138457145 := by
  unfold tailWord_7215198
  simp only [CollatzResearch.WordTrace]
  refine ⟨32894986314322172319807781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 175439927009718252372308165 32894986314322172319807781)
  ·
    refine ⟨6167809933935407309963959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32894986314322172319807781 6167809933935407309963959)
    ·
      refine ⟨9251714900903110964945939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6167809933935407309963959 9251714900903110964945939)
      ·
        refine ⟨13877572351354666447418909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9251714900903110964945939 13877572351354666447418909)
        ·
          refine ⟨5204089631757999917782091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13877572351354666447418909 5204089631757999917782091)
          ·
            refine ⟨7806134447636999876673137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5204089631757999917782091 7806134447636999876673137)
            ·
              refine ⟨5854600835727749907504853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7806134447636999876673137 5854600835727749907504853)
              ·
                refine ⟨137217207087369138457145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5854600835727749907504853 137217207087369138457145)
                ·
                  rfl

theorem cell23_7215198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 3, 1, 2, 7].length) (baseStart_7215198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7215198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7215198 prefixEnd_7215198 := by exact prefixLift 7215198
  have htrace : WordTrace (prefixWord ++ tailWord_7215198) baseStart_7215198 baseEnd_7215198 := by
    simpa [prefixWord, tailWord_7215198, baseEnd_7215198] using wordTrace_append hprefix tailTrace_7215198
  have hstable : (prefixWord ++ tailWord_7215198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7215198).length < 2 ^ (prefixWord ++ tailWord_7215198).sum := by decide
  have hdescent : baseEnd_7215198 < baseStart_7215198 := by decide
  rcases family_descends (prefixWord ++ tailWord_7215198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7215214 : List Nat := [4, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2]
def baseStart_7215214 : Nat := 118140960795 + 7215214 * 2 ^ 59
def prefixEnd_7215214 : Nat := 4983230072969 + 3 ^ 40 * 7215214 * 2
def baseEnd_7215214 : Nat := 3704872807049438675742841

theorem tailTrace_7215214 : CollatzResearch.WordTrace tailWord_7215214 prefixEnd_7215214 3704872807049438675742841 := by
  unfold tailWord_7215214
  simp only [CollatzResearch.WordTrace]
  refine ⟨32895059260314926661380587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 175440316055012942194029797 32895059260314926661380587)
  ·
    refine ⟨49342588890472389992070881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32895059260314926661380587 49342588890472389992070881)
    ·
      refine ⟨37006941667854292494053161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49342588890472389992070881 37006941667854292494053161)
      ·
        refine ⟨27755206250890719370539871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37006941667854292494053161 27755206250890719370539871)
        ·
          refine ⟨41632809376336079055809807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27755206250890719370539871 41632809376336079055809807)
          ·
            refine ⟨62449214064504118583714711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41632809376336079055809807 62449214064504118583714711)
            ·
              refine ⟨93673821096756177875572067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62449214064504118583714711 93673821096756177875572067)
              ·
                refine ⟨140510731645134266813358101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 93673821096756177875572067 140510731645134266813358101)
                ·
                  refine ⟨6586440545865668756876161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 140510731645134266813358101 6586440545865668756876161)
                  ·
                    refine ⟨4939830409399251567657121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6586440545865668756876161 4939830409399251567657121)
                    ·
                      refine ⟨3704872807049438675742841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4939830409399251567657121 3704872807049438675742841)
                      ·
                        rfl

theorem cell23_7215214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2].length) (baseStart_7215214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7215214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7215214 prefixEnd_7215214 := by exact prefixLift 7215214
  have htrace : WordTrace (prefixWord ++ tailWord_7215214) baseStart_7215214 baseEnd_7215214 := by
    simpa [prefixWord, tailWord_7215214, baseEnd_7215214] using wordTrace_append hprefix tailTrace_7215214
  have hstable : (prefixWord ++ tailWord_7215214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7215214).length < 2 ^ (prefixWord ++ tailWord_7215214).sum := by decide
  have hdescent : baseEnd_7215214 < baseStart_7215214 := by decide
  rcases family_descends (prefixWord ++ tailWord_7215214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7215237 : List Nat := [1, 3, 1, 1, 5, 3, 1, 1, 7]
def baseStart_7215237 : Nat := 118140960795 + 7215237 * 2 ^ 59
def prefixEnd_7215237 : Nat := 4983230072969 + 3 ^ 40 * 7215237 * 2
def baseEnd_7215237 : Nat := 411653846344943565083915

theorem tailTrace_7215237 : CollatzResearch.WordTrace tailWord_7215237 prefixEnd_7215237 411653846344943565083915 := by
  unfold tailWord_7215237
  simp only [CollatzResearch.WordTrace]
  refine ⟨263161312961436088219131965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175440875307624058812754643 263161312961436088219131965)
  ·
    refine ⟨98685492360538533082174487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 263161312961436088219131965 98685492360538533082174487)
    ·
      refine ⟨148028238540807799623261731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98685492360538533082174487 148028238540807799623261731)
      ·
        refine ⟨222042357811211699434892597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148028238540807799623261731 222042357811211699434892597)
        ·
          refine ⟨20816471044801096822021181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 222042357811211699434892597 20816471044801096822021181)
          ·
            refine ⟨7806176641800411308257943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20816471044801096822021181 7806176641800411308257943)
            ·
              refine ⟨11709264962700616962386915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7806176641800411308257943 11709264962700616962386915)
              ·
                refine ⟨17563897444050925443580373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11709264962700616962386915 17563897444050925443580373)
                ·
                  refine ⟨411653846344943565083915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17563897444050925443580373 411653846344943565083915)
                  ·
                    rfl

theorem cell23_7215237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 3, 1, 1, 7].length) (baseStart_7215237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7215237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7215237 prefixEnd_7215237 := by exact prefixLift 7215237
  have htrace : WordTrace (prefixWord ++ tailWord_7215237) baseStart_7215237 baseEnd_7215237 := by
    simpa [prefixWord, tailWord_7215237, baseEnd_7215237] using wordTrace_append hprefix tailTrace_7215237
  have hstable : (prefixWord ++ tailWord_7215237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7215237).length < 2 ^ (prefixWord ++ tailWord_7215237).sum := by decide
  have hdescent : baseEnd_7215237 < baseStart_7215237 := by decide
  rcases family_descends (prefixWord ++ tailWord_7215237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7215260 : List Nat := [2, 2, 3, 2, 1, 1, 1, 2, 1, 1, 7]
def baseStart_7215260 : Nat := 118140960795 + 7215260 * 2 ^ 59
def prefixEnd_7215260 : Nat := 4983230072969 + 3 ^ 40 * 7215260 * 2
def baseEnd_7215260 : Nat := 3704896427159545495767629

theorem tailTrace_7215260 : CollatzResearch.WordTrace tailWord_7215260 prefixEnd_7215260 3704896427159545495767629 := by
  unfold tailWord_7215260
  simp only [CollatzResearch.WordTrace]
  refine ⟨131581075920176381573609617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175441434560235175431479489 131581075920176381573609617)
  ·
    refine ⟨98685806940132286180207213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131581075920176381573609617 98685806940132286180207213)
    ·
      refine ⟨37007177602549607317577705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98685806940132286180207213 37007177602549607317577705)
      ·
        refine ⟨27755383201912205488183279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37007177602549607317577705 27755383201912205488183279)
        ·
          refine ⟨41633074802868308232274919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27755383201912205488183279 41633074802868308232274919)
          ·
            refine ⟨62449612204302462348412379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41633074802868308232274919 62449612204302462348412379)
            ·
              refine ⟨93674418306453693522618569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62449612204302462348412379 93674418306453693522618569)
              ·
                refine ⟨70255813729840270141963927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 93674418306453693522618569 70255813729840270141963927)
                ·
                  refine ⟨105383720594760405212945891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70255813729840270141963927 105383720594760405212945891)
                  ·
                    refine ⟨158075580892140607819418837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 105383720594760405212945891 158075580892140607819418837)
                    ·
                      refine ⟨3704896427159545495767629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 158075580892140607819418837 3704896427159545495767629)
                      ·
                        rfl

theorem cell23_7215260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 2, 1, 1, 7].length) (baseStart_7215260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7215260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7215260 prefixEnd_7215260 := by exact prefixLift 7215260
  have htrace : WordTrace (prefixWord ++ tailWord_7215260) baseStart_7215260 baseEnd_7215260 := by
    simpa [prefixWord, tailWord_7215260, baseEnd_7215260] using wordTrace_append hprefix tailTrace_7215260
  have hstable : (prefixWord ++ tailWord_7215260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7215260).length < 2 ^ (prefixWord ++ tailWord_7215260).sum := by decide
  have hdescent : baseEnd_7215260 < baseStart_7215260 := by decide
  rcases family_descends (prefixWord ++ tailWord_7215260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7215277 : List Nat := [1, 5, 2, 1, 2, 1, 1, 2, 1, 2, 5]
def baseStart_7215277 : Nat := 118140960795 + 7215277 * 2 ^ 59
def prefixEnd_7215277 : Nat := 4983230072969 + 3 ^ 40 * 7215277 * 2
def baseEnd_7215277 : Nat := 3704905156330671929255051

theorem tailTrace_7215277 : CollatzResearch.WordTrace tailWord_7215277 prefixEnd_7215277 3704905156330671929255051 := by
  unfold tailWord_7215277
  simp only [CollatzResearch.WordTrace]
  refine ⟨263162771881291175050588085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175441847920860783367058723 263162771881291175050588085)
  ·
    refine ⟨24671509863871047660992633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 263162771881291175050588085 24671509863871047660992633)
    ·
      refine ⟨18503632397903285745744475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24671509863871047660992633 18503632397903285745744475)
      ·
        refine ⟨27755448596854928618616713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18503632397903285745744475 27755448596854928618616713)
        ·
          refine ⟨20816586447641196463962535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27755448596854928618616713 20816586447641196463962535)
          ·
            refine ⟨31224879671461794695943803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20816586447641196463962535 31224879671461794695943803)
            ·
              refine ⟨46837319507192692043915705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31224879671461794695943803 46837319507192692043915705)
              ·
                refine ⟨35127989630394519032936779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46837319507192692043915705 35127989630394519032936779)
                ·
                  refine ⟨52691984445591778549405169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35127989630394519032936779 52691984445591778549405169)
                  ·
                    refine ⟨39518988334193833912053877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 52691984445591778549405169 39518988334193833912053877)
                    ·
                      refine ⟨3704905156330671929255051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39518988334193833912053877 3704905156330671929255051)
                      ·
                        rfl

theorem cell23_7215277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 1, 2, 1, 2, 5].length) (baseStart_7215277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7215277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7215277 prefixEnd_7215277 := by exact prefixLift 7215277
  have htrace : WordTrace (prefixWord ++ tailWord_7215277) baseStart_7215277 baseEnd_7215277 := by
    simpa [prefixWord, tailWord_7215277, baseEnd_7215277] using wordTrace_append hprefix tailTrace_7215277
  have hstable : (prefixWord ++ tailWord_7215277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7215277).length < 2 ^ (prefixWord ++ tailWord_7215277).sum := by decide
  have hdescent : baseEnd_7215277 < baseStart_7215277 := by decide
  rcases family_descends (prefixWord ++ tailWord_7215277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7215287 : List Nat := [1, 1, 3, 1, 4, 2, 2, 2, 2, 1, 4]
def baseStart_7215287 : Nat := 118140960795 + 7215287 * 2 ^ 59
def prefixEnd_7215287 : Nat := 4983230072969 + 3 ^ 40 * 7215287 * 2
def baseEnd_7215287 : Nat := 3704910291137216890130005

theorem tailTrace_7215287 : CollatzResearch.WordTrace tailWord_7215287 prefixEnd_7215287 3704910291137216890130005 := by
  unfold tailWord_7215287
  simp only [CollatzResearch.WordTrace]
  refine ⟨263163136611254946758452115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175442091074169964505634743 263163136611254946758452115)
  ·
    refine ⟨394744704916882420137678173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263163136611254946758452115 394744704916882420137678173)
    ·
      refine ⟨148029264343830907551629315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 394744704916882420137678173 148029264343830907551629315)
      ·
        refine ⟨222043896515746361327443973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148029264343830907551629315 222043896515746361327443973)
        ·
          refine ⟨41633230596702442748895745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 222043896515746361327443973 41633230596702442748895745)
          ·
            refine ⟨31224922947526832061671809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41633230596702442748895745 31224922947526832061671809)
            ·
              refine ⟨23418692210645124046253857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31224922947526832061671809 23418692210645124046253857)
              ·
                refine ⟨17564019157983843034690393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23418692210645124046253857 17564019157983843034690393)
                ·
                  refine ⟨13173014368487882276017795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17564019157983843034690393 13173014368487882276017795)
                  ·
                    refine ⟨19759521552731823414026693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13173014368487882276017795 19759521552731823414026693)
                    ·
                      refine ⟨3704910291137216890130005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19759521552731823414026693 3704910291137216890130005)
                      ·
                        rfl

theorem cell23_7215287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 2, 2, 2, 1, 4].length) (baseStart_7215287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7215287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7215287 prefixEnd_7215287 := by exact prefixLift 7215287
  have htrace : WordTrace (prefixWord ++ tailWord_7215287) baseStart_7215287 baseEnd_7215287 := by
    simpa [prefixWord, tailWord_7215287, baseEnd_7215287] using wordTrace_append hprefix tailTrace_7215287
  have hstable : (prefixWord ++ tailWord_7215287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7215287).length < 2 ^ (prefixWord ++ tailWord_7215287).sum := by decide
  have hdescent : baseEnd_7215287 < baseStart_7215287 := by decide
  rcases family_descends (prefixWord ++ tailWord_7215287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7215314 : List Nat := [3, 2, 2, 2, 1, 3, 1, 2, 3, 4]
def baseStart_7215314 : Nat := 118140960795 + 7215314 * 2 ^ 59
def prefixEnd_7215314 : Nat := 4983230072969 + 3 ^ 40 * 7215314 * 2
def baseEnd_7215314 : Nat := 1234974718371629428164127

theorem tailTrace_7215314 : CollatzResearch.WordTrace tailWord_7215314 prefixEnd_7215314 1234974718371629428164127 := by
  unfold tailWord_7215314
  simp only [CollatzResearch.WordTrace]
  refine ⟨65791030345539282592421249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175442747588104753579789997 65791030345539282592421249)
  ·
    refine ⟨49343272759154461944315937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65791030345539282592421249 49343272759154461944315937)
    ·
      refine ⟨37007454569365846458236953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49343272759154461944315937 37007454569365846458236953)
      ·
        refine ⟨27755590927024384843677715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37007454569365846458236953 27755590927024384843677715)
        ·
          refine ⟨41633386390536577265516573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27755590927024384843677715 41633386390536577265516573)
          ·
            refine ⟨15612519896451216474568715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41633386390536577265516573 15612519896451216474568715)
            ·
              refine ⟨23418779844676824711853073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15612519896451216474568715 23418779844676824711853073)
              ·
                refine ⟨17564084883507618533889805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23418779844676824711853073 17564084883507618533889805)
                ·
                  refine ⟨6586531831315356950208677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17564084883507618533889805 6586531831315356950208677)
                  ·
                    refine ⟨1234974718371629428164127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6586531831315356950208677 1234974718371629428164127)
                    ·
                      rfl

theorem cell23_7215314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 1, 2, 3, 4].length) (baseStart_7215314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7215314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7215314 prefixEnd_7215314 := by exact prefixLift 7215314
  have htrace : WordTrace (prefixWord ++ tailWord_7215314) baseStart_7215314 baseEnd_7215314 := by
    simpa [prefixWord, tailWord_7215314, baseEnd_7215314] using wordTrace_append hprefix tailTrace_7215314
  have hstable : (prefixWord ++ tailWord_7215314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7215314).length < 2 ^ (prefixWord ++ tailWord_7215314).sum := by decide
  have hdescent : baseEnd_7215314 < baseStart_7215314 := by decide
  rcases family_descends (prefixWord ++ tailWord_7215314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7215354 : List Nat := [3, 1, 1, 1, 1, 5, 1, 3, 3, 1, 3]
def baseStart_7215354 : Nat := 118140960795 + 7215354 * 2 ^ 59
def prefixEnd_7215354 : Nat := 4983230072969 + 3 ^ 40 * 7215354 * 2
def baseEnd_7215354 : Nat := 3704944694341068127992197

theorem tailTrace_7215354 : CollatzResearch.WordTrace tailWord_7215354 prefixEnd_7215354 3704944694341068127992197 := by
  unfold tailWord_7215354
  simp only [CollatzResearch.WordTrace]
  refine ⟨65791395075503054300285279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175443720201341478134094077 65791395075503054300285279)
  ·
    refine ⟨98687092613254581450427919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65791395075503054300285279 98687092613254581450427919)
    ·
      refine ⟨148030638919881872175641879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98687092613254581450427919 148030638919881872175641879)
      ·
        refine ⟨222045958379822808263462819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148030638919881872175641879 222045958379822808263462819)
        ·
          refine ⟨333068937569734212395194229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 222045958379822808263462819 333068937569734212395194229)
          ·
            refine ⟨31225212897162582412049459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 333068937569734212395194229 31225212897162582412049459)
            ·
              refine ⟨46837819345743873618074189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31225212897162582412049459 46837819345743873618074189)
              ·
                refine ⟨17564182254653952606777821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46837819345743873618074189 17564182254653952606777821)
                ·
                  refine ⟨6586568345495232227541683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17564182254653952606777821 6586568345495232227541683)
                  ·
                    refine ⟨9879852518242848341312525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6586568345495232227541683 9879852518242848341312525)
                    ·
                      refine ⟨3704944694341068127992197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9879852518242848341312525 3704944694341068127992197)
                      ·
                        rfl

theorem cell23_7215354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 1, 3, 3, 1, 3].length) (baseStart_7215354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7215354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7215354 prefixEnd_7215354 := by exact prefixLift 7215354
  have htrace : WordTrace (prefixWord ++ tailWord_7215354) baseStart_7215354 baseEnd_7215354 := by
    simpa [prefixWord, tailWord_7215354, baseEnd_7215354] using wordTrace_append hprefix tailTrace_7215354
  have hstable : (prefixWord ++ tailWord_7215354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7215354).length < 2 ^ (prefixWord ++ tailWord_7215354).sum := by decide
  have hdescent : baseEnd_7215354 < baseStart_7215354 := by decide
  rcases family_descends (prefixWord ++ tailWord_7215354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7215374 : List Nat := [4, 1, 1, 2, 1, 2, 4, 2, 1, 5]
def baseStart_7215374 : Nat := 118140960795 + 7215374 * 2 ^ 59
def prefixEnd_7215374 : Nat := 4983230072969 + 3 ^ 40 * 7215374 * 2
def baseEnd_7215374 : Nat := 1234984987984719349914035

theorem tailTrace_7215374 : CollatzResearch.WordTrace tailWord_7215374 prefixEnd_7215374 1234984987984719349914035 := by
  unfold tailWord_7215374
  simp only [CollatzResearch.WordTrace]
  refine ⟨32895788720242470077108647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 175444206507959840411246117 32895788720242470077108647)
  ·
    refine ⟨49343683080363705115662971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32895788720242470077108647 49343683080363705115662971)
    ·
      refine ⟨74015524620545557673494457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49343683080363705115662971 74015524620545557673494457)
      ·
        refine ⟨55511643465409168255120843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74015524620545557673494457 55511643465409168255120843)
        ·
          refine ⟨83267465198113752382681265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55511643465409168255120843 83267465198113752382681265)
          ·
            refine ⟨62450598898585314287010949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83267465198113752382681265 62450598898585314287010949)
            ·
              refine ⟨11709487293484746428814553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 62450598898585314287010949 11709487293484746428814553)
              ·
                refine ⟨8782115470113559821610915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11709487293484746428814553 8782115470113559821610915)
                ·
                  refine ⟨13173173205170339732416373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8782115470113559821610915 13173173205170339732416373)
                  ·
                    refine ⟨1234984987984719349914035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13173173205170339732416373 1234984987984719349914035)
                    ·
                      rfl

theorem cell23_7215374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 4, 2, 1, 5].length) (baseStart_7215374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7215374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7215374 prefixEnd_7215374 := by exact prefixLift 7215374
  have htrace : WordTrace (prefixWord ++ tailWord_7215374) baseStart_7215374 baseEnd_7215374 := by
    simpa [prefixWord, tailWord_7215374, baseEnd_7215374] using wordTrace_append hprefix tailTrace_7215374
  have hstable : (prefixWord ++ tailWord_7215374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7215374).length < 2 ^ (prefixWord ++ tailWord_7215374).sum := by decide
  have hdescent : baseEnd_7215374 < baseStart_7215374 := by decide
  rcases family_descends (prefixWord ++ tailWord_7215374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7215387 : List Nat := [1, 1, 1, 1, 1, 1, 7, 2, 4, 4]
def baseStart_7215387 : Nat := 118140960795 + 7215387 * 2 ^ 59
def prefixEnd_7215387 : Nat := 4983230072969 + 3 ^ 40 * 7215387 * 2
def baseEnd_7215387 : Nat := 1234987213067555499626515

theorem tailTrace_7215387 : CollatzResearch.WordTrace tailWord_7215387 prefixEnd_7215387 1234987213067555499626515 := by
  unfold tailWord_7215387
  simp only [CollatzResearch.WordTrace]
  refine ⟨263166783910892663837092415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175444522607261775891394943 263166783910892663837092415)
  ·
    refine ⟨394750175866338995755638623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263166783910892663837092415 394750175866338995755638623)
    ·
      refine ⟨592125263799508493633457935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 394750175866338995755638623 592125263799508493633457935)
      ·
        refine ⟨888187895699262740450186903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 592125263799508493633457935 888187895699262740450186903)
        ·
          refine ⟨1332281843548894110675280355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 888187895699262740450186903 1332281843548894110675280355)
          ·
            refine ⟨1998422765323341166012920533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1332281843548894110675280355 1998422765323341166012920533)
            ·
              refine ⟨46838033562265808578427825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1998422765323341166012920533 46838033562265808578427825)
              ·
                refine ⟨35128525171699356433820869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46838033562265808578427825 35128525171699356433820869)
                ·
                  refine ⟨6586598469693629331341413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35128525171699356433820869 6586598469693629331341413)
                  ·
                    refine ⟨1234987213067555499626515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6586598469693629331341413 1234987213067555499626515)
                    ·
                      rfl

theorem cell23_7215387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 7, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 7, 2, 4, 4].length) (baseStart_7215387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7215387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7215387 prefixEnd_7215387 := by exact prefixLift 7215387
  have htrace : WordTrace (prefixWord ++ tailWord_7215387) baseStart_7215387 baseEnd_7215387 := by
    simpa [prefixWord, tailWord_7215387, baseEnd_7215387] using wordTrace_append hprefix tailTrace_7215387
  have hstable : (prefixWord ++ tailWord_7215387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7215387).length < 2 ^ (prefixWord ++ tailWord_7215387).sum := by decide
  have hdescent : baseEnd_7215387 < baseStart_7215387 := by decide
  rcases family_descends (prefixWord ++ tailWord_7215387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7215405 : List Nat := [1, 5, 3, 1, 2, 2, 1, 1, 3, 1, 3]
def baseStart_7215405 : Nat := 118140960795 + 7215405 * 2 ^ 59
def prefixEnd_7215405 : Nat := 4983230072969 + 3 ^ 40 * 7215405 * 2
def baseEnd_7215405 : Nat := 3704970881854447428454463

theorem tailTrace_7215405 : CollatzResearch.WordTrace tailWord_7215405 prefixEnd_7215405 3704970881854447428454463 := by
  unfold tailWord_7215405
  simp only [CollatzResearch.WordTrace]
  refine ⟨263167440424827452911247669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175444960283218301940831779 263167440424827452911247669)
  ·
    refine ⟨24671947539827573710429469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 263167440424827452911247669 24671947539827573710429469)
    ·
      refine ⟨9251980327435340141411051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24671947539827573710429469 9251980327435340141411051)
      ·
        refine ⟨13877970491153010212116577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9251980327435340141411051 13877970491153010212116577)
        ·
          refine ⟨10408477868364757659087433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13877970491153010212116577 10408477868364757659087433)
          ·
            refine ⟨7806358401273568244315575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10408477868364757659087433 7806358401273568244315575)
            ·
              refine ⟨11709537601910352366473363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7806358401273568244315575 11709537601910352366473363)
              ·
                refine ⟨17564306402865528549710045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11709537601910352366473363 17564306402865528549710045)
                ·
                  refine ⟨6586614901074573206141267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17564306402865528549710045 6586614901074573206141267)
                  ·
                    refine ⟨9879922351611859809211901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6586614901074573206141267 9879922351611859809211901)
                    ·
                      refine ⟨3704970881854447428454463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9879922351611859809211901 3704970881854447428454463)
                      ·
                        rfl

theorem cell23_7215405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 2, 1, 1, 3, 1, 3].length) (baseStart_7215405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7215405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7215405 prefixEnd_7215405 := by exact prefixLift 7215405
  have htrace : WordTrace (prefixWord ++ tailWord_7215405) baseStart_7215405 baseEnd_7215405 := by
    simpa [prefixWord, tailWord_7215405, baseEnd_7215405] using wordTrace_append hprefix tailTrace_7215405
  have hstable : (prefixWord ++ tailWord_7215405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7215405).length < 2 ^ (prefixWord ++ tailWord_7215405).sum := by decide
  have hdescent : baseEnd_7215405 < baseStart_7215405 := by decide
  rcases family_descends (prefixWord ++ tailWord_7215405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7215417 : List Nat := [1, 2, 1, 6, 1, 1, 1, 10]
def baseStart_7215417 : Nat := 118140960795 + 7215417 * 2 ^ 59
def prefixEnd_7215417 : Nat := 4983230072969 + 3 ^ 40 * 7215417 * 2
def baseEnd_7215417 : Nat := 137221371986011162277941

theorem tailTrace_7215417 : CollatzResearch.WordTrace tailWord_7215417 prefixEnd_7215417 137221371986011162277941 := by
  unfold tailWord_7215417
  simp only [CollatzResearch.WordTrace]
  refine ⟨263167878100783978960684505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175445252067189319307123003 263167878100783978960684505)
  ·
    refine ⟨197375908575587984220513379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 263167878100783978960684505 197375908575587984220513379)
    ·
      refine ⟨296063862863381976330770069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197375908575587984220513379 296063862863381976330770069)
      ·
        refine ⟨13877993571721030140504847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 296063862863381976330770069 13877993571721030140504847)
        ·
          refine ⟨20816990357581545210757271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13877993571721030140504847 20816990357581545210757271)
          ·
            refine ⟨31225485536372317816135907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20816990357581545210757271 31225485536372317816135907)
            ·
              refine ⟨46838228304558476724203861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31225485536372317816135907 46838228304558476724203861)
              ·
                refine ⟨137221371986011162277941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 46838228304558476724203861 137221371986011162277941)
                ·
                  rfl

theorem cell23_7215417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 1, 10].length) (baseStart_7215417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7215417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7215417 prefixEnd_7215417 := by exact prefixLift 7215417
  have htrace : WordTrace (prefixWord ++ tailWord_7215417) baseStart_7215417 baseEnd_7215417 := by
    simpa [prefixWord, tailWord_7215417, baseEnd_7215417] using wordTrace_append hprefix tailTrace_7215417
  have hstable : (prefixWord ++ tailWord_7215417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7215417).length < 2 ^ (prefixWord ++ tailWord_7215417).sum := by decide
  have hdescent : baseEnd_7215417 < baseStart_7215417 := by decide
  rcases family_descends (prefixWord ++ tailWord_7215417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7215444 : List Nat := [2, 4, 1, 1, 2, 2, 1, 1, 3, 3, 3]
def baseStart_7215444 : Nat := 118140960795 + 7215444 * 2 ^ 59
def prefixEnd_7215444 : Nat := 4983230072969 + 3 ^ 40 * 7215444 * 2
def baseEnd_7215444 : Nat := 3704990907599972775866783

theorem tailTrace_7215444 : CollatzResearch.WordTrace tailWord_7215444 prefixEnd_7215444 3704990907599972775866783 := by
  unfold tailWord_7215444
  simp only [CollatzResearch.WordTrace]
  refine ⟨131584431435843081285958693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175445908581124108381278257 131584431435843081285958693)
  ·
    refine ⟨24672080894220577741117255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 131584431435843081285958693 24672080894220577741117255)
    ·
      refine ⟨37008121341330866611675883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24672080894220577741117255 37008121341330866611675883)
      ·
        refine ⟨55512182011996299917513825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37008121341330866611675883 55512182011996299917513825)
        ·
          refine ⟨41634136508997224938135369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55512182011996299917513825 41634136508997224938135369)
          ·
            refine ⟨31225602381747918703601527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41634136508997224938135369 31225602381747918703601527)
            ·
              refine ⟨46838403572621878055402291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31225602381747918703601527 46838403572621878055402291)
              ·
                refine ⟨70257605358932817083103437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46838403572621878055402291 70257605358932817083103437)
                ·
                  refine ⟨26346602009599806406163789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 70257605358932817083103437 26346602009599806406163789)
                  ·
                    refine ⟨9879975753599927402311421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26346602009599806406163789 9879975753599927402311421)
                    ·
                      refine ⟨3704990907599972775866783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9879975753599927402311421 3704990907599972775866783)
                      ·
                        rfl

theorem cell23_7215444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 1, 1, 3, 3, 3].length) (baseStart_7215444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7215444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7215444 prefixEnd_7215444 := by exact prefixLift 7215444
  have htrace : WordTrace (prefixWord ++ tailWord_7215444) baseStart_7215444 baseEnd_7215444 := by
    simpa [prefixWord, tailWord_7215444, baseEnd_7215444] using wordTrace_append hprefix tailTrace_7215444
  have hstable : (prefixWord ++ tailWord_7215444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7215444).length < 2 ^ (prefixWord ++ tailWord_7215444).sum := by decide
  have hdescent : baseEnd_7215444 < baseStart_7215444 := by decide
  rcases family_descends (prefixWord ++ tailWord_7215444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7215461 : List Nat := [1, 3, 1, 3, 1, 3, 1, 4, 2, 1, 3]
def baseStart_7215461 : Nat := 118140960795 + 7215461 * 2 ^ 59
def prefixEnd_7215461 : Nat := 4983230072969 + 3 ^ 40 * 7215461 * 2
def baseEnd_7215461 : Nat := 3704999636771099209354205

theorem tailTrace_7215461 : CollatzResearch.WordTrace tailWord_7215461 prefixEnd_7215461 3704999636771099209354205 := by
  unfold tailWord_7215461
  simp only [CollatzResearch.WordTrace]
  refine ⟨263169482912624574475286237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175446321941749716316857491 263169482912624574475286237)
  ·
    refine ⟨98688556092234215428232339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 263169482912624574475286237 98688556092234215428232339)
    ·
      refine ⟨148032834138351323142348509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98688556092234215428232339 148032834138351323142348509)
      ·
        refine ⟨55512312801881746178380691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 148032834138351323142348509 55512312801881746178380691)
        ·
          refine ⟨83268469202822619267571037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55512312801881746178380691 83268469202822619267571037)
          ·
            refine ⟨31225675951058482225339139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 83268469202822619267571037 31225675951058482225339139)
            ·
              refine ⟨46838513926587723338008709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31225675951058482225339139 46838513926587723338008709)
              ·
                refine ⟨8782221361235198125876633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46838513926587723338008709 8782221361235198125876633)
                ·
                  refine ⟨6586666020926398594407475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8782221361235198125876633 6586666020926398594407475)
                  ·
                    refine ⟨9879999031389597891611213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6586666020926398594407475 9879999031389597891611213)
                    ·
                      refine ⟨3704999636771099209354205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9879999031389597891611213 3704999636771099209354205)
                      ·
                        rfl

theorem cell23_7215461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 1, 4, 2, 1, 3].length) (baseStart_7215461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7215461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7215461 prefixEnd_7215461 := by exact prefixLift 7215461
  have htrace : WordTrace (prefixWord ++ tailWord_7215461) baseStart_7215461 baseEnd_7215461 := by
    simpa [prefixWord, tailWord_7215461, baseEnd_7215461] using wordTrace_append hprefix tailTrace_7215461
  have hstable : (prefixWord ++ tailWord_7215461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7215461).length < 2 ^ (prefixWord ++ tailWord_7215461).sum := by decide
  have hdescent : baseEnd_7215461 < baseStart_7215461 := by decide
  rcases family_descends (prefixWord ++ tailWord_7215461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7215514 : List Nat := [3, 1, 1, 4, 1, 2, 1, 2, 2, 2, 4]
def baseStart_7215514 : Nat := 118140960795 + 7215514 * 2 ^ 59
def prefixEnd_7215514 : Nat := 4983230072969 + 3 ^ 40 * 7215514 * 2
def baseEnd_7215514 : Nat := 3705026851245787501991461

theorem tailTrace_7215514 : CollatzResearch.WordTrace tailWord_7215514 prefixEnd_7215514 3705026851245787501991461 := by
  unfold tailWord_7215514
  simp only [CollatzResearch.WordTrace]
  refine ⟨65792853995358141131741399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175447610654288376351310397 65792853995358141131741399)
  ·
    refine ⟨98689280993037211697612099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65792853995358141131741399 98689280993037211697612099)
    ·
      refine ⟨148033921489555817546418149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98689280993037211697612099 148033921489555817546418149)
      ·
        refine ⟨27756360279291715789953403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 148033921489555817546418149 27756360279291715789953403)
        ·
          refine ⟨41634540418937573684930105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27756360279291715789953403 41634540418937573684930105)
          ·
            refine ⟨31225905314203180263697579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41634540418937573684930105 31225905314203180263697579)
            ·
              refine ⟨46838857971304770395546369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31225905314203180263697579 46838857971304770395546369)
              ·
                refine ⟨35129143478478577796659777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46838857971304770395546369 35129143478478577796659777)
                ·
                  refine ⟨26346857608858933347494833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35129143478478577796659777 26346857608858933347494833)
                  ·
                    refine ⟨19760143206644200010621125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26346857608858933347494833 19760143206644200010621125)
                    ·
                      refine ⟨3705026851245787501991461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19760143206644200010621125 3705026851245787501991461)
                      ·
                        rfl

theorem cell23_7215514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 1, 2, 2, 2, 4].length) (baseStart_7215514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7215514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7215514 prefixEnd_7215514 := by exact prefixLift 7215514
  have htrace : WordTrace (prefixWord ++ tailWord_7215514) baseStart_7215514 baseEnd_7215514 := by
    simpa [prefixWord, tailWord_7215514, baseEnd_7215514] using wordTrace_append hprefix tailTrace_7215514
  have hstable : (prefixWord ++ tailWord_7215514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7215514).length < 2 ^ (prefixWord ++ tailWord_7215514).sum := by decide
  have hdescent : baseEnd_7215514 < baseStart_7215514 := by decide
  rcases family_descends (prefixWord ++ tailWord_7215514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7215586 : List Nat := [3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2]
def baseStart_7215586 : Nat := 118140960795 + 7215586 * 2 ^ 59
def prefixEnd_7215586 : Nat := 4983230072969 + 3 ^ 40 * 7215586 * 2
def baseEnd_7215586 : Nat := 3705063821852911220291131

theorem tailTrace_7215586 : CollatzResearch.WordTrace tailWord_7215586 prefixEnd_7215586 3705063821852911220291131 := by
  unfold tailWord_7215586
  simp only [CollatzResearch.WordTrace]
  refine ⟨65793510509292930205896653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175449361358114480549057741 65793510509292930205896653)
  ·
    refine ⟨24672566440984848827211245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65793510509292930205896653 24672566440984848827211245)
    ·
      refine ⟨9252212415369318310204217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24672566440984848827211245 9252212415369318310204217)
      ·
        refine ⟨6939159311526988732653163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9252212415369318310204217 6939159311526988732653163)
        ·
          refine ⟨10408738967290483098979745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6939159311526988732653163 10408738967290483098979745)
          ·
            refine ⟨7806554225467862324234809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10408738967290483098979745 7806554225467862324234809)
            ·
              refine ⟨5854915669100896743176107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7806554225467862324234809 5854915669100896743176107)
              ·
                refine ⟨8782373503651345114764161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5854915669100896743176107 8782373503651345114764161)
                ·
                  refine ⟨6586780127738508836073121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8782373503651345114764161 6586780127738508836073121)
                  ·
                    refine ⟨4940085095803881627054841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6586780127738508836073121 4940085095803881627054841)
                    ·
                      refine ⟨3705063821852911220291131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4940085095803881627054841 3705063821852911220291131)
                      ·
                        rfl

theorem cell23_7215586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2].length) (baseStart_7215586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7215586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7215586 prefixEnd_7215586 := by exact prefixLift 7215586
  have htrace : WordTrace (prefixWord ++ tailWord_7215586) baseStart_7215586 baseEnd_7215586 := by
    simpa [prefixWord, tailWord_7215586, baseEnd_7215586] using wordTrace_append hprefix tailTrace_7215586
  have hstable : (prefixWord ++ tailWord_7215586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7215586).length < 2 ^ (prefixWord ++ tailWord_7215586).sum := by decide
  have hdescent : baseEnd_7215586 < baseStart_7215586 := by decide
  rcases family_descends (prefixWord ++ tailWord_7215586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7215591 : List Nat := [1, 1, 5, 2, 1, 1, 2, 1, 1, 6, 2]
def baseStart_7215591 : Nat := 118140960795 + 7215591 * 2 ^ 59
def prefixEnd_7215591 : Nat := 4983230072969 + 3 ^ 40 * 7215591 * 2
def baseEnd_7215591 : Nat := 3705066389256183700728607

theorem tailTrace_7215591 : CollatzResearch.WordTrace tailWord_7215591 prefixEnd_7215591 3705066389256183700728607 := by
  unfold tailWord_7215591
  simp only [CollatzResearch.WordTrace]
  refine ⟨263174224402153606677518627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175449482934769071118345751 263174224402153606677518627)
  ·
    refine ⟨394761336603230410016277941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263174224402153606677518627 394761336603230410016277941)
    ·
      refine ⟨37008875306552850939026057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 394761336603230410016277941 37008875306552850939026057)
      ·
        refine ⟨27756656479914638204269543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37008875306552850939026057 27756656479914638204269543)
        ·
          refine ⟨41634984719871957306404315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27756656479914638204269543 41634984719871957306404315)
          ·
            refine ⟨62452477079807935959606473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41634984719871957306404315 62452477079807935959606473)
            ·
              refine ⟨46839357809855951969704855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62452477079807935959606473 46839357809855951969704855)
              ·
                refine ⟨70259036714783927954557283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46839357809855951969704855 70259036714783927954557283)
                ·
                  refine ⟨105388555072175891931835925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70259036714783927954557283 105388555072175891931835925)
                  ·
                    refine ⟨4940088519008244934304809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 105388555072175891931835925 4940088519008244934304809)
                    ·
                      refine ⟨3705066389256183700728607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4940088519008244934304809 3705066389256183700728607)
                      ·
                        rfl

theorem cell23_7215591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 2, 1, 1, 6, 2].length) (baseStart_7215591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7215591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7215591 prefixEnd_7215591 := by exact prefixLift 7215591
  have htrace : WordTrace (prefixWord ++ tailWord_7215591) baseStart_7215591 baseEnd_7215591 := by
    simpa [prefixWord, tailWord_7215591, baseEnd_7215591] using wordTrace_append hprefix tailTrace_7215591
  have hstable : (prefixWord ++ tailWord_7215591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7215591).length < 2 ^ (prefixWord ++ tailWord_7215591).sum := by decide
  have hdescent : baseEnd_7215591 < baseStart_7215591 := by decide
  rcases family_descends (prefixWord ++ tailWord_7215591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7215658 : List Nat := [3, 1, 4, 1, 1, 2, 1, 1, 5, 1, 3]
def baseStart_7215658 : Nat := 118140960795 + 7215658 * 2 ^ 59
def prefixEnd_7215658 : Nat := 4983230072969 + 3 ^ 40 * 7215658 * 2
def baseEnd_7215658 : Nat := 3705100792460034938590799

theorem tailTrace_7215658 : CollatzResearch.WordTrace tailWord_7215658 prefixEnd_7215658 3705100792460034938590799 := by
  unfold tailWord_7215658
  simp only [CollatzResearch.WordTrace]
  refine ⟨65794167023227719280051907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175451112061940584746805085 65794167023227719280051907)
  ·
    refine ⟨98691250534841578920077861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65794167023227719280051907 98691250534841578920077861)
    ·
      refine ⟨18504609475282796047514599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 98691250534841578920077861 18504609475282796047514599)
      ·
        refine ⟨27756914212924194071271899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18504609475282796047514599 27756914212924194071271899)
        ·
          refine ⟨41635371319386291106907849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27756914212924194071271899 41635371319386291106907849)
          ·
            refine ⟨31226528489539718330180887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41635371319386291106907849 31226528489539718330180887)
            ·
              refine ⟨46839792734309577495271331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31226528489539718330180887 46839792734309577495271331)
              ·
                refine ⟨70259689101464366242906997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46839792734309577495271331 70259689101464366242906997)
                ·
                  refine ⟨6586845853262284335272531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 70259689101464366242906997 6586845853262284335272531)
                  ·
                    refine ⟨9880268779893426502908797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6586845853262284335272531 9880268779893426502908797)
                    ·
                      refine ⟨3705100792460034938590799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9880268779893426502908797 3705100792460034938590799)
                      ·
                        rfl

theorem cell23_7215658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 1, 1, 5, 1, 3].length) (baseStart_7215658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7215658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7215658 prefixEnd_7215658 := by exact prefixLift 7215658
  have htrace : WordTrace (prefixWord ++ tailWord_7215658) baseStart_7215658 baseEnd_7215658 := by
    simpa [prefixWord, tailWord_7215658, baseEnd_7215658] using wordTrace_append hprefix tailTrace_7215658
  have hstable : (prefixWord ++ tailWord_7215658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7215658).length < 2 ^ (prefixWord ++ tailWord_7215658).sum := by decide
  have hdescent : baseEnd_7215658 < baseStart_7215658 := by decide
  rcases family_descends (prefixWord ++ tailWord_7215658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7215662 : List Nat := [4, 1, 3, 1, 4, 1, 1, 1, 2, 2, 3]
def baseStart_7215662 : Nat := 118140960795 + 7215662 * 2 ^ 59
def prefixEnd_7215662 : Nat := 4983230072969 + 3 ^ 40 * 7215662 * 2
def baseEnd_7215662 : Nat := 3705102846382652922940781

theorem tailTrace_7215662 : CollatzResearch.WordTrace tailWord_7215662 prefixEnd_7215662 3705102846382652922940781 := by
  unfold tailWord_7215662
  simp only [CollatzResearch.WordTrace]
  refine ⟨32897101748112048225419155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 175451209323264257202235493 32897101748112048225419155)
  ·
    refine ⟨49345652622168072338128733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32897101748112048225419155 49345652622168072338128733)
    ·
      refine ⟨18504619733313027126798275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49345652622168072338128733 18504619733313027126798275)
      ·
        refine ⟨27756929599969540690197413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18504619733313027126798275 27756929599969540690197413)
        ·
          refine ⟨5204424299994288879412015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27756929599969540690197413 5204424299994288879412015)
          ·
            refine ⟨7806636449991433319118023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5204424299994288879412015 7806636449991433319118023)
            ·
              refine ⟨11709954674987149978677035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7806636449991433319118023 11709954674987149978677035)
              ·
                refine ⟨17564932012480724968015553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11709954674987149978677035 17564932012480724968015553)
                ·
                  refine ⟨13173699009360543726011665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17564932012480724968015553 13173699009360543726011665)
                  ·
                    refine ⟨9880274257020407794508749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13173699009360543726011665 9880274257020407794508749)
                    ·
                      refine ⟨3705102846382652922940781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9880274257020407794508749 3705102846382652922940781)
                      ·
                        rfl

theorem cell23_7215662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 4, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 4, 1, 1, 1, 2, 2, 3].length) (baseStart_7215662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7215662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7215662 prefixEnd_7215662 := by exact prefixLift 7215662
  have htrace : WordTrace (prefixWord ++ tailWord_7215662) baseStart_7215662 baseEnd_7215662 := by
    simpa [prefixWord, tailWord_7215662, baseEnd_7215662] using wordTrace_append hprefix tailTrace_7215662
  have hstable : (prefixWord ++ tailWord_7215662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7215662).length < 2 ^ (prefixWord ++ tailWord_7215662).sum := by decide
  have hdescent : baseEnd_7215662 < baseStart_7215662 := by decide
  rcases family_descends (prefixWord ++ tailWord_7215662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7215701 : List Nat := [1, 3, 2, 2, 1, 1, 2, 1, 5, 2, 3]
def baseStart_7215701 : Nat := 118140960795 + 7215701 * 2 ^ 59
def prefixEnd_7215701 : Nat := 4983230072969 + 3 ^ 40 * 7215701 * 2
def baseEnd_7215701 : Nat := 3705122872128178270353101

theorem tailTrace_7215701 : CollatzResearch.WordTrace tailWord_7215701 prefixEnd_7215701 3705122872128178270353101 := by
  unfold tailWord_7215701
  simp only [CollatzResearch.WordTrace]
  refine ⟨263178236431755095464022957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175452157621170063642681971 263178236431755095464022957)
  ·
    refine ⟨98691838661908160799008609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 263178236431755095464022957 98691838661908160799008609)
    ·
      refine ⟨74018878996431120599256457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98691838661908160799008609 74018878996431120599256457)
      ·
        refine ⟨55514159247323340449442343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74018878996431120599256457 55514159247323340449442343)
        ·
          refine ⟨83271238870985010674163515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55514159247323340449442343 83271238870985010674163515)
          ·
            refine ⟨124906858306477516011245273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83271238870985010674163515 124906858306477516011245273)
            ·
              refine ⟨93680143729858137008433955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 124906858306477516011245273 93680143729858137008433955)
              ·
                refine ⟨140520215594787205512650933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 93680143729858137008433955 140520215594787205512650933)
                ·
                  refine ⟨13173770212011300516811025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 140520215594787205512650933 13173770212011300516811025)
                  ·
                    refine ⟨9880327659008475387608269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13173770212011300516811025 9880327659008475387608269)
                    ·
                      refine ⟨3705122872128178270353101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9880327659008475387608269 3705122872128178270353101)
                      ·
                        rfl

theorem cell23_7215701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 1, 5, 2, 3].length) (baseStart_7215701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7215701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7215701 prefixEnd_7215701 := by exact prefixLift 7215701
  have htrace : WordTrace (prefixWord ++ tailWord_7215701) baseStart_7215701 baseEnd_7215701 := by
    simpa [prefixWord, tailWord_7215701, baseEnd_7215701] using wordTrace_append hprefix tailTrace_7215701
  have hstable : (prefixWord ++ tailWord_7215701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7215701).length < 2 ^ (prefixWord ++ tailWord_7215701).sum := by decide
  have hdescent : baseEnd_7215701 < baseStart_7215701 := by decide
  rcases family_descends (prefixWord ++ tailWord_7215701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7215749 : List Nat := [1, 3, 1, 1, 4, 3, 3, 2, 1, 2, 2]
def baseStart_7215749 : Nat := 118140960795 + 7215749 * 2 ^ 59
def prefixEnd_7215749 : Nat := 4983230072969 + 3 ^ 40 * 7215749 * 2
def baseEnd_7215749 : Nat := 3705147519199594082552881

theorem tailTrace_7215749 : CollatzResearch.WordTrace tailWord_7215749 prefixEnd_7215749 3705147519199594082552881 := by
  unfold tailWord_7215749
  simp only [CollatzResearch.WordTrace]
  refine ⟨263179987135581199661770301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175453324757054133107846867 263179987135581199661770301)
  ·
    refine ⟨98692495175842949873163863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 263179987135581199661770301 98692495175842949873163863)
    ·
      refine ⟨148038742763764424809745795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98692495175842949873163863 148038742763764424809745795)
      ·
        refine ⟨222058114145646637214618693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148038742763764424809745795 222058114145646637214618693)
        ·
          refine ⟨41635896402308744477741005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 222058114145646637214618693 41635896402308744477741005)
          ·
            refine ⟨15613461150865779179152877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41635896402308744477741005 15613461150865779179152877)
            ·
              refine ⟨5855047931574667192182329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15613461150865779179152877 5855047931574667192182329)
              ·
                refine ⟨4391285948681000394136747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5855047931574667192182329 4391285948681000394136747)
                ·
                  refine ⟨6586928923021500591205121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4391285948681000394136747 6586928923021500591205121)
                  ·
                    refine ⟨4940196692266125443403841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6586928923021500591205121 4940196692266125443403841)
                    ·
                      refine ⟨3705147519199594082552881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4940196692266125443403841 3705147519199594082552881)
                      ·
                        rfl

theorem cell23_7215749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 3, 2, 1, 2, 2].length) (baseStart_7215749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7215749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7215749 prefixEnd_7215749 := by exact prefixLift 7215749
  have htrace : WordTrace (prefixWord ++ tailWord_7215749) baseStart_7215749 baseEnd_7215749 := by
    simpa [prefixWord, tailWord_7215749, baseEnd_7215749] using wordTrace_append hprefix tailTrace_7215749
  have hstable : (prefixWord ++ tailWord_7215749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7215749).length < 2 ^ (prefixWord ++ tailWord_7215749).sum := by decide
  have hdescent : baseEnd_7215749 < baseStart_7215749 := by decide
  rcases family_descends (prefixWord ++ tailWord_7215749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7215791 : List Nat := [1, 1, 2, 1, 2, 5, 2, 1, 2, 1, 5]
def baseStart_7215791 : Nat := 118140960795 + 7215791 * 2 ^ 59
def prefixEnd_7215791 : Nat := 4983230072969 + 3 ^ 40 * 7215791 * 2
def baseEnd_7215791 : Nat := 3705169085387082918227687

theorem tailTrace_7215791 : CollatzResearch.WordTrace tailWord_7215791 prefixEnd_7215791 3705169085387082918227687 := by
  unfold tailWord_7215791
  simp only [CollatzResearch.WordTrace]
  refine ⟨263181519001429040834799227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175454346000952693889866151 263181519001429040834799227)
  ·
    refine ⟨394772278502143561252198841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263181519001429040834799227 394772278502143561252198841)
    ·
      refine ⟨296079208876607670939149131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 394772278502143561252198841 296079208876607670939149131)
      ·
        refine ⟨444118813314911506408723697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 296079208876607670939149131 444118813314911506408723697)
        ·
          refine ⟨333089109986183629806542773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 444118813314911506408723697 333089109986183629806542773)
          ·
            refine ⟨31227104061204715294363385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 333089109986183629806542773 31227104061204715294363385)
            ·
              refine ⟨23420328045903536470772539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31227104061204715294363385 23420328045903536470772539)
              ·
                refine ⟨35130492068855304706158809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23420328045903536470772539 35130492068855304706158809)
                ·
                  refine ⟨26347869051641478529619107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35130492068855304706158809 26347869051641478529619107)
                  ·
                    refine ⟨39521803577462217794428661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26347869051641478529619107 39521803577462217794428661)
                    ·
                      refine ⟨3705169085387082918227687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39521803577462217794428661 3705169085387082918227687)
                      ·
                        rfl

theorem cell23_7215791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 2, 1, 2, 1, 5].length) (baseStart_7215791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7215791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7215791 prefixEnd_7215791 := by exact prefixLift 7215791
  have htrace : WordTrace (prefixWord ++ tailWord_7215791) baseStart_7215791 baseEnd_7215791 := by
    simpa [prefixWord, tailWord_7215791, baseEnd_7215791] using wordTrace_append hprefix tailTrace_7215791
  have hstable : (prefixWord ++ tailWord_7215791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7215791).length < 2 ^ (prefixWord ++ tailWord_7215791).sum := by decide
  have hdescent : baseEnd_7215791 < baseStart_7215791 := by decide
  rcases family_descends (prefixWord ++ tailWord_7215791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7215801 : List Nat := [1, 2, 1, 4, 1, 1, 1, 4, 2, 2, 4]
def baseStart_7215801 : Nat := 118140960795 + 7215801 * 2 ^ 59
def prefixEnd_7215801 : Nat := 4983230072969 + 3 ^ 40 * 7215801 * 2
def baseEnd_7215801 : Nat := 3705174220193627879102641

theorem tailTrace_7215801 : CollatzResearch.WordTrace tailWord_7215801 prefixEnd_7215801 3705174220193627879102641 := by
  unfold tailWord_7215801
  simp only [CollatzResearch.WordTrace]
  refine ⟨263181883731392812542663257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175454589154261875028442171 263181883731392812542663257)
  ·
    refine ⟨197386412798544609406997443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 263181883731392812542663257 197386412798544609406997443)
    ·
      refine ⟨296079619197816914110496165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197386412798544609406997443 296079619197816914110496165)
      ·
        refine ⟨55514928599590671395718031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 296079619197816914110496165 55514928599590671395718031)
        ·
          refine ⟨83272392899386007093577047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55514928599590671395718031 83272392899386007093577047)
          ·
            refine ⟨124908589349079010640365571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83272392899386007093577047 124908589349079010640365571)
            ·
              refine ⟨187362884023618515960548357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 124908589349079010640365571 187362884023618515960548357)
              ·
                refine ⟨35130540754428471742602817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 187362884023618515960548357 35130540754428471742602817)
                ·
                  refine ⟨26347905565821353806952113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35130540754428471742602817 26347905565821353806952113)
                  ·
                    refine ⟨19760929174366015355214085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26347905565821353806952113 19760929174366015355214085)
                    ·
                      refine ⟨3705174220193627879102641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19760929174366015355214085 3705174220193627879102641)
                      ·
                        rfl

theorem cell23_7215801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 4, 2, 2, 4].length) (baseStart_7215801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7215801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7215801 prefixEnd_7215801 := by exact prefixLift 7215801
  have htrace : WordTrace (prefixWord ++ tailWord_7215801) baseStart_7215801 baseEnd_7215801 := by
    simpa [prefixWord, tailWord_7215801, baseEnd_7215801] using wordTrace_append hprefix tailTrace_7215801
  have hstable : (prefixWord ++ tailWord_7215801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7215801).length < 2 ^ (prefixWord ++ tailWord_7215801).sum := by decide
  have hdescent : baseEnd_7215801 < baseStart_7215801 := by decide
  rcases family_descends (prefixWord ++ tailWord_7215801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7215818 : List Nat := [3, 1, 2, 1, 4, 2, 1, 1, 2, 2, 4]
def baseStart_7215818 : Nat := 118140960795 + 7215818 * 2 ^ 59
def prefixEnd_7215818 : Nat := 4983230072969 + 3 ^ 40 * 7215818 * 2
def baseEnd_7215818 : Nat := 3705182949364754312590063

theorem tailTrace_7215818 : CollatzResearch.WordTrace tailWord_7215818 prefixEnd_7215818 3705182949364754312590063 := by
  unfold tailWord_7215818
  simp only [CollatzResearch.WordTrace]
  refine ⟨65795625943082806111508027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175455002514887482964021405 65795625943082806111508027)
  ·
    refine ⟨98693438914624209167262041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65795625943082806111508027 98693438914624209167262041)
    ·
      refine ⟨74020079185968156875446531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98693438914624209167262041 74020079185968156875446531)
      ·
        refine ⟨111030118778952235313169797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74020079185968156875446531 111030118778952235313169797)
        ·
          refine ⟨20818147271053544121219337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 111030118778952235313169797 20818147271053544121219337)
          ·
            refine ⟨15613610453290158090914503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20818147271053544121219337 15613610453290158090914503)
            ·
              refine ⟨23420415679935237136371755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15613610453290158090914503 23420415679935237136371755)
              ·
                refine ⟨35130623519902855704557633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23420415679935237136371755 35130623519902855704557633)
                ·
                  refine ⟨26347967639927141778418225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35130623519902855704557633 26347967639927141778418225)
                  ·
                    refine ⟨19760975729945356333813669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26347967639927141778418225 19760975729945356333813669)
                    ·
                      refine ⟨3705182949364754312590063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19760975729945356333813669 3705182949364754312590063)
                      ·
                        rfl

theorem cell23_7215818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 1, 1, 2, 2, 4].length) (baseStart_7215818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7215818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7215818 prefixEnd_7215818 := by exact prefixLift 7215818
  have htrace : WordTrace (prefixWord ++ tailWord_7215818) baseStart_7215818 baseEnd_7215818 := by
    simpa [prefixWord, tailWord_7215818, baseEnd_7215818] using wordTrace_append hprefix tailTrace_7215818
  have hstable : (prefixWord ++ tailWord_7215818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7215818).length < 2 ^ (prefixWord ++ tailWord_7215818).sum := by decide
  have hdescent : baseEnd_7215818 < baseStart_7215818 := by decide
  rcases family_descends (prefixWord ++ tailWord_7215818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7215822 : List Nat := [4, 1, 1, 1, 3, 2, 2, 3, 2, 2, 2]
def baseStart_7215822 : Nat := 118140960795 + 7215822 * 2 ^ 59
def prefixEnd_7215822 : Nat := 4983230072969 + 3 ^ 40 * 7215822 * 2
def baseEnd_7215822 : Nat := 3705185003287372296940045

theorem tailTrace_7215822 : CollatzResearch.WordTrace tailWord_7215822 prefixEnd_7215822 3705185003287372296940045 := by
  unfold tailWord_7215822
  simp only [CollatzResearch.WordTrace]
  refine ⟨32897831208039591641147215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 175455099776211155419451813 32897831208039591641147215)
  ·
    refine ⟨49346746812059387461720823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32897831208039591641147215 49346746812059387461720823)
    ·
      refine ⟨74020120218089081192581235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49346746812059387461720823 74020120218089081192581235)
      ·
        refine ⟨111030180327133621788871853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74020120218089081192581235 111030180327133621788871853)
        ·
          refine ⟨41636317622675108170826945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 111030180327133621788871853 41636317622675108170826945)
          ·
            refine ⟨31227238217006331128120209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41636317622675108170826945 31227238217006331128120209)
            ·
              refine ⟨23420428662754748346090157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31227238217006331128120209 23420428662754748346090157)
              ·
                refine ⟨8782660748533030629783809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23420428662754748346090157 8782660748533030629783809)
                ·
                  refine ⟨6586995561399772972337857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8782660748533030629783809 6586995561399772972337857)
                  ·
                    refine ⟨4940246671049829729253393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6586995561399772972337857 4940246671049829729253393)
                    ·
                      refine ⟨3705185003287372296940045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4940246671049829729253393 3705185003287372296940045)
                      ·
                        rfl

theorem cell23_7215822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 2, 3, 2, 2, 2].length) (baseStart_7215822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7215822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7215822 prefixEnd_7215822 := by exact prefixLift 7215822
  have htrace : WordTrace (prefixWord ++ tailWord_7215822) baseStart_7215822 baseEnd_7215822 := by
    simpa [prefixWord, tailWord_7215822, baseEnd_7215822] using wordTrace_append hprefix tailTrace_7215822
  have hstable : (prefixWord ++ tailWord_7215822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7215822).length < 2 ^ (prefixWord ++ tailWord_7215822).sum := by decide
  have hdescent : baseEnd_7215822 < baseStart_7215822 := by decide
  rcases family_descends (prefixWord ++ tailWord_7215822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7215845 : List Nat := [1, 3, 1, 4, 1, 3, 2, 3, 5]
def baseStart_7215845 : Nat := 118140960795 + 7215845 * 2 ^ 59
def prefixEnd_7215845 : Nat := 4983230072969 + 3 ^ 40 * 7215845 * 2
def baseEnd_7215845 : Nat := 411688534815825078550271

theorem tailTrace_7215845 : CollatzResearch.WordTrace tailWord_7215845 prefixEnd_7215845 411688534815825078550271 := by
  unfold tailWord_7215845
  simp only [CollatzResearch.WordTrace]
  refine ⟨263183488543233408057264989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175455659028822272038176659 263183488543233408057264989)
  ·
    refine ⟨98693808203712528021474371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 263183488543233408057264989 98693808203712528021474371)
    ·
      refine ⟨148040712305568792032211557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98693808203712528021474371 148040712305568792032211557)
      ·
        refine ⟨27757633557294148506039667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 148040712305568792032211557 27757633557294148506039667)
        ·
          refine ⟨41636450335941222759059501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27757633557294148506039667 41636450335941222759059501)
          ·
            refine ⟨15613668875977958534647313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41636450335941222759059501 15613668875977958534647313)
            ·
              refine ⟨11710251656983468900985485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15613668875977958534647313 11710251656983468900985485)
              ·
                refine ⟨4391344371368800837869557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11710251656983468900985485 4391344371368800837869557)
                ·
                  refine ⟨411688534815825078550271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4391344371368800837869557 411688534815825078550271)
                  ·
                    rfl

theorem cell23_7215845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 2, 3, 5].length) (baseStart_7215845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7215845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7215845 prefixEnd_7215845 := by exact prefixLift 7215845
  have htrace : WordTrace (prefixWord ++ tailWord_7215845) baseStart_7215845 baseEnd_7215845 := by
    simpa [prefixWord, tailWord_7215845, baseEnd_7215845] using wordTrace_append hprefix tailTrace_7215845
  have hstable : (prefixWord ++ tailWord_7215845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7215845).length < 2 ^ (prefixWord ++ tailWord_7215845).sum := by decide
  have hdescent : baseEnd_7215845 < baseStart_7215845 := by decide
  rcases family_descends (prefixWord ++ tailWord_7215845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7215891 : List Nat := [1, 1, 1, 2, 1, 3, 3, 1, 2, 4, 4]
def baseStart_7215891 : Nat := 118140960795 + 7215891 * 2 ^ 59
def prefixEnd_7215891 : Nat := 4983230072969 + 3 ^ 40 * 7215891 * 2
def baseEnd_7215891 : Nat := 3705220433452532526977227

theorem tailTrace_7215891 : CollatzResearch.WordTrace tailWord_7215891 prefixEnd_7215891 3705220433452532526977227 := by
  unfold tailWord_7215891
  simp only [CollatzResearch.WordTrace]
  refine ⟨263185166301066757913439527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175456777534044505275626351 263185166301066757913439527)
  ·
    refine ⟨394777749451600136870159291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263185166301066757913439527 394777749451600136870159291)
    ·
      refine ⟨592166624177400205305238937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 394777749451600136870159291 592166624177400205305238937)
      ·
        refine ⟨444124968133050153978929203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 592166624177400205305238937 444124968133050153978929203)
        ·
          refine ⟨666187452199575230968393805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 444124968133050153978929203 666187452199575230968393805)
          ·
            refine ⟨249820294574840711613147677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 666187452199575230968393805 249820294574840711613147677)
            ·
              refine ⟨93682610465565266854930379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 249820294574840711613147677 93682610465565266854930379)
              ·
                refine ⟨140523915698347900282395569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 93682610465565266854930379 140523915698347900282395569)
                ·
                  refine ⟨105392936773760925211796677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 140523915698347900282395569 105392936773760925211796677)
                  ·
                    refine ⟨19761175645080173477211877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 105392936773760925211796677 19761175645080173477211877)
                    ·
                      refine ⟨3705220433452532526977227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19761175645080173477211877 3705220433452532526977227)
                      ·
                        rfl

theorem cell23_7215891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 1, 2, 4, 4].length) (baseStart_7215891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7215891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7215891 prefixEnd_7215891 := by exact prefixLift 7215891
  have htrace : WordTrace (prefixWord ++ tailWord_7215891) baseStart_7215891 baseEnd_7215891 := by
    simpa [prefixWord, tailWord_7215891, baseEnd_7215891] using wordTrace_append hprefix tailTrace_7215891
  have hstable : (prefixWord ++ tailWord_7215891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7215891).length < 2 ^ (prefixWord ++ tailWord_7215891).sum := by decide
  have hdescent : baseEnd_7215891 < baseStart_7215891 := by decide
  rcases family_descends (prefixWord ++ tailWord_7215891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7215898 : List Nat := [3, 1, 1, 3, 2, 1, 1, 3, 1, 4, 3]
def baseStart_7215898 : Nat := 118140960795 + 7215898 * 2 ^ 59
def prefixEnd_7215898 : Nat := 4983230072969 + 3 ^ 40 * 7215898 * 2
def baseEnd_7215898 : Nat := 3705224027817113999589695

theorem tailTrace_7215898 : CollatzResearch.WordTrace tailWord_7215898 prefixEnd_7215898 3705224027817113999589695 := by
  unfold tailWord_7215898
  simp only [CollatzResearch.WordTrace]
  refine ⟨65796355403010349527236087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175456947741360932072629565 65796355403010349527236087)
  ·
    refine ⟨98694533104515524290854131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65796355403010349527236087 98694533104515524290854131)
    ·
      refine ⟨148041799656773286436281197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98694533104515524290854131 148041799656773286436281197)
      ·
        refine ⟨55515674871289982413605449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 148041799656773286436281197 55515674871289982413605449)
        ·
          refine ⟨41636756153467486810204087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55515674871289982413605449 41636756153467486810204087)
          ·
            refine ⟨62455134230201230215306131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41636756153467486810204087 62455134230201230215306131)
            ·
              refine ⟨93682701345301845322959197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62455134230201230215306131 93682701345301845322959197)
              ·
                refine ⟨35131013004488191996109699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 93682701345301845322959197 35131013004488191996109699)
                ·
                  refine ⟨52696519506732287994164549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35131013004488191996109699 52696519506732287994164549)
                  ·
                    refine ⟨9880597407512303998905853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 52696519506732287994164549 9880597407512303998905853)
                    ·
                      refine ⟨3705224027817113999589695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9880597407512303998905853 3705224027817113999589695)
                      ·
                        rfl

theorem cell23_7215898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 3, 1, 4, 3].length) (baseStart_7215898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7215898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7215898 prefixEnd_7215898 := by exact prefixLift 7215898
  have htrace : WordTrace (prefixWord ++ tailWord_7215898) baseStart_7215898 baseEnd_7215898 := by
    simpa [prefixWord, tailWord_7215898, baseEnd_7215898] using wordTrace_append hprefix tailTrace_7215898
  have hstable : (prefixWord ++ tailWord_7215898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7215898).length < 2 ^ (prefixWord ++ tailWord_7215898).sum := by decide
  have hdescent : baseEnd_7215898 < baseStart_7215898 := by decide
  rcases family_descends (prefixWord ++ tailWord_7215898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7215935 : List Nat := [1, 1, 2, 2, 5, 1, 4, 1, 6]
def baseStart_7215935 : Nat := 118140960795 + 7215935 * 2 ^ 59
def prefixEnd_7215935 : Nat := 4983230072969 + 3 ^ 40 * 7215935 * 2
def baseEnd_7215935 : Nat := 411693669622370039425225

theorem tailTrace_7215935 : CollatzResearch.WordTrace tailWord_7215935 prefixEnd_7215935 411693669622370039425225 := by
  unfold tailWord_7215935
  simp only [CollatzResearch.WordTrace]
  refine ⟨263186771112907353428041259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175457847408604902285360839 263186771112907353428041259)
  ·
    refine ⟨394780156669361030142061889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263186771112907353428041259 394780156669361030142061889)
    ·
      refine ⟨296085117502020772606546417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 394780156669361030142061889 296085117502020772606546417)
      ·
        refine ⟨222063838126515579454909813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 296085117502020772606546417 222063838126515579454909813)
        ·
          refine ⟨20818484824360835573897795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 222063838126515579454909813 20818484824360835573897795)
          ·
            refine ⟨31227727236541253360846693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20818484824360835573897795 31227727236541253360846693)
            ·
              refine ⟨5855198856851485005158755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31227727236541253360846693 5855198856851485005158755)
              ·
                refine ⟨8782798285277227507738133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5855198856851485005158755 8782798285277227507738133)
                ·
                  refine ⟨411693669622370039425225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8782798285277227507738133 411693669622370039425225)
                  ·
                    rfl

theorem cell23_7215935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 4, 1, 6].length) (baseStart_7215935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7215935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7215935 prefixEnd_7215935 := by exact prefixLift 7215935
  have htrace : WordTrace (prefixWord ++ tailWord_7215935) baseStart_7215935 baseEnd_7215935 := by
    simpa [prefixWord, tailWord_7215935, baseEnd_7215935] using wordTrace_append hprefix tailTrace_7215935
  have hstable : (prefixWord ++ tailWord_7215935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7215935).length < 2 ^ (prefixWord ++ tailWord_7215935).sum := by decide
  have hdescent : baseEnd_7215935 < baseStart_7215935 := by decide
  rcases family_descends (prefixWord ++ tailWord_7215935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7215941 : List Nat := [1, 3, 1, 1, 1, 2, 2, 1, 1, 3, 7]
def baseStart_7215941 : Nat := 118140960795 + 7215941 * 2 ^ 59
def prefixEnd_7215941 : Nat := 4983230072969 + 3 ^ 40 * 7215941 * 2
def baseEnd_7215941 : Nat := 3705246107485257331351997

theorem tailTrace_7215941 : CollatzResearch.WordTrace tailWord_7215941 prefixEnd_7215941 3705246107485257331351997 := by
  unfold tailWord_7215941
  simp only [CollatzResearch.WordTrace]
  refine ⟨263186989950885616452759677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175457993300590410968506451 263186989950885616452759677)
  ·
    refine ⟨98695121231582106169784879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 263186989950885616452759677 98695121231582106169784879)
    ·
      refine ⟨148042681847373159254677319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98695121231582106169784879 148042681847373159254677319)
      ·
        refine ⟨222064022771059738882015979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148042681847373159254677319 222064022771059738882015979)
        ·
          refine ⟨333096034156589608323023969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 222064022771059738882015979 333096034156589608323023969)
          ·
            refine ⟨249822025617442206242267977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 333096034156589608323023969 249822025617442206242267977)
            ·
              refine ⟨187366519213081654681700983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 249822025617442206242267977 187366519213081654681700983)
              ·
                refine ⟨281049778819622482022551475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 187366519213081654681700983 281049778819622482022551475)
                ·
                  refine ⟨421574668229433723033827213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 281049778819622482022551475 421574668229433723033827213)
                  ·
                    refine ⟨158090500586037646137685205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 421574668229433723033827213 158090500586037646137685205)
                    ·
                      refine ⟨3705246107485257331351997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 158090500586037646137685205 3705246107485257331351997)
                      ·
                        rfl

theorem cell23_7215941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 1, 1, 3, 7].length) (baseStart_7215941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7215941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7215941 prefixEnd_7215941 := by exact prefixLift 7215941
  have htrace : WordTrace (prefixWord ++ tailWord_7215941) baseStart_7215941 baseEnd_7215941 := by
    simpa [prefixWord, tailWord_7215941, baseEnd_7215941] using wordTrace_append hprefix tailTrace_7215941
  have hstable : (prefixWord ++ tailWord_7215941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7215941).length < 2 ^ (prefixWord ++ tailWord_7215941).sum := by decide
  have hdescent : baseEnd_7215941 < baseStart_7215941 := by decide
  rcases family_descends (prefixWord ++ tailWord_7215941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7215949 : List Nat := [1, 6, 1, 2, 2, 1, 2, 1, 2, 2, 3]
def baseStart_7215949 : Nat := 118140960795 + 7215949 * 2 ^ 59
def prefixEnd_7215949 : Nat := 4983230072969 + 3 ^ 40 * 7215949 * 2
def baseEnd_7215949 : Nat := 3705250215330493300051961

theorem tailTrace_7215949 : CollatzResearch.WordTrace tailWord_7215949 prefixEnd_7215949 3705250215330493300051961 := by
  unfold tailWord_7215949
  simp only [CollatzResearch.WordTrace]
  refine ⟨263187281734856633819050901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175458187823237755879367267 263187281734856633819050901)
  ·
    refine ⟨12336903831321404710268011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 263187281734856633819050901 12336903831321404710268011)
    ·
      refine ⟨18505355746982107065402017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12336903831321404710268011 18505355746982107065402017)
      ·
        refine ⟨13879016810236580299051513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18505355746982107065402017 13879016810236580299051513)
        ·
          refine ⟨10409262607677435224288635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13879016810236580299051513 10409262607677435224288635)
          ·
            refine ⟨15613893911516152836432953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10409262607677435224288635 15613893911516152836432953)
            ·
              refine ⟨11710420433637114627324715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15613893911516152836432953 11710420433637114627324715)
              ·
                refine ⟨17565630650455671940987073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11710420433637114627324715 17565630650455671940987073)
                ·
                  refine ⟨13174222987841753955740305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17565630650455671940987073 13174222987841753955740305)
                  ·
                    refine ⟨9880667240881315466805229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13174222987841753955740305 9880667240881315466805229)
                    ·
                      refine ⟨3705250215330493300051961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9880667240881315466805229 3705250215330493300051961)
                      ·
                        rfl

theorem cell23_7215949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 2, 1, 2, 2, 3].length) (baseStart_7215949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7215949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7215949 prefixEnd_7215949 := by exact prefixLift 7215949
  have htrace : WordTrace (prefixWord ++ tailWord_7215949) baseStart_7215949 baseEnd_7215949 := by
    simpa [prefixWord, tailWord_7215949, baseEnd_7215949] using wordTrace_append hprefix tailTrace_7215949
  have hstable : (prefixWord ++ tailWord_7215949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7215949).length < 2 ^ (prefixWord ++ tailWord_7215949).sum := by decide
  have hdescent : baseEnd_7215949 < baseStart_7215949 := by decide
  rcases family_descends (prefixWord ++ tailWord_7215949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7215972 : List Nat := [2, 3, 1, 1, 4, 1, 2, 2, 2, 3, 2]
def baseStart_7215972 : Nat := 118140960795 + 7215972 * 2 ^ 59
def prefixEnd_7215972 : Nat := 4983230072969 + 3 ^ 40 * 7215972 * 2
def baseEnd_7215972 : Nat := 3705262025385546710064355

theorem tailTrace_7215972 : CollatzResearch.WordTrace tailWord_7215972 prefixEnd_7215972 3705262025385546710064355 := by
  unfold tailWord_7215972
  simp only [CollatzResearch.WordTrace]
  refine ⟨131594060306886654373569085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175458747075848872498092113 131594060306886654373569085)
  ·
    refine ⟨49347772615082495390088407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 131594060306886654373569085 49347772615082495390088407)
    ·
      refine ⟨74021658922623743085132611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49347772615082495390088407 74021658922623743085132611)
      ·
        refine ⟨111032488383935614627698917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74021658922623743085132611 111032488383935614627698917)
        ·
          refine ⟨20818591571987927742693547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 111032488383935614627698917 20818591571987927742693547)
          ·
            refine ⟨31227887357981891614040321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20818591571987927742693547 31227887357981891614040321)
            ·
              refine ⟨23420915518486418710530241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31227887357981891614040321 23420915518486418710530241)
              ·
                refine ⟨17565686638864814032897681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23420915518486418710530241 17565686638864814032897681)
                ·
                  refine ⟨13174264979148610524673261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17565686638864814032897681 13174264979148610524673261)
                  ·
                    refine ⟨4940349367180728946752473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13174264979148610524673261 4940349367180728946752473)
                    ·
                      refine ⟨3705262025385546710064355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4940349367180728946752473 3705262025385546710064355)
                      ·
                        rfl

theorem cell23_7215972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 2, 2, 2, 3, 2].length) (baseStart_7215972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7215972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7215972 prefixEnd_7215972 := by exact prefixLift 7215972
  have htrace : WordTrace (prefixWord ++ tailWord_7215972) baseStart_7215972 baseEnd_7215972 := by
    simpa [prefixWord, tailWord_7215972, baseEnd_7215972] using wordTrace_append hprefix tailTrace_7215972
  have hstable : (prefixWord ++ tailWord_7215972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7215972).length < 2 ^ (prefixWord ++ tailWord_7215972).sum := by decide
  have hdescent : baseEnd_7215972 < baseStart_7215972 := by decide
  rcases family_descends (prefixWord ++ tailWord_7215972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7215979 : List Nat := [1, 1, 1, 1, 2, 2, 8, 2, 1, 1, 3]
def baseStart_7215979 : Nat := 118140960795 + 7215979 * 2 ^ 59
def prefixEnd_7215979 : Nat := 4983230072969 + 3 ^ 40 * 7215979 * 2
def baseEnd_7215979 : Nat := 3705265619750128182676823

theorem tailTrace_7215979 : CollatzResearch.WordTrace tailWord_7215979 prefixEnd_7215979 3705265619750128182676823 := by
  unfold tailWord_7215979
  simp only [CollatzResearch.WordTrace]
  refine ⟨263188375924747948942642991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175458917283165299295095327 263188375924747948942642991)
  ·
    refine ⟨394782563887121923413964487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263188375924747948942642991 394782563887121923413964487)
    ·
      refine ⟨592173845830682885120946731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 394782563887121923413964487 592173845830682885120946731)
      ·
        refine ⟨888260768746024327681420097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 592173845830682885120946731 888260768746024327681420097)
        ·
          refine ⟨666195576559518245761065073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 888260768746024327681420097 666195576559518245761065073)
          ·
            refine ⟨499646682419638684320798805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 666195576559518245761065073 499646682419638684320798805)
            ·
              refine ⟨5855234559605140831884361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 499646682419638684320798805 5855234559605140831884361)
              ·
                refine ⟨4391425919703855623913271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5855234559605140831884361 4391425919703855623913271)
                ·
                  refine ⟨6587138879555783435869907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4391425919703855623913271 6587138879555783435869907)
                  ·
                    refine ⟨9880708319333675153804861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6587138879555783435869907 9880708319333675153804861)
                    ·
                      refine ⟨3705265619750128182676823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9880708319333675153804861 3705265619750128182676823)
                      ·
                        rfl

theorem cell23_7215979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 8, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 8, 2, 1, 1, 3].length) (baseStart_7215979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7215979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7215979 prefixEnd_7215979 := by exact prefixLift 7215979
  have htrace : WordTrace (prefixWord ++ tailWord_7215979) baseStart_7215979 baseEnd_7215979 := by
    simpa [prefixWord, tailWord_7215979, baseEnd_7215979] using wordTrace_append hprefix tailTrace_7215979
  have hstable : (prefixWord ++ tailWord_7215979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7215979).length < 2 ^ (prefixWord ++ tailWord_7215979).sum := by decide
  have hdescent : baseEnd_7215979 < baseStart_7215979 := by decide
  rcases family_descends (prefixWord ++ tailWord_7215979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7215995 : List Nat := [1, 1, 1, 1, 1, 5, 4, 3, 2, 4]
def baseStart_7215995 : Nat := 118140960795 + 7215995 * 2 ^ 59
def prefixEnd_7215995 : Nat := 4983230072969 + 3 ^ 40 * 7215995 * 2
def baseEnd_7215995 : Nat := 1235091278480200040025583

theorem tailTrace_7215995 : CollatzResearch.WordTrace tailWord_7215995 prefixEnd_7215995 1235091278480200040025583 := by
  unfold tailWord_7215995
  simp only [CollatzResearch.WordTrace]
  refine ⟨263188959492689983675225439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175459306328459989116816959 263188959492689983675225439)
  ·
    refine ⟨394783439239034975512838159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263188959492689983675225439 394783439239034975512838159)
    ·
      refine ⟨592175158858552463269257239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 394783439239034975512838159 592175158858552463269257239)
      ·
        refine ⟨888262738287828694903885859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 592175158858552463269257239 888262738287828694903885859)
        ·
          refine ⟨1332394107431743042355828789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 888262738287828694903885859 1332394107431743042355828789)
          ·
            refine ⟨124911947571725910220858949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1332394107431743042355828789 124911947571725910220858949)
            ·
              refine ⟨23420990169698608166411053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 124911947571725910220858949 23420990169698608166411053)
              ·
                refine ⟨8782871313636978062404145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23420990169698608166411053 8782871313636978062404145)
                ·
                  refine ⟨6587153485227733546803109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8782871313636978062404145 6587153485227733546803109)
                  ·
                    refine ⟨1235091278480200040025583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6587153485227733546803109 1235091278480200040025583)
                    ·
                      rfl

theorem cell23_7215995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 4, 3, 2, 4].length) (baseStart_7215995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7215995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7215995 prefixEnd_7215995 := by exact prefixLift 7215995
  have htrace : WordTrace (prefixWord ++ tailWord_7215995) baseStart_7215995 baseEnd_7215995 := by
    simpa [prefixWord, tailWord_7215995, baseEnd_7215995] using wordTrace_append hprefix tailTrace_7215995
  have hstable : (prefixWord ++ tailWord_7215995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7215995).length < 2 ^ (prefixWord ++ tailWord_7215995).sum := by decide
  have hdescent : baseEnd_7215995 < baseStart_7215995 := by decide
  rcases family_descends (prefixWord ++ tailWord_7215995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7216005 : List Nat := [1, 3, 1, 1, 3, 3, 2, 1, 3, 2, 3]
def baseStart_7216005 : Nat := 118140960795 + 7216005 * 2 ^ 59
def prefixEnd_7216005 : Nat := 4983230072969 + 3 ^ 40 * 7216005 * 2
def baseEnd_7216005 : Nat := 3705278970247145080951703

theorem tailTrace_7216005 : CollatzResearch.WordTrace tailWord_7216005 prefixEnd_7216005 3705278970247145080951703 := by
  unfold tailWord_7216005
  simp only [CollatzResearch.WordTrace]
  refine ⟨263189324222653755383089469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175459549481769170255392979 263189324222653755383089469)
  ·
    refine ⟨98695996583495158268658551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 263189324222653755383089469 98695996583495158268658551)
    ·
      refine ⟨148043994875242737402987827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98695996583495158268658551 148043994875242737402987827)
      ·
        refine ⟨222065992312864106104481741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148043994875242737402987827 222065992312864106104481741)
        ·
          refine ⟨83274747117324039789180653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 222065992312864106104481741 83274747117324039789180653)
          ·
            refine ⟨31228030168996514920942745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 83274747117324039789180653 31228030168996514920942745)
            ·
              refine ⟨23421022626747386190707059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31228030168996514920942745 23421022626747386190707059)
              ·
                refine ⟨35131533940121079286060589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23421022626747386190707059 35131533940121079286060589)
                ·
                  refine ⟨13174325227545404732272721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35131533940121079286060589 13174325227545404732272721)
                  ·
                    refine ⟨9880743920659053549204541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13174325227545404732272721 9880743920659053549204541)
                    ·
                      refine ⟨3705278970247145080951703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9880743920659053549204541 3705278970247145080951703)
                      ·
                        rfl

theorem cell23_7216005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 2, 1, 3, 2, 3].length) (baseStart_7216005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7216005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7216005 prefixEnd_7216005 := by exact prefixLift 7216005
  have htrace : WordTrace (prefixWord ++ tailWord_7216005) baseStart_7216005 baseEnd_7216005 := by
    simpa [prefixWord, tailWord_7216005, baseEnd_7216005] using wordTrace_append hprefix tailTrace_7216005
  have hstable : (prefixWord ++ tailWord_7216005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7216005).length < 2 ^ (prefixWord ++ tailWord_7216005).sum := by decide
  have hdescent : baseEnd_7216005 < baseStart_7216005 := by decide
  rcases family_descends (prefixWord ++ tailWord_7216005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7216049 : List Nat := [1, 2, 2, 4, 4, 1, 1, 1, 1, 2, 4]
def baseStart_7216049 : Nat := 118140960795 + 7216049 * 2 ^ 59
def prefixEnd_7216049 : Nat := 4983230072969 + 3 ^ 40 * 7216049 * 2
def baseEnd_7216049 : Nat := 3705301563395942908801501

theorem tailTrace_7216049 : CollatzResearch.WordTrace tailWord_7216049 prefixEnd_7216049 3705301563395942908801501 := by
  unfold tailWord_7216049
  simp only [CollatzResearch.WordTrace]
  refine ⟨263190929034494350897691201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175460619356329567265127467 263190929034494350897691201)
  ·
    refine ⟨197393196775870763173268401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 263190929034494350897691201 197393196775870763173268401)
    ·
      refine ⟨148044897581903072379951301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 197393196775870763173268401 148044897581903072379951301)
      ·
        refine ⟨27758418296606826071240869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 148044897581903072379951301 27758418296606826071240869)
        ·
          refine ⟨5204703430613779888357663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27758418296606826071240869 5204703430613779888357663)
          ·
            refine ⟨7807055145920669832536495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5204703430613779888357663 7807055145920669832536495)
            ·
              refine ⟨11710582718881004748804743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7807055145920669832536495 11710582718881004748804743)
              ·
                refine ⟨17565874078321507123207115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11710582718881004748804743 17565874078321507123207115)
                ·
                  refine ⟨26348811117482260684810673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17565874078321507123207115 26348811117482260684810673)
                  ·
                    refine ⟨19761608338111695513608005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26348811117482260684810673 19761608338111695513608005)
                    ·
                      refine ⟨3705301563395942908801501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19761608338111695513608005 3705301563395942908801501)
                      ·
                        rfl

theorem cell23_7216049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 4, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 4, 1, 1, 1, 1, 2, 4].length) (baseStart_7216049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7216049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7216049 prefixEnd_7216049 := by exact prefixLift 7216049
  have htrace : WordTrace (prefixWord ++ tailWord_7216049) baseStart_7216049 baseEnd_7216049 := by
    simpa [prefixWord, tailWord_7216049, baseEnd_7216049] using wordTrace_append hprefix tailTrace_7216049
  have hstable : (prefixWord ++ tailWord_7216049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7216049).length < 2 ^ (prefixWord ++ tailWord_7216049).sum := by decide
  have hdescent : baseEnd_7216049 < baseStart_7216049 := by decide
  rcases family_descends (prefixWord ++ tailWord_7216049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7216125 : List Nat := [1, 4, 1, 1, 1, 2, 1, 2, 4, 3, 3]
def baseStart_7216125 : Nat := 118140960795 + 7216125 * 2 ^ 59
def prefixEnd_7216125 : Nat := 4983230072969 + 3 ^ 40 * 7216125 * 2
def baseEnd_7216125 : Nat := 3705340587925684611451151

theorem tailTrace_7216125 : CollatzResearch.WordTrace tailWord_7216125 prefixEnd_7216125 3705340587925684611451151 := by
  unfold tailWord_7216125
  simp only [CollatzResearch.WordTrace]
  refine ⟨263193700982219015877457829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175462467321479343918305219 263193700982219015877457829)
  ·
    refine ⟨49348818934166065477023343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 263193700982219015877457829 49348818934166065477023343)
    ·
      refine ⟨74023228401249098215535015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49348818934166065477023343 74023228401249098215535015)
      ·
        refine ⟨111034842601873647323302523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74023228401249098215535015 111034842601873647323302523)
        ·
          refine ⟨166552263902810470984953785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111034842601873647323302523 166552263902810470984953785)
          ·
            refine ⟨124914197927107853238715339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 166552263902810470984953785 124914197927107853238715339)
            ·
              refine ⟨187371296890661779858073009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 124914197927107853238715339 187371296890661779858073009)
              ·
                refine ⟨140528472667996334893554757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 187371296890661779858073009 140528472667996334893554757)
                ·
                  refine ⟨26349088625249312792541517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 140528472667996334893554757 26349088625249312792541517)
                  ·
                    refine ⟨9880908234468492297203069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26349088625249312792541517 9880908234468492297203069)
                    ·
                      refine ⟨3705340587925684611451151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9880908234468492297203069 3705340587925684611451151)
                      ·
                        rfl

theorem cell23_7216125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 2, 4, 3, 3].length) (baseStart_7216125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7216125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7216125 prefixEnd_7216125 := by exact prefixLift 7216125
  have htrace : WordTrace (prefixWord ++ tailWord_7216125) baseStart_7216125 baseEnd_7216125 := by
    simpa [prefixWord, tailWord_7216125, baseEnd_7216125] using wordTrace_append hprefix tailTrace_7216125
  have hstable : (prefixWord ++ tailWord_7216125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7216125).length < 2 ^ (prefixWord ++ tailWord_7216125).sum := by decide
  have hdescent : baseEnd_7216125 < baseStart_7216125 := by decide
  rcases family_descends (prefixWord ++ tailWord_7216125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7216126 : List Nat := [4, 2, 2, 2, 2, 1, 1, 2, 1, 4, 2]
def baseStart_7216126 : Nat := 118140960795 + 7216126 * 2 ^ 59
def prefixEnd_7216126 : Nat := 4983230072969 + 3 ^ 40 * 7216126 * 2
def baseEnd_7216126 : Nat := 3705341101406339107538647

theorem tailTrace_7216126 : CollatzResearch.WordTrace tailWord_7216126 prefixEnd_7216126 3705341101406339107538647 := by
  unfold tailWord_7216126
  simp only [CollatzResearch.WordTrace]
  refine ⟨32899217181901924131030529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 175462491636810262032162821 32899217181901924131030529)
  ·
    refine ⟨24674412886426443098272897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32899217181901924131030529 24674412886426443098272897)
    ·
      refine ⟨18505809664819832323704673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24674412886426443098272897 18505809664819832323704673)
      ·
        refine ⟨13879357248614874242778505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18505809664819832323704673 13879357248614874242778505)
        ·
          refine ⟨10409517936461155682083879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13879357248614874242778505 10409517936461155682083879)
          ·
            refine ⟨15614276904691733523125819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10409517936461155682083879 15614276904691733523125819)
            ·
              refine ⟨23421415357037600284688729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15614276904691733523125819 23421415357037600284688729)
              ·
                refine ⟨17566061517778200213516547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23421415357037600284688729 17566061517778200213516547)
                ·
                  refine ⟨26349092276667300320274821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17566061517778200213516547 26349092276667300320274821)
                  ·
                    refine ⟨4940454801875118810051529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26349092276667300320274821 4940454801875118810051529)
                    ·
                      refine ⟨3705341101406339107538647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4940454801875118810051529 3705341101406339107538647)
                      ·
                        rfl

theorem cell23_7216126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 1, 2, 1, 4, 2].length) (baseStart_7216126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7216126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7216126 prefixEnd_7216126 := by exact prefixLift 7216126
  have htrace : WordTrace (prefixWord ++ tailWord_7216126) baseStart_7216126 baseEnd_7216126 := by
    simpa [prefixWord, tailWord_7216126, baseEnd_7216126] using wordTrace_append hprefix tailTrace_7216126
  have hstable : (prefixWord ++ tailWord_7216126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7216126).length < 2 ^ (prefixWord ++ tailWord_7216126).sum := by decide
  have hdescent : baseEnd_7216126 < baseStart_7216126 := by decide
  rcases family_descends (prefixWord ++ tailWord_7216126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7216128 : List Nat := [2, 1, 1, 2, 1, 1, 1, 2, 5, 7]
def baseStart_7216128 : Nat := 118140960795 + 7216128 * 2 ^ 59
def prefixEnd_7216128 : Nat := 4983230072969 + 3 ^ 40 * 7216128 * 2
def baseEnd_7216128 : Nat := 1235114042789216033237879

theorem tailTrace_7216128 : CollatzResearch.WordTrace tailWord_7216128 prefixEnd_7216128 1235114042789216033237879 := by
  unfold tailWord_7216128
  simp only [CollatzResearch.WordTrace]
  refine ⟨131596905200604073694908519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175462540267472098259878025 131596905200604073694908519)
  ·
    refine ⟨197395357800906110542362779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131596905200604073694908519 197395357800906110542362779)
    ·
      refine ⟨296093036701359165813544169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197395357800906110542362779 296093036701359165813544169)
      ·
        refine ⟨222069777526019374360158127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 296093036701359165813544169 222069777526019374360158127)
        ·
          refine ⟨333104666289029061540237191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 222069777526019374360158127 333104666289029061540237191)
          ·
            refine ⟨499656999433543592310355787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 333104666289029061540237191 499656999433543592310355787)
            ·
              refine ⟨749485499150315388465533681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 499656999433543592310355787 749485499150315388465533681)
              ·
                refine ⟨562114124362736541349150261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 749485499150315388465533681 562114124362736541349150261)
                ·
                  refine ⟨52698199159006550751482837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 562114124362736541349150261 52698199159006550751482837)
                  ·
                    refine ⟨1235114042789216033237879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 52698199159006550751482837 1235114042789216033237879)
                    ·
                      rfl

theorem cell23_7216128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 2, 5, 7].length) (baseStart_7216128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7216128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7216128 prefixEnd_7216128 := by exact prefixLift 7216128
  have htrace : WordTrace (prefixWord ++ tailWord_7216128) baseStart_7216128 baseEnd_7216128 := by
    simpa [prefixWord, tailWord_7216128, baseEnd_7216128] using wordTrace_append hprefix tailTrace_7216128
  have hstable : (prefixWord ++ tailWord_7216128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7216128).length < 2 ^ (prefixWord ++ tailWord_7216128).sum := by decide
  have hdescent : baseEnd_7216128 < baseStart_7216128 := by decide
  rcases family_descends (prefixWord ++ tailWord_7216128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7216130 : List Nat := [3, 4, 1, 3, 1, 1, 3, 1, 1, 3, 2]
def baseStart_7216130 : Nat := 118140960795 + 7216130 * 2 ^ 59
def prefixEnd_7216130 : Nat := 4983230072969 + 3 ^ 40 * 7216130 * 2
def baseEnd_7216130 : Nat := 3705343155328957091888629

theorem tailTrace_7216130 : CollatzResearch.WordTrace tailWord_7216130 prefixEnd_7216130 3705343155328957091888629 := by
  unfold tailWord_7216130
  simp only [CollatzResearch.WordTrace]
  refine ⟨65798470836800225432847461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175462588898133934487593229 65798470836800225432847461)
  ·
    refine ⟨12337213281900042268658899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 65798470836800225432847461 12337213281900042268658899)
    ·
      refine ⟨18505819922850063402988349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12337213281900042268658899 18505819922850063402988349)
      ·
        refine ⟨6939682471068773776120631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18505819922850063402988349 6939682471068773776120631)
        ·
          refine ⟨10409523706603160664180947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6939682471068773776120631 10409523706603160664180947)
          ·
            refine ⟨15614285559904740996271421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10409523706603160664180947 15614285559904740996271421)
            ·
              refine ⟨5855357084964277873601783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15614285559904740996271421 5855357084964277873601783)
              ·
                refine ⟨8783035627446416810402675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5855357084964277873601783 8783035627446416810402675)
                ·
                  refine ⟨13174553441169625215604013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8783035627446416810402675 13174553441169625215604013)
                  ·
                    refine ⟨4940457540438609455851505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13174553441169625215604013 4940457540438609455851505)
                    ·
                      refine ⟨3705343155328957091888629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4940457540438609455851505 3705343155328957091888629)
                      ·
                        rfl

theorem cell23_7216130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 3, 1, 1, 3, 2].length) (baseStart_7216130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7216130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7216130 prefixEnd_7216130 := by exact prefixLift 7216130
  have htrace : WordTrace (prefixWord ++ tailWord_7216130) baseStart_7216130 baseEnd_7216130 := by
    simpa [prefixWord, tailWord_7216130, baseEnd_7216130] using wordTrace_append hprefix tailTrace_7216130
  have hstable : (prefixWord ++ tailWord_7216130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7216130).length < 2 ^ (prefixWord ++ tailWord_7216130).sum := by decide
  have hdescent : baseEnd_7216130 < baseStart_7216130 := by decide
  rcases family_descends (prefixWord ++ tailWord_7216130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7216149 : List Nat := [1, 3, 2, 1, 4, 1, 4, 2, 5]
def baseStart_7216149 : Nat := 118140960795 + 7216149 * 2 ^ 59
def prefixEnd_7216149 : Nat := 4983230072969 + 3 ^ 40 * 7216149 * 2
def baseEnd_7216149 : Nat := 411705879051265835283449

theorem tailTrace_7216149 : CollatzResearch.WordTrace tailWord_7216149 prefixEnd_7216149 411705879051265835283449 := by
  unfold tailWord_7216149
  simp only [CollatzResearch.WordTrace]
  refine ⟨263194576334132067976331501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175463050889421378650887667 263194576334132067976331501)
  ·
    refine ⟨98697966125299525491124313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 263194576334132067976331501 98697966125299525491124313)
    ·
      refine ⟨74023474593974644118343235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98697966125299525491124313 74023474593974644118343235)
      ·
        refine ⟨111035211890961966177514853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74023474593974644118343235 111035211890961966177514853)
        ·
          refine ⟨20819102229555368658284035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 111035211890961966177514853 20819102229555368658284035)
          ·
            refine ⟨31228653344333052987426053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20819102229555368658284035 31228653344333052987426053)
            ·
              refine ⟨5855372502062447435142385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31228653344333052987426053 5855372502062447435142385)
              ·
                refine ⟨4391529376546835576356789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5855372502062447435142385 4391529376546835576356789)
                ·
                  refine ⟨411705879051265835283449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4391529376546835576356789 411705879051265835283449)
                  ·
                    rfl

theorem cell23_7216149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 4, 2, 5].length) (baseStart_7216149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7216149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7216149 prefixEnd_7216149 := by exact prefixLift 7216149
  have htrace : WordTrace (prefixWord ++ tailWord_7216149) baseStart_7216149 baseEnd_7216149 := by
    simpa [prefixWord, tailWord_7216149, baseEnd_7216149] using wordTrace_append hprefix tailTrace_7216149
  have hstable : (prefixWord ++ tailWord_7216149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7216149).length < 2 ^ (prefixWord ++ tailWord_7216149).sum := by decide
  have hdescent : baseEnd_7216149 < baseStart_7216149 := by decide
  rcases family_descends (prefixWord ++ tailWord_7216149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7216152 : List Nat := [2, 1, 2, 3, 2, 2, 1, 1, 2, 5, 2]
def baseStart_7216152 : Nat := 118140960795 + 7216152 * 2 ^ 59
def prefixEnd_7216152 : Nat := 4983230072969 + 3 ^ 40 * 7216152 * 2
def baseEnd_7216152 : Nat := 3705354451903356005813527

theorem tailTrace_7216152 : CollatzResearch.WordTrace tailWord_7216152 prefixEnd_7216152 3705354451903356005813527 := by
  unfold tailWord_7216152
  simp only [CollatzResearch.WordTrace]
  refine ⟨131597342876560599744345355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175463123835414132992460473 131597342876560599744345355)
  ·
    refine ⟨197396014314840899616518033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131597342876560599744345355 197396014314840899616518033)
    ·
      refine ⟨148047010736130674712388525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 197396014314840899616518033 148047010736130674712388525)
      ·
        refine ⟨55517629026049003017145697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 148047010736130674712388525 55517629026049003017145697)
        ·
          refine ⟨41638221769536752262859273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55517629026049003017145697 41638221769536752262859273)
          ·
            refine ⟨31228666327152564197144455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41638221769536752262859273 31228666327152564197144455)
            ·
              refine ⟨46842999490728846295716683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31228666327152564197144455 46842999490728846295716683)
              ·
                refine ⟨70264499236093269443575025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46842999490728846295716683 70264499236093269443575025)
                ·
                  refine ⟨52698374427069952082681269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 70264499236093269443575025 52698374427069952082681269)
                  ·
                    refine ⟨4940472602537808007751369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 52698374427069952082681269 4940472602537808007751369)
                    ·
                      refine ⟨3705354451903356005813527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4940472602537808007751369 3705354451903356005813527)
                      ·
                        rfl

theorem cell23_7216152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 1, 1, 2, 5, 2].length) (baseStart_7216152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7216152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7216152 prefixEnd_7216152 := by exact prefixLift 7216152
  have htrace : WordTrace (prefixWord ++ tailWord_7216152) baseStart_7216152 baseEnd_7216152 := by
    simpa [prefixWord, tailWord_7216152, baseEnd_7216152] using wordTrace_append hprefix tailTrace_7216152
  have hstable : (prefixWord ++ tailWord_7216152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7216152).length < 2 ^ (prefixWord ++ tailWord_7216152).sum := by decide
  have hdescent : baseEnd_7216152 < baseStart_7216152 := by decide
  rcases family_descends (prefixWord ++ tailWord_7216152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7216165 : List Nat := [1, 3, 1, 2, 2, 2, 2, 2, 1, 3, 4]
def baseStart_7216165 : Nat := 118140960795 + 7216165 * 2 ^ 59
def prefixEnd_7216165 : Nat := 4983230072969 + 3 ^ 40 * 7216165 * 2
def baseEnd_7216165 : Nat := 3705361127151864454950967

theorem tailTrace_7216165 : CollatzResearch.WordTrace tailWord_7216165 prefixEnd_7216165 3705361127151864454950967 := by
  unfold tailWord_7216165
  simp only [CollatzResearch.WordTrace]
  refine ⟨263195159902074102708913949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175463439934716068472609299 263195159902074102708913949)
  ·
    refine ⟨98698184963277788515842731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 263195159902074102708913949 98698184963277788515842731)
    ·
      refine ⟨148047277444916682773764097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98698184963277788515842731 148047277444916682773764097)
      ·
        refine ⟨111035458083687512080323073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148047277444916682773764097 111035458083687512080323073)
        ·
          refine ⟨83276593562765634060242305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111035458083687512080323073 83276593562765634060242305)
          ·
            refine ⟨62457445172074225545181729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83276593562765634060242305 62457445172074225545181729)
            ·
              refine ⟨46843083879055669158886297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62457445172074225545181729 46843083879055669158886297)
              ·
                refine ⟨35132312909291751869164723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46843083879055669158886297 35132312909291751869164723)
                ·
                  refine ⟨52698469363937627803747085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35132312909291751869164723 52698469363937627803747085)
                  ·
                    refine ⟨19761926011476610426405157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 52698469363937627803747085 19761926011476610426405157)
                    ·
                      refine ⟨3705361127151864454950967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19761926011476610426405157 3705361127151864454950967)
                      ·
                        rfl

theorem cell23_7216165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 2, 2, 1, 3, 4].length) (baseStart_7216165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7216165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7216165 prefixEnd_7216165 := by exact prefixLift 7216165
  have htrace : WordTrace (prefixWord ++ tailWord_7216165) baseStart_7216165 baseEnd_7216165 := by
    simpa [prefixWord, tailWord_7216165, baseEnd_7216165] using wordTrace_append hprefix tailTrace_7216165
  have hstable : (prefixWord ++ tailWord_7216165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7216165).length < 2 ^ (prefixWord ++ tailWord_7216165).sum := by decide
  have hdescent : baseEnd_7216165 < baseStart_7216165 := by decide
  rcases family_descends (prefixWord ++ tailWord_7216165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7216202 : List Nat := [3, 1, 2, 1, 1, 2, 2, 4, 2, 2, 3]
def baseStart_7216202 : Nat := 118140960795 + 7216202 * 2 ^ 59
def prefixEnd_7216202 : Nat := 4983230072969 + 3 ^ 40 * 7216202 * 2
def baseEnd_7216202 : Nat := 3705380125936080810188297

theorem tailTrace_7216202 : CollatzResearch.WordTrace tailWord_7216202 prefixEnd_7216202 3705380125936080810188297 := by
  unfold tailWord_7216202
  simp only [CollatzResearch.WordTrace]
  refine ⟨65799127350735014507002715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175464339601960038685340573 65799127350735014507002715)
  ·
    refine ⟨98698691026102521760504073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65799127350735014507002715 98698691026102521760504073)
    ·
      refine ⟨74024018269576891320378055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98698691026102521760504073 74024018269576891320378055)
      ·
        refine ⟨111036027404365336980567083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74024018269576891320378055 111036027404365336980567083)
        ·
          refine ⟨166554041106548005470850625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111036027404365336980567083 166554041106548005470850625)
          ·
            refine ⟨124915530829911004103137969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 166554041106548005470850625 124915530829911004103137969)
            ·
              refine ⟨93686648122433253077353477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 124915530829911004103137969 93686648122433253077353477)
              ·
                refine ⟨17566246522956234952003777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 93686648122433253077353477 17566246522956234952003777)
                ·
                  refine ⟨13174684892217176214002833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17566246522956234952003777 13174684892217176214002833)
                  ·
                    refine ⟨9881013669162882160502125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13174684892217176214002833 9881013669162882160502125)
                    ·
                      refine ⟨3705380125936080810188297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9881013669162882160502125 3705380125936080810188297)
                      ·
                        rfl

theorem cell23_7216202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 4, 2, 2, 3].length) (baseStart_7216202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7216202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7216202 prefixEnd_7216202 := by exact prefixLift 7216202
  have htrace : WordTrace (prefixWord ++ tailWord_7216202) baseStart_7216202 baseEnd_7216202 := by
    simpa [prefixWord, tailWord_7216202, baseEnd_7216202] using wordTrace_append hprefix tailTrace_7216202
  have hstable : (prefixWord ++ tailWord_7216202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7216202).length < 2 ^ (prefixWord ++ tailWord_7216202).sum := by decide
  have hdescent : baseEnd_7216202 < baseStart_7216202 := by decide
  rcases family_descends (prefixWord ++ tailWord_7216202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7216209 : List Nat := [1, 2, 2, 1, 3, 1, 4, 4, 1, 4]
def baseStart_7216209 : Nat := 118140960795 + 7216209 * 2 ^ 59
def prefixEnd_7216209 : Nat := 4983230072969 + 3 ^ 40 * 7216209 * 2
def baseEnd_7216209 : Nat := 1235127906766887427600255

theorem tailTrace_7216209 : CollatzResearch.WordTrace tailWord_7216209 prefixEnd_7216209 1235127906766887427600255 := by
  unfold tailWord_7216209
  simp only [CollatzResearch.WordTrace]
  refine ⟨263196764713914698223515681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175464509809276465482343787 263196764713914698223515681)
  ·
    refine ⟨197397573535436023667636761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 263196764713914698223515681 197397573535436023667636761)
    ·
      refine ⟨148048180151577017750727571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 197397573535436023667636761 148048180151577017750727571)
      ·
        refine ⟨222072270227365526626091357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148048180151577017750727571 222072270227365526626091357)
        ·
          refine ⟨83277101335262072484784259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 222072270227365526626091357 83277101335262072484784259)
          ·
            refine ⟨124915652002893108727176389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83277101335262072484784259 124915652002893108727176389)
            ·
              refine ⟨23421684750542457886345573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 124915652002893108727176389 23421684750542457886345573)
              ·
                refine ⟨4391565890726710853689795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23421684750542457886345573 4391565890726710853689795)
                ·
                  refine ⟨6587348836090066280534693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4391565890726710853689795 6587348836090066280534693)
                  ·
                    refine ⟨1235127906766887427600255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6587348836090066280534693 1235127906766887427600255)
                    ·
                      rfl

theorem cell23_7216209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 4, 4, 1, 4].length) (baseStart_7216209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7216209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7216209 prefixEnd_7216209 := by exact prefixLift 7216209
  have htrace : WordTrace (prefixWord ++ tailWord_7216209) baseStart_7216209 baseEnd_7216209 := by
    simpa [prefixWord, tailWord_7216209, baseEnd_7216209] using wordTrace_append hprefix tailTrace_7216209
  have hstable : (prefixWord ++ tailWord_7216209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7216209).length < 2 ^ (prefixWord ++ tailWord_7216209).sum := by decide
  have hdescent : baseEnd_7216209 < baseStart_7216209 := by decide
  rcases family_descends (prefixWord ++ tailWord_7216209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7216252 : List Nat := [2, 2, 2, 1, 1, 3, 1, 5, 1, 5]
def baseStart_7216252 : Nat := 118140960795 + 7216252 * 2 ^ 59
def prefixEnd_7216252 : Nat := 4983230072969 + 3 ^ 40 * 7216252 * 2
def baseEnd_7216252 : Nat := 1235135266656268538187689

theorem tailTrace_7216252 : CollatzResearch.WordTrace tailWord_7216252 prefixEnd_7216252 1235135266656268538187689 := by
  unfold tailWord_7216252
  simp only [CollatzResearch.WordTrace]
  refine ⟨131599166526379458283665505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175465555368505944378220673 131599166526379458283665505)
  ·
    refine ⟨98699374894784593712749129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131599166526379458283665505 98699374894784593712749129)
    ·
      refine ⟨74024531171088445284561847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98699374894784593712749129 74024531171088445284561847)
      ·
        refine ⟨111036796756632667926842771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74024531171088445284561847 111036796756632667926842771)
        ·
          refine ⟨166555195134949001890264157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111036796756632667926842771 166555195134949001890264157)
          ·
            refine ⟨62458198175605875708849059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 166555195134949001890264157 62458198175605875708849059)
            ·
              refine ⟨93687297263408813563273589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62458198175605875708849059 93687297263408813563273589)
              ·
                refine ⟨8783184118444576271556899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 93687297263408813563273589 8783184118444576271556899)
                ·
                  refine ⟨13174776177666864407335349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8783184118444576271556899 13174776177666864407335349)
                  ·
                    refine ⟨1235135266656268538187689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13174776177666864407335349 1235135266656268538187689)
                    ·
                      rfl

theorem cell23_7216252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 5, 1, 5].length) (baseStart_7216252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7216252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7216252 prefixEnd_7216252 := by exact prefixLift 7216252
  have htrace : WordTrace (prefixWord ++ tailWord_7216252) baseStart_7216252 baseEnd_7216252 := by
    simpa [prefixWord, tailWord_7216252, baseEnd_7216252] using wordTrace_append hprefix tailTrace_7216252
  have hstable : (prefixWord ++ tailWord_7216252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7216252).length < 2 ^ (prefixWord ++ tailWord_7216252).sum := by decide
  have hdescent : baseEnd_7216252 < baseStart_7216252 := by decide
  rcases family_descends (prefixWord ++ tailWord_7216252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7216259 : List Nat := [1, 1, 1, 3, 3, 2, 3, 2, 2, 3, 2]
def baseStart_7216259 : Nat := 118140960795 + 7216259 * 2 ^ 59
def prefixEnd_7216259 : Nat := 4983230072969 + 3 ^ 40 * 7216259 * 2
def baseEnd_7216259 : Nat := 3705409394333387087175535

theorem tailTrace_7216259 : CollatzResearch.WordTrace tailWord_7216259 prefixEnd_7216259 3705409394333387087175535 := by
  unfold tailWord_7216259
  simp only [CollatzResearch.WordTrace]
  refine ⟨263198588363733556762835831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175465725575822371175223887 263198588363733556762835831)
  ·
    refine ⟨394797882545600335144253747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263198588363733556762835831 394797882545600335144253747)
    ·
      refine ⟨592196823818400502716380621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 394797882545600335144253747 592196823818400502716380621)
      ·
        refine ⟨222073808931900188518642733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 592196823818400502716380621 222073808931900188518642733)
        ·
          refine ⟨83277678349462570694491025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 222073808931900188518642733 83277678349462570694491025)
          ·
            refine ⟨62458258762096928020868269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83277678349462570694491025 62458258762096928020868269)
            ·
              refine ⟨23421847035786348007825601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62458258762096928020868269 23421847035786348007825601)
              ·
                refine ⟨17566385276839761005869201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23421847035786348007825601 17566385276839761005869201)
                ·
                  refine ⟨13174788957629820754401901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17566385276839761005869201 13174788957629820754401901)
                  ·
                    refine ⟨4940545859111182782900713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13174788957629820754401901 4940545859111182782900713)
                    ·
                      refine ⟨3705409394333387087175535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4940545859111182782900713 3705409394333387087175535)
                      ·
                        rfl

theorem cell23_7216259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 3, 2, 2, 3, 2].length) (baseStart_7216259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7216259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7216259 prefixEnd_7216259 := by exact prefixLift 7216259
  have htrace : WordTrace (prefixWord ++ tailWord_7216259) baseStart_7216259 baseEnd_7216259 := by
    simpa [prefixWord, tailWord_7216259, baseEnd_7216259] using wordTrace_append hprefix tailTrace_7216259
  have hstable : (prefixWord ++ tailWord_7216259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7216259).length < 2 ^ (prefixWord ++ tailWord_7216259).sum := by decide
  have hdescent : baseEnd_7216259 < baseStart_7216259 := by decide
  rcases family_descends (prefixWord ++ tailWord_7216259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7216272 : List Nat := [2, 1, 1, 1, 1, 1, 4, 2, 2, 6, 2]
def baseStart_7216272 : Nat := 118140960795 + 7216272 * 2 ^ 59
def prefixEnd_7216272 : Nat := 4983230072969 + 3 ^ 40 * 7216272 * 2
def baseEnd_7216272 : Nat := 3705416069581895536312975

theorem tailTrace_7216272 : CollatzResearch.WordTrace tailWord_7216272 prefixEnd_7216272 3705416069581895536312975 := by
  unfold tailWord_7216272
  simp only [CollatzResearch.WordTrace]
  refine ⟨131599531256343229991529535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175466041675124306655372713 131599531256343229991529535)
  ·
    refine ⟨197399296884514844987294303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131599531256343229991529535 197399296884514844987294303)
    ·
      refine ⟨296098945326772267480941455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197399296884514844987294303 296098945326772267480941455)
      ·
        refine ⟨444148417990158401221412183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 296098945326772267480941455 444148417990158401221412183)
        ·
          refine ⟨666222626985237601832118275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 444148417990158401221412183 666222626985237601832118275)
          ·
            refine ⟨999333940477856402748177413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 666222626985237601832118275 999333940477856402748177413)
            ·
              refine ⟨187375113839598075515283265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 999333940477856402748177413 187375113839598075515283265)
              ·
                refine ⟨140531335379698556636462449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 187375113839598075515283265 140531335379698556636462449)
                ·
                  refine ⟨105398501534773917477346837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 140531335379698556636462449 105398501534773917477346837)
                  ·
                    refine ⟨4940554759442527381750633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 105398501534773917477346837 4940554759442527381750633)
                    ·
                      refine ⟨3705416069581895536312975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4940554759442527381750633 3705416069581895536312975)
                      ·
                        rfl

theorem cell23_7216272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 2, 2, 6, 2].length) (baseStart_7216272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7216272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7216272 prefixEnd_7216272 := by exact prefixLift 7216272
  have htrace : WordTrace (prefixWord ++ tailWord_7216272) baseStart_7216272 baseEnd_7216272 := by
    simpa [prefixWord, tailWord_7216272, baseEnd_7216272] using wordTrace_append hprefix tailTrace_7216272
  have hstable : (prefixWord ++ tailWord_7216272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7216272).length < 2 ^ (prefixWord ++ tailWord_7216272).sum := by decide
  have hdescent : baseEnd_7216272 < baseStart_7216272 := by decide
  rcases family_descends (prefixWord ++ tailWord_7216272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7216286 : List Nat := [4, 3, 1, 1, 2, 1, 3, 2, 1, 5]
def baseStart_7216286 : Nat := 118140960795 + 7216286 * 2 ^ 59
def prefixEnd_7216286 : Nat := 4983230072969 + 3 ^ 40 * 7216286 * 2
def baseEnd_7216286 : Nat := 1235141086103686160512637

theorem tailTrace_7216286 : CollatzResearch.WordTrace tailWord_7216286 prefixEnd_7216286 1235141086103686160512637 := by
  unfold tailWord_7216286
  simp only [CollatzResearch.WordTrace]
  refine ⟨32899946641829467546758589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 175466382089757160249379141 32899946641829467546758589)
  ·
    refine ⟨12337479990686050330034471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32899946641829467546758589 12337479990686050330034471)
    ·
      refine ⟨18506219986029075495051707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12337479990686050330034471 18506219986029075495051707)
      ·
        refine ⟨27759329979043613242577561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18506219986029075495051707 27759329979043613242577561)
        ·
          refine ⟨20819497484282709931933171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27759329979043613242577561 20819497484282709931933171)
          ·
            refine ⟨31229246226424064897899757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20819497484282709931933171 31229246226424064897899757)
            ·
              refine ⟨11710967334909024336712409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31229246226424064897899757 11710967334909024336712409)
              ·
                refine ⟨8783225501181768252534307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11710967334909024336712409 8783225501181768252534307)
                ·
                  refine ⟨13174838251772652378801461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8783225501181768252534307 13174838251772652378801461)
                  ·
                    refine ⟨1235141086103686160512637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13174838251772652378801461 1235141086103686160512637)
                    ·
                      rfl

theorem cell23_7216286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 3, 2, 1, 5].length) (baseStart_7216286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7216286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7216286 prefixEnd_7216286 := by exact prefixLift 7216286
  have htrace : WordTrace (prefixWord ++ tailWord_7216286) baseStart_7216286 baseEnd_7216286 := by
    simpa [prefixWord, tailWord_7216286, baseEnd_7216286] using wordTrace_append hprefix tailTrace_7216286
  have hstable : (prefixWord ++ tailWord_7216286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7216286).length < 2 ^ (prefixWord ++ tailWord_7216286).sum := by decide
  have hdescent : baseEnd_7216286 < baseStart_7216286 := by decide
  rcases family_descends (prefixWord ++ tailWord_7216286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7216306 : List Nat := [3, 2, 1, 1, 1, 5, 3, 1, 1, 1, 4]
def baseStart_7216306 : Nat := 118140960795 + 7216306 * 2 ^ 59
def prefixEnd_7216306 : Nat := 4983230072969 + 3 ^ 40 * 7216306 * 2
def baseEnd_7216306 : Nat := 3705433527924148403287819

theorem tailTrace_7216306 : CollatzResearch.WordTrace tailWord_7216306 prefixEnd_7216306 3705433527924148403287819 := by
  unfold tailWord_7216306
  simp only [CollatzResearch.WordTrace]
  refine ⟨65800075648640820947449193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175466868396375522526531181 65800075648640820947449193)
  ·
    refine ⟨49350056736480615710586895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65800075648640820947449193 49350056736480615710586895)
    ·
      refine ⟨74025085104720923565880343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49350056736480615710586895 74025085104720923565880343)
      ·
        refine ⟨111037627657081385348820515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74025085104720923565880343 111037627657081385348820515)
        ·
          refine ⟨166556441485622078023230773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111037627657081385348820515 166556441485622078023230773)
          ·
            refine ⟨15614666389277069814677885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 166556441485622078023230773 15614666389277069814677885)
            ·
              refine ⟨5855499895978901180504207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15614666389277069814677885 5855499895978901180504207)
              ·
                refine ⟨8783249843968351770756311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5855499895978901180504207 8783249843968351770756311)
                ·
                  refine ⟨13174874765952527656134467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8783249843968351770756311 13174874765952527656134467)
                  ·
                    refine ⟨19762312148928791484201701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13174874765952527656134467 19762312148928791484201701)
                    ·
                      refine ⟨3705433527924148403287819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19762312148928791484201701 3705433527924148403287819)
                      ·
                        rfl

theorem cell23_7216306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 3, 1, 1, 1, 4].length) (baseStart_7216306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7216306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7216306 prefixEnd_7216306 := by exact prefixLift 7216306
  have htrace : WordTrace (prefixWord ++ tailWord_7216306) baseStart_7216306 baseEnd_7216306 := by
    simpa [prefixWord, tailWord_7216306, baseEnd_7216306] using wordTrace_append hprefix tailTrace_7216306
  have hstable : (prefixWord ++ tailWord_7216306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7216306).length < 2 ^ (prefixWord ++ tailWord_7216306).sum := by decide
  have hdescent : baseEnd_7216306 < baseStart_7216306 := by decide
  rcases family_descends (prefixWord ++ tailWord_7216306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7216315 : List Nat := [1, 1, 1, 1, 1, 2, 4, 2, 2, 2, 6]
def baseStart_7216315 : Nat := 118140960795 + 7216315 * 2 ^ 59
def prefixEnd_7216315 : Nat := 4983230072969 + 3 ^ 40 * 7216315 * 2
def baseEnd_7216315 : Nat := 3705438149250038868075277

theorem tailTrace_7216315 : CollatzResearch.WordTrace tailWord_7216315 prefixEnd_7216315 3705438149250038868075277 := by
  unfold tailWord_7216315
  simp only [CollatzResearch.WordTrace]
  refine ⟨263200630851530678326874399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175467087234353785551249599 263200630851530678326874399)
  ·
    refine ⟨394800946277296017490311599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263200630851530678326874399 394800946277296017490311599)
    ·
      refine ⟨592201419415944026235467399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 394800946277296017490311599 592201419415944026235467399)
      ·
        refine ⟨888302129123916039353201099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 592201419415944026235467399 888302129123916039353201099)
        ·
          refine ⟨1332453193685874059029801649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 888302129123916039353201099 1332453193685874059029801649)
          ·
            refine ⟨999339895264405544272351237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1332453193685874059029801649 999339895264405544272351237)
            ·
              refine ⟨187376230362076039551065857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 999339895264405544272351237 187376230362076039551065857)
              ·
                refine ⟨140532172771557029663299393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 187376230362076039551065857 140532172771557029663299393)
                ·
                  refine ⟨105399129578667772247474545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 140532172771557029663299393 105399129578667772247474545)
                  ·
                    refine ⟨79049347184000829185605909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 105399129578667772247474545 79049347184000829185605909)
                    ·
                      refine ⟨3705438149250038868075277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 79049347184000829185605909 3705438149250038868075277)
                      ·
                        rfl

theorem cell23_7216315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 2, 2, 2, 6].length) (baseStart_7216315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7216315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7216315 prefixEnd_7216315 := by exact prefixLift 7216315
  have htrace : WordTrace (prefixWord ++ tailWord_7216315) baseStart_7216315 baseEnd_7216315 := by
    simpa [prefixWord, tailWord_7216315, baseEnd_7216315] using wordTrace_append hprefix tailTrace_7216315
  have hstable : (prefixWord ++ tailWord_7216315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7216315).length < 2 ^ (prefixWord ++ tailWord_7216315).sum := by decide
  have hdescent : baseEnd_7216315 < baseStart_7216315 := by decide
  rcases family_descends (prefixWord ++ tailWord_7216315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7216316 : List Nat := [2, 2, 2, 3, 2, 2, 2, 2, 2, 4]
def baseStart_7216316 : Nat := 118140960795 + 7216316 * 2 ^ 59
def prefixEnd_7216316 : Nat := 4983230072969 + 3 ^ 40 * 7216316 * 2
def baseEnd_7216316 : Nat := 1235146220910231121387591

theorem tailTrace_7216316 : CollatzResearch.WordTrace tailWord_7216316 prefixEnd_7216316 1235146220910231121387591 := by
  unfold tailWord_7216316
  simp only [CollatzResearch.WordTrace]
  refine ⟨131600333662263527748830401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175467111549684703665107201 131600333662263527748830401)
  ·
    refine ⟨98700250246697645811622801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131600333662263527748830401 98700250246697645811622801)
    ·
      refine ⟨74025187685023234358717101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98700250246697645811622801 74025187685023234358717101)
      ·
        refine ⟨27759445381883712884518913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74025187685023234358717101 27759445381883712884518913)
        ·
          refine ⟨20819584036412784663389185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27759445381883712884518913 20819584036412784663389185)
          ·
            refine ⟨15614688027309588497541889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20819584036412784663389185 15614688027309588497541889)
            ·
              refine ⟨11711016020482191373156417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15614688027309588497541889 11711016020482191373156417)
              ·
                refine ⟨8783262015361643529867313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11711016020482191373156417 8783262015361643529867313)
                ·
                  refine ⟨6587446511521232647400485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8783262015361643529867313 6587446511521232647400485)
                  ·
                    refine ⟨1235146220910231121387591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6587446511521232647400485 1235146220910231121387591)
                    ·
                      rfl

theorem cell23_7216316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 2, 2, 2, 4].length) (baseStart_7216316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7216316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7216316 prefixEnd_7216316 := by exact prefixLift 7216316
  have htrace : WordTrace (prefixWord ++ tailWord_7216316) baseStart_7216316 baseEnd_7216316 := by
    simpa [prefixWord, tailWord_7216316, baseEnd_7216316] using wordTrace_append hprefix tailTrace_7216316
  have hstable : (prefixWord ++ tailWord_7216316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7216316).length < 2 ^ (prefixWord ++ tailWord_7216316).sum := by decide
  have hdescent : baseEnd_7216316 < baseStart_7216316 := by decide
  rcases family_descends (prefixWord ++ tailWord_7216316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7216333 : List Nat := [1, 6, 2, 2, 1, 1, 2, 1, 1, 6]
def baseStart_7216333 : Nat := 118140960795 + 7216333 * 2 ^ 59
def prefixEnd_7216333 : Nat := 4983230072969 + 3 ^ 40 * 7216333 * 2
def baseEnd_7216333 : Nat := 1235149130633939932550065

theorem tailTrace_7216333 : CollatzResearch.WordTrace tailWord_7216333 prefixEnd_7216333 1235149130633939932550065 := by
  unfold tailWord_7216333
  simp only [CollatzResearch.WordTrace]
  refine ⟨263201287365465467401029653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175467524910310311600686435 263201287365465467401029653)
  ·
    refine ⟨12337560345256193784423265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 263201287365465467401029653 12337560345256193784423265)
    ·
      refine ⟨9253170258942145338317449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12337560345256193784423265 9253170258942145338317449)
      ·
        refine ⟨6939877694206609003738087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9253170258942145338317449 6939877694206609003738087)
        ·
          refine ⟨10409816541309913505607131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6939877694206609003738087 10409816541309913505607131)
          ·
            refine ⟨15614724811964870258410697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10409816541309913505607131 15614724811964870258410697)
            ·
              refine ⟨11711043608973652693808023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15614724811964870258410697 11711043608973652693808023)
              ·
                refine ⟨17566565413460479040712035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11711043608973652693808023 17566565413460479040712035)
                ·
                  refine ⟨26349848120190718561068053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17566565413460479040712035 26349848120190718561068053)
                  ·
                    refine ⟨1235149130633939932550065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26349848120190718561068053 1235149130633939932550065)
                    ·
                      rfl

theorem cell23_7216333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 2, 1, 1, 6].length) (baseStart_7216333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7216333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7216333 prefixEnd_7216333 := by exact prefixLift 7216333
  have htrace : WordTrace (prefixWord ++ tailWord_7216333) baseStart_7216333 baseEnd_7216333 := by
    simpa [prefixWord, tailWord_7216333, baseEnd_7216333] using wordTrace_append hprefix tailTrace_7216333
  have hstable : (prefixWord ++ tailWord_7216333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7216333).length < 2 ^ (prefixWord ++ tailWord_7216333).sum := by decide
  have hdescent : baseEnd_7216333 < baseStart_7216333 := by decide
  rcases family_descends (prefixWord ++ tailWord_7216333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7216340 : List Nat := [2, 4, 1, 4, 1, 1, 1, 2, 3, 2, 2]
def baseStart_7216340 : Nat := 118140960795 + 7216340 * 2 ^ 59
def prefixEnd_7216340 : Nat := 4983230072969 + 3 ^ 40 * 7216340 * 2
def baseEnd_7216340 : Nat := 3705450986266401270262663

theorem tailTrace_7216340 : CollatzResearch.WordTrace tailWord_7216340 prefixEnd_7216340 3705450986266401270262663 := by
  unfold tailWord_7216340
  simp only [CollatzResearch.WordTrace]
  refine ⟨131600771338220053798267237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175467695117626738397689649 131600771338220053798267237)
  ·
    refine ⟨24675144625916260087175107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 131600771338220053798267237 24675144625916260087175107)
    ·
      refine ⟨37012716938874390130762661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24675144625916260087175107 37012716938874390130762661)
      ·
        refine ⟨6939884426038948149517999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37012716938874390130762661 6939884426038948149517999)
        ·
          refine ⟨10409826639058422224276999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6939884426038948149517999 10409826639058422224276999)
          ·
            refine ⟨15614739958587633336415499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10409826639058422224276999 15614739958587633336415499)
            ·
              refine ⟨23422109937881450004623249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15614739958587633336415499 23422109937881450004623249)
              ·
                refine ⟨17566582453411087503467437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23422109937881450004623249 17566582453411087503467437)
                ·
                  refine ⟨6587468420029157813800289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17566582453411087503467437 6587468420029157813800289)
                  ·
                    refine ⟨4940601315021868360350217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6587468420029157813800289 4940601315021868360350217)
                    ·
                      refine ⟨3705450986266401270262663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4940601315021868360350217 3705450986266401270262663)
                      ·
                        rfl

theorem cell23_7216340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 1, 2, 3, 2, 2].length) (baseStart_7216340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7216340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7216340 prefixEnd_7216340 := by exact prefixLift 7216340
  have htrace : WordTrace (prefixWord ++ tailWord_7216340) baseStart_7216340 baseEnd_7216340 := by
    simpa [prefixWord, tailWord_7216340, baseEnd_7216340] using wordTrace_append hprefix tailTrace_7216340
  have hstable : (prefixWord ++ tailWord_7216340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7216340).length < 2 ^ (prefixWord ++ tailWord_7216340).sum := by decide
  have hdescent : baseEnd_7216340 < baseStart_7216340 := by decide
  rcases family_descends (prefixWord ++ tailWord_7216340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7216396 : List Nat := [2, 2, 1, 2, 2, 3, 3, 1, 1, 4, 2]
def baseStart_7216396 : Nat := 118140960795 + 7216396 * 2 ^ 59
def prefixEnd_7216396 : Nat := 4983230072969 + 3 ^ 40 * 7216396 * 2
def baseEnd_7216396 : Nat := 3705479741183053051162405

theorem tailTrace_7216396 : CollatzResearch.WordTrace tailWord_7216396 prefixEnd_7216396 3705479741183053051162405 := by
  unfold tailWord_7216396
  simp only [CollatzResearch.WordTrace]
  refine ⟨131601792582118614580286521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175469056776158152773715361 131601792582118614580286521)
  ·
    refine ⟨98701344436588960935214891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131601792582118614580286521 98701344436588960935214891)
    ·
      refine ⟨148052016654883441402822337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98701344436588960935214891 148052016654883441402822337)
      ·
        refine ⟨111039012491162581052116753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148052016654883441402822337 111039012491162581052116753)
        ·
          refine ⟨83279259368371935789087565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111039012491162581052116753 83279259368371935789087565)
          ·
            refine ⟨31229722263139475920907837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 83279259368371935789087565 31229722263139475920907837)
            ·
              refine ⟨11711145848677303470340439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31229722263139475920907837 11711145848677303470340439)
              ·
                refine ⟨17566718773015955205510659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11711145848677303470340439 17566718773015955205510659)
                ·
                  refine ⟨26350078159523932808265989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17566718773015955205510659 26350078159523932808265989)
                  ·
                    refine ⟨4940639654910737401549873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26350078159523932808265989 4940639654910737401549873)
                    ·
                      refine ⟨3705479741183053051162405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4940639654910737401549873 3705479741183053051162405)
                      ·
                        rfl

theorem cell23_7216396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 3, 1, 1, 4, 2].length) (baseStart_7216396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7216396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7216396 prefixEnd_7216396 := by exact prefixLift 7216396
  have htrace : WordTrace (prefixWord ++ tailWord_7216396) baseStart_7216396 baseEnd_7216396 := by
    simpa [prefixWord, tailWord_7216396, baseEnd_7216396] using wordTrace_append hprefix tailTrace_7216396
  have hstable : (prefixWord ++ tailWord_7216396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7216396).length < 2 ^ (prefixWord ++ tailWord_7216396).sum := by decide
  have hdescent : baseEnd_7216396 < baseStart_7216396 := by decide
  rcases family_descends (prefixWord ++ tailWord_7216396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7216413 : List Nat := [1, 4, 2, 3, 1, 1, 1, 2, 4, 2, 2]
def baseStart_7216413 : Nat := 118140960795 + 7216413 * 2 ^ 59
def prefixEnd_7216413 : Nat := 4983230072969 + 3 ^ 40 * 7216413 * 2
def baseEnd_7216413 : Nat := 3705488470354179484649827

theorem tailTrace_7216413 : CollatzResearch.WordTrace tailWord_7216413 prefixEnd_7216413 3705488470354179484649827 := by
  unfold tailWord_7216413
  simp only [CollatzResearch.WordTrace]
  refine ⟨263204205205175641063941893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175469470136783760709294595 263204205205175641063941893)
  ·
    refine ⟨49350788475970432699489105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 263204205205175641063941893 49350788475970432699489105)
    ·
      refine ⟨37013091356977824524616829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49350788475970432699489105 37013091356977824524616829)
      ·
        refine ⟨13879909258866684196731311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37013091356977824524616829 13879909258866684196731311)
        ·
          refine ⟨20819863888300026295096967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13879909258866684196731311 20819863888300026295096967)
          ·
            refine ⟨31229795832450039442645451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20819863888300026295096967 31229795832450039442645451)
            ·
              refine ⟨46844693748675059163968177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31229795832450039442645451 46844693748675059163968177)
              ·
                refine ⟨35133520311506294372976133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46844693748675059163968177 35133520311506294372976133)
                ·
                  refine ⟨6587535058407430194933025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35133520311506294372976133 6587535058407430194933025)
                  ·
                    refine ⟨4940651293805572646199769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6587535058407430194933025 4940651293805572646199769)
                    ·
                      refine ⟨3705488470354179484649827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4940651293805572646199769 3705488470354179484649827)
                      ·
                        rfl

theorem cell23_7216413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 1, 2, 4, 2, 2].length) (baseStart_7216413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7216413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7216413 prefixEnd_7216413 := by exact prefixLift 7216413
  have htrace : WordTrace (prefixWord ++ tailWord_7216413) baseStart_7216413 baseEnd_7216413 := by
    simpa [prefixWord, tailWord_7216413, baseEnd_7216413] using wordTrace_append hprefix tailTrace_7216413
  have hstable : (prefixWord ++ tailWord_7216413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7216413).length < 2 ^ (prefixWord ++ tailWord_7216413).sum := by decide
  have hdescent : baseEnd_7216413 < baseStart_7216413 := by decide
  rcases family_descends (prefixWord ++ tailWord_7216413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7216489 : List Nat := [1, 2, 1, 1, 1, 3, 2, 3, 4, 2, 3]
def baseStart_7216489 : Nat := 118140960795 + 7216489 * 2 ^ 59
def prefixEnd_7216489 : Nat := 4983230072969 + 3 ^ 40 * 7216489 * 2
def baseEnd_7216489 : Nat := 3705527494883921187299477

theorem tailTrace_7216489 : CollatzResearch.WordTrace tailWord_7216489 prefixEnd_7216489 3705527494883921187299477 := by
  unfold tailWord_7216489
  simp only [CollatzResearch.WordTrace]
  refine ⟨263206977152900306043708521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175471318101933537362472347 263206977152900306043708521)
  ·
    refine ⟨197405232864675229532781391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 263206977152900306043708521 197405232864675229532781391)
    ·
      refine ⟨296107849297012844299172087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197405232864675229532781391 296107849297012844299172087)
      ·
        refine ⟨444161773945519266448758131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 296107849297012844299172087 444161773945519266448758131)
        ·
          refine ⟨666242660918278899673137197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 444161773945519266448758131 666242660918278899673137197)
          ·
            refine ⟨249840997844354587377426449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 666242660918278899673137197 249840997844354587377426449)
            ·
              refine ⟨187380748383265940533069837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 249840997844354587377426449 187380748383265940533069837)
              ·
                refine ⟨70267780643724727699901189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 187380748383265940533069837 70267780643724727699901189)
                ·
                  refine ⟨13175208870698386443731473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 70267780643724727699901189 13175208870698386443731473)
                  ·
                    refine ⟨9881406653023789832798605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13175208870698386443731473 9881406653023789832798605)
                    ·
                      refine ⟨3705527494883921187299477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9881406653023789832798605 3705527494883921187299477)
                      ·
                        rfl

theorem cell23_7216489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 3, 4, 2, 3].length) (baseStart_7216489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7216489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7216489 prefixEnd_7216489 := by exact prefixLift 7216489
  have htrace : WordTrace (prefixWord ++ tailWord_7216489) baseStart_7216489 baseEnd_7216489 := by
    simpa [prefixWord, tailWord_7216489, baseEnd_7216489] using wordTrace_append hprefix tailTrace_7216489
  have hstable : (prefixWord ++ tailWord_7216489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7216489).length < 2 ^ (prefixWord ++ tailWord_7216489).sum := by decide
  have hdescent : baseEnd_7216489 < baseStart_7216489 := by decide
  rcases family_descends (prefixWord ++ tailWord_7216489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7216509 : List Nat := [1, 4, 1, 1, 2, 2, 1, 5, 6]
def baseStart_7216509 : Nat := 118140960795 + 7216509 * 2 ^ 59
def prefixEnd_7216509 : Nat := 4983230072969 + 3 ^ 40 * 7216509 * 2
def baseEnd_7216509 : Nat := 411726418277445678783265

theorem tailTrace_7216509 : CollatzResearch.WordTrace tailWord_7216509 prefixEnd_7216509 411726418277445678783265 := by
  unfold tailWord_7216509
  simp only [CollatzResearch.WordTrace]
  refine ⟨263207706612827849459436581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175471804408551899639624387 263207706612827849459436581)
  ·
    refine ⟨49351444989905221773644359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 263207706612827849459436581 49351444989905221773644359)
    ·
      refine ⟨74027167484857832660466539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49351444989905221773644359 74027167484857832660466539)
      ·
        refine ⟨111040751227286748990699809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74027167484857832660466539 111040751227286748990699809)
        ·
          refine ⟨83280563420465061743024857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111040751227286748990699809 83280563420465061743024857)
          ·
            refine ⟨62460422565348796307268643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83280563420465061743024857 62460422565348796307268643)
            ·
              refine ⟨93690633848023194460902965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62460422565348796307268643 93690633848023194460902965)
              ·
                refine ⟨8783496923252174480709653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 93690633848023194460902965 8783496923252174480709653)
                ·
                  refine ⟨411726418277445678783265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8783496923252174480709653 411726418277445678783265)
                  ·
                    rfl

theorem cell23_7216509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 5, 6].length) (baseStart_7216509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7216509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7216509 prefixEnd_7216509 := by exact prefixLift 7216509
  have htrace : WordTrace (prefixWord ++ tailWord_7216509) baseStart_7216509 baseEnd_7216509 := by
    simpa [prefixWord, tailWord_7216509, baseEnd_7216509] using wordTrace_append hprefix tailTrace_7216509
  have hstable : (prefixWord ++ tailWord_7216509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7216509).length < 2 ^ (prefixWord ++ tailWord_7216509).sum := by decide
  have hdescent : baseEnd_7216509 < baseStart_7216509 := by decide
  rcases family_descends (prefixWord ++ tailWord_7216509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7216513 : List Nat := [1, 2, 4, 3, 2, 1, 1, 2, 3, 4]
def baseStart_7216513 : Nat := 118140960795 + 7216513 * 2 ^ 59
def prefixEnd_7216513 : Nat := 4983230072969 + 3 ^ 40 * 7216513 * 2
def baseEnd_7216513 : Nat := 1235179939473209697799789

theorem tailTrace_7216513 : CollatzResearch.WordTrace tailWord_7216513 prefixEnd_7216513 1235179939473209697799789 := by
  unfold tailWord_7216513
  simp only [CollatzResearch.WordTrace]
  refine ⟨263207852504813358142582193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175471901669875572095054795 263207852504813358142582193)
  ·
    refine ⟨197405889378610018606936645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 263207852504813358142582193 197405889378610018606936645)
    ·
      refine ⟨37013604258489378488800621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 197405889378610018606936645 37013604258489378488800621)
      ·
        refine ⟨13880101596933516933300233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37013604258489378488800621 13880101596933516933300233)
        ·
          refine ⟨10410076197700137699975175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13880101596933516933300233 10410076197700137699975175)
          ·
            refine ⟨15615114296550206549962763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10410076197700137699975175 15615114296550206549962763)
            ·
              refine ⟨23422671444825309824944145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15615114296550206549962763 23422671444825309824944145)
              ·
                refine ⟨17567003583618982368708109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23422671444825309824944145 17567003583618982368708109)
                ·
                  refine ⟨6587626343857118388265541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17567003583618982368708109 6587626343857118388265541)
                  ·
                    refine ⟨1235179939473209697799789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6587626343857118388265541 1235179939473209697799789)
                    ·
                      rfl

theorem cell23_7216513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 1, 2, 3, 4].length) (baseStart_7216513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7216513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7216513 prefixEnd_7216513 := by exact prefixLift 7216513
  have htrace : WordTrace (prefixWord ++ tailWord_7216513) baseStart_7216513 baseEnd_7216513 := by
    simpa [prefixWord, tailWord_7216513, baseEnd_7216513] using wordTrace_append hprefix tailTrace_7216513
  have hstable : (prefixWord ++ tailWord_7216513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7216513).length < 2 ^ (prefixWord ++ tailWord_7216513).sum := by decide
  have hdescent : baseEnd_7216513 < baseStart_7216513 := by decide
  rcases family_descends (prefixWord ++ tailWord_7216513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7216559 : List Nat := [1, 1, 2, 1, 2, 2, 1, 3, 5, 1, 4]
def baseStart_7216559 : Nat := 118140960795 + 7216559 * 2 ^ 59
def prefixEnd_7216559 : Nat := 4983230072969 + 3 ^ 40 * 7216559 * 2
def baseEnd_7216559 : Nat := 3705563438529735913424155

theorem tailTrace_7216559 : CollatzResearch.WordTrace tailWord_7216559 prefixEnd_7216559 3705563438529735913424155 := by
  unfold tailWord_7216559
  simp only [CollatzResearch.WordTrace]
  refine ⟨263209530262646707998756731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175473020175097805332504487 263209530262646707998756731)
  ·
    refine ⟨394814295393970061998135097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263209530262646707998756731 394814295393970061998135097)
    ·
      refine ⟨296110721545477546498601323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 394814295393970061998135097 296110721545477546498601323)
      ·
        refine ⟨444166082318216319747901985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 296110721545477546498601323 444166082318216319747901985)
        ·
          refine ⟨333124561738662239810926489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 444166082318216319747901985 333124561738662239810926489)
          ·
            refine ⟨249843421303996679858194867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 333124561738662239810926489 249843421303996679858194867)
            ·
              refine ⟨374765131955995019787292301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 249843421303996679858194867 374765131955995019787292301)
              ·
                refine ⟨140536924483498132420234613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 374765131955995019787292301 140536924483498132420234613)
                ·
                  refine ⟨13175336670327949914396995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 140536924483498132420234613 13175336670327949914396995)
                  ·
                    refine ⟨19763005005491924871595493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13175336670327949914396995 19763005005491924871595493)
                    ·
                      refine ⟨3705563438529735913424155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19763005005491924871595493 3705563438529735913424155)
                      ·
                        rfl

theorem cell23_7216559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 3, 5, 1, 4].length) (baseStart_7216559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7216559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7216559 prefixEnd_7216559 := by exact prefixLift 7216559
  have htrace : WordTrace (prefixWord ++ tailWord_7216559) baseStart_7216559 baseEnd_7216559 := by
    simpa [prefixWord, tailWord_7216559, baseEnd_7216559] using wordTrace_append hprefix tailTrace_7216559
  have hstable : (prefixWord ++ tailWord_7216559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7216559).length < 2 ^ (prefixWord ++ tailWord_7216559).sum := by decide
  have hdescent : baseEnd_7216559 < baseStart_7216559 := by decide
  rcases family_descends (prefixWord ++ tailWord_7216559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7216576 : List Nat := [2, 1, 1, 2, 3, 1, 3, 4, 1, 1, 4]
def baseStart_7216576 : Nat := 118140960795 + 7216576 * 2 ^ 59
def prefixEnd_7216576 : Nat := 4983230072969 + 3 ^ 40 * 7216576 * 2
def baseEnd_7216576 : Nat := 3705572167700862346911577

theorem tailTrace_7216576 : CollatzResearch.WordTrace tailWord_7216576 prefixEnd_7216576 3705572167700862346911577 := by
  unfold tailWord_7216576
  simp only [CollatzResearch.WordTrace]
  refine ⟨131605075151792559951062791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175473433535723413268083721 131605075151792559951062791)
  ·
    refine ⟨197407612727688839926594187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131605075151792559951062791 197407612727688839926594187)
    ·
      refine ⟨296111419091533259889891281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197407612727688839926594187 296111419091533259889891281)
      ·
        refine ⟨222083564318649944917418461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 296111419091533259889891281 222083564318649944917418461)
        ·
          refine ⟨83281336619493729344031923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 222083564318649944917418461 83281336619493729344031923)
          ·
            refine ⟨124922004929240594016047885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83281336619493729344031923 124922004929240594016047885)
            ·
              refine ⟨46845751848465222756017957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 124922004929240594016047885 46845751848465222756017957)
              ·
                refine ⟨8783578471587229266753367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46845751848465222756017957 8783578471587229266753367)
                ·
                  refine ⟨13175367707380843900130051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8783578471587229266753367 13175367707380843900130051)
                  ·
                    refine ⟨19763051561071265850195077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13175367707380843900130051 19763051561071265850195077)
                    ·
                      refine ⟨3705572167700862346911577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19763051561071265850195077 3705572167700862346911577)
                      ·
                        rfl

theorem cell23_7216576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 3, 4, 1, 1, 4].length) (baseStart_7216576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7216576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7216576 prefixEnd_7216576 := by exact prefixLift 7216576
  have htrace : WordTrace (prefixWord ++ tailWord_7216576) baseStart_7216576 baseEnd_7216576 := by
    simpa [prefixWord, tailWord_7216576, baseEnd_7216576] using wordTrace_append hprefix tailTrace_7216576
  have hstable : (prefixWord ++ tailWord_7216576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7216576).length < 2 ^ (prefixWord ++ tailWord_7216576).sum := by decide
  have hdescent : baseEnd_7216576 < baseStart_7216576 := by decide
  rcases family_descends (prefixWord ++ tailWord_7216576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7216586 : List Nat := [3, 1, 2, 1, 2, 3, 1, 2, 4, 4]
def baseStart_7216586 : Nat := 118140960795 + 7216586 * 2 ^ 59
def prefixEnd_7216586 : Nat := 4983230072969 + 3 ^ 40 * 7216586 * 2
def baseEnd_7216586 : Nat := 1235192434169135769262177

theorem tailTrace_7216586 : CollatzResearch.WordTrace tailWord_7216586 prefixEnd_7216586 1235192434169135769262177 := by
  unfold tailWord_7216586
  simp only [CollatzResearch.WordTrace]
  refine ⟨65802628758387222902497403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175473676689032594406659741 65802628758387222902497403)
  ·
    refine ⟨98703943137580834353746105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65802628758387222902497403 98703943137580834353746105)
    ·
      refine ⟨74027957353185625765309579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98703943137580834353746105 74027957353185625765309579)
      ·
        refine ⟨111041936029778438647964369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74027957353185625765309579 111041936029778438647964369)
        ·
          refine ⟨83281452022333828985973277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111041936029778438647964369 83281452022333828985973277)
          ·
            refine ⟨31230544508375185869739979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 83281452022333828985973277 31230544508375185869739979)
            ·
              refine ⟨46845816762562778804609969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31230544508375185869739979 46845816762562778804609969)
              ·
                refine ⟨35134362571922084103457477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46845816762562778804609969 35134362571922084103457477)
                ·
                  refine ⟨6587692982235390769398277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35134362571922084103457477 6587692982235390769398277)
                  ·
                    refine ⟨1235192434169135769262177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6587692982235390769398277 1235192434169135769262177)
                    ·
                      rfl

theorem cell23_7216586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 1, 2, 4, 4].length) (baseStart_7216586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7216586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7216586 prefixEnd_7216586 := by exact prefixLift 7216586
  have htrace : WordTrace (prefixWord ++ tailWord_7216586) baseStart_7216586 baseEnd_7216586 := by
    simpa [prefixWord, tailWord_7216586, baseEnd_7216586] using wordTrace_append hprefix tailTrace_7216586
  have hstable : (prefixWord ++ tailWord_7216586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7216586).length < 2 ^ (prefixWord ++ tailWord_7216586).sum := by decide
  have hdescent : baseEnd_7216586 < baseStart_7216586 := by decide
  rcases family_descends (prefixWord ++ tailWord_7216586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7216630 : List Nat := [5, 1, 1, 1, 2, 2, 3, 2, 1, 2, 3]
def baseStart_7216630 : Nat := 118140960795 + 7216630 * 2 ^ 59
def prefixEnd_7216630 : Nat := 4983230072969 + 3 ^ 40 * 7216630 * 2
def baseEnd_7216630 : Nat := 3705599895656205135636329

theorem tailTrace_7216630 : CollatzResearch.WordTrace tailWord_7216630 prefixEnd_7216630 3705599895656205135636329 := by
  unfold tailWord_7216630
  simp only [CollatzResearch.WordTrace]
  refine ⟨16450757490336842945286959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 175474746563592991416394229 16450757490336842945286959)
  ·
    refine ⟨24676136235505264417930439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16450757490336842945286959 24676136235505264417930439)
    ·
      refine ⟨37014204353257896626895659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24676136235505264417930439 37014204353257896626895659)
      ·
        refine ⟨55521306529886844940343489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37014204353257896626895659 55521306529886844940343489)
        ·
          refine ⟨41640979897415133705257617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55521306529886844940343489 41640979897415133705257617)
          ·
            refine ⟨31230734923061350278943213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41640979897415133705257617 31230734923061350278943213)
            ·
              refine ⟨11711525596148006354603705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31230734923061350278943213 11711525596148006354603705)
              ·
                refine ⟨8783644197111004765952779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11711525596148006354603705 8783644197111004765952779)
                ·
                  refine ⟨13175466295666507148929169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8783644197111004765952779 13175466295666507148929169)
                  ·
                    refine ⟨9881599721749880361696877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13175466295666507148929169 9881599721749880361696877)
                    ·
                      refine ⟨3705599895656205135636329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9881599721749880361696877 3705599895656205135636329)
                      ·
                        rfl

theorem cell23_7216630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 3, 2, 1, 2, 3].length) (baseStart_7216630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7216630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7216630 prefixEnd_7216630 := by exact prefixLift 7216630
  have htrace : WordTrace (prefixWord ++ tailWord_7216630) baseStart_7216630 baseEnd_7216630 := by
    simpa [prefixWord, tailWord_7216630, baseEnd_7216630] using wordTrace_append hprefix tailTrace_7216630
  have hstable : (prefixWord ++ tailWord_7216630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7216630).length < 2 ^ (prefixWord ++ tailWord_7216630).sum := by decide
  have hdescent : baseEnd_7216630 < baseStart_7216630 := by decide
  rcases family_descends (prefixWord ++ tailWord_7216630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7216639 : List Nat := [1, 1, 2, 2, 1, 2, 2, 3, 2, 2, 5]
def baseStart_7216639 : Nat := 118140960795 + 7216639 * 2 ^ 59
def prefixEnd_7216639 : Nat := 4983230072969 + 3 ^ 40 * 7216639 * 2
def baseEnd_7216639 : Nat := 3705604516982095600423787

theorem tailTrace_7216639 : CollatzResearch.WordTrace tailWord_7216639 prefixEnd_7216639 3705604516982095600423787 := by
  unfold tailWord_7216639
  simp only [CollatzResearch.WordTrace]
  refine ⟨263212448102356881661668971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175474965401571254441112647 263212448102356881661668971)
  ·
    refine ⟨394818672153535322492503457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263212448102356881661668971 394818672153535322492503457)
    ·
      refine ⟨296114004115151491869377593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 394818672153535322492503457 296114004115151491869377593)
      ·
        refine ⟨222085503086363618902033195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 296114004115151491869377593 222085503086363618902033195)
        ·
          refine ⟨333128254629545428353049793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 222085503086363618902033195 333128254629545428353049793)
          ·
            refine ⟨249846190972159071264787345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 333128254629545428353049793 249846190972159071264787345)
            ·
              refine ⟨187384643229119303448590509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 249846190972159071264787345 187384643229119303448590509)
              ·
                refine ⟨70269241210919738793221441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 187384643229119303448590509 70269241210919738793221441)
                ·
                  refine ⟨52701930908189804094916081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 70269241210919738793221441 52701930908189804094916081)
                  ·
                    refine ⟨39526448181142353071187061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 52701930908189804094916081 39526448181142353071187061)
                    ·
                      refine ⟨3705604516982095600423787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39526448181142353071187061 3705604516982095600423787)
                      ·
                        rfl

theorem cell23_7216639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 3, 2, 2, 5].length) (baseStart_7216639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7216639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7216639 prefixEnd_7216639 := by exact prefixLift 7216639
  have htrace : WordTrace (prefixWord ++ tailWord_7216639) baseStart_7216639 baseEnd_7216639 := by
    simpa [prefixWord, tailWord_7216639, baseEnd_7216639] using wordTrace_append hprefix tailTrace_7216639
  have hstable : (prefixWord ++ tailWord_7216639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7216639).length < 2 ^ (prefixWord ++ tailWord_7216639).sum := by decide
  have hdescent : baseEnd_7216639 < baseStart_7216639 := by decide
  rcases family_descends (prefixWord ++ tailWord_7216639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7216683 : List Nat := [1, 1, 1, 1, 2, 1, 3, 1, 8, 2, 2]
def baseStart_7216683 : Nat := 118140960795 + 7216683 * 2 ^ 59
def prefixEnd_7216683 : Nat := 4983230072969 + 3 ^ 40 * 7216683 * 2
def baseEnd_7216683 : Nat := 3705627110130893428273585

theorem tailTrace_7216683 : CollatzResearch.WordTrace tailWord_7216683 prefixEnd_7216683 3705627110130893428273585 := by
  unfold tailWord_7216683
  simp only [CollatzResearch.WordTrace]
  refine ⟨263214052914197477176270703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175476035276131651450847135 263214052914197477176270703)
  ·
    refine ⟨394821079371296215764406055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263214052914197477176270703 394821079371296215764406055)
    ·
      refine ⟨592231619056944323646609083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 394821079371296215764406055 592231619056944323646609083)
      ·
        refine ⟨888347428585416485469913625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 592231619056944323646609083 888347428585416485469913625)
        ·
          refine ⟨666260571439062364102435219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 888347428585416485469913625 666260571439062364102435219)
          ·
            refine ⟨999390857158593546153652829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 666260571439062364102435219 999390857158593546153652829)
            ·
              refine ⟨374771571434472579807619811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 999390857158593546153652829 374771571434472579807619811)
              ·
                refine ⟨562157357151708869711429717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 374771571434472579807619811 562157357151708869711429717)
                ·
                  refine ⟨6587781529121588316930817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 562157357151708869711429717 6587781529121588316930817)
                  ·
                    refine ⟨4940836146841191237698113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6587781529121588316930817 4940836146841191237698113)
                    ·
                      refine ⟨3705627110130893428273585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4940836146841191237698113 3705627110130893428273585)
                      ·
                        rfl

theorem cell23_7216683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 1, 8, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 1, 8, 2, 2].length) (baseStart_7216683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7216683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7216683 prefixEnd_7216683 := by exact prefixLift 7216683
  have htrace : WordTrace (prefixWord ++ tailWord_7216683) baseStart_7216683 baseEnd_7216683 := by
    simpa [prefixWord, tailWord_7216683, baseEnd_7216683] using wordTrace_append hprefix tailTrace_7216683
  have hstable : (prefixWord ++ tailWord_7216683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7216683).length < 2 ^ (prefixWord ++ tailWord_7216683).sum := by decide
  have hdescent : baseEnd_7216683 < baseStart_7216683 := by decide
  rcases family_descends (prefixWord ++ tailWord_7216683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7216743 : List Nat := [1, 1, 5, 1, 1, 1, 2, 2, 2, 5, 2]
def baseStart_7216743 : Nat := 118140960795 + 7216743 * 2 ^ 59
def prefixEnd_7216743 : Nat := 4983230072969 + 3 ^ 40 * 7216743 * 2
def baseEnd_7216743 : Nat := 3705657918970163193523309

theorem tailTrace_7216743 : CollatzResearch.WordTrace tailWord_7216743 prefixEnd_7216743 3705657918970163193523309 := by
  unfold tailWord_7216743
  simp only [CollatzResearch.WordTrace]
  refine ⟨263216241293980107423454883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175477494195986738282303255 263216241293980107423454883)
  ·
    refine ⟨394824361940970161135182325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263216241293980107423454883 394824361940970161135182325)
    ·
      refine ⟨37014783931965952606423343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 394824361940970161135182325 37014783931965952606423343)
      ·
        refine ⟨55522175897948928909635015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37014783931965952606423343 55522175897948928909635015)
        ·
          refine ⟨83283263846923393364452523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55522175897948928909635015 83283263846923393364452523)
          ·
            refine ⟨124924895770385090046678785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83283263846923393364452523 124924895770385090046678785)
            ·
              refine ⟨93693671827788817535009089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 124924895770385090046678785 93693671827788817535009089)
              ·
                refine ⟨70270253870841613151256817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 93693671827788817535009089 70270253870841613151256817)
                ·
                  refine ⟨52702690403131209863442613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 70270253870841613151256817 52702690403131209863442613)
                  ·
                    refine ⟨4940877225293550924697745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 52702690403131209863442613 4940877225293550924697745)
                    ·
                      refine ⟨3705657918970163193523309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4940877225293550924697745 3705657918970163193523309)
                      ·
                        rfl

theorem cell23_7216743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 2, 2, 5, 2].length) (baseStart_7216743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7216743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7216743 prefixEnd_7216743 := by exact prefixLift 7216743
  have htrace : WordTrace (prefixWord ++ tailWord_7216743) baseStart_7216743 baseEnd_7216743 := by
    simpa [prefixWord, tailWord_7216743, baseEnd_7216743] using wordTrace_append hprefix tailTrace_7216743
  have hstable : (prefixWord ++ tailWord_7216743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7216743).length < 2 ^ (prefixWord ++ tailWord_7216743).sum := by decide
  have hdescent : baseEnd_7216743 < baseStart_7216743 := by decide
  rcases family_descends (prefixWord ++ tailWord_7216743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7216757 : List Nat := [1, 3, 4, 2, 1, 3, 1, 3, 5]
def baseStart_7216757 : Nat := 118140960795 + 7216757 * 2 ^ 59
def prefixEnd_7216757 : Nat := 4983230072969 + 3 ^ 40 * 7216757 * 2
def baseEnd_7216757 : Nat := 411740567522147348749805

theorem tailTrace_7216757 : CollatzResearch.WordTrace tailWord_7216757 prefixEnd_7216757 411740567522147348749805 := by
  unfold tailWord_7216757
  simp only [CollatzResearch.WordTrace]
  refine ⟨263216751915929387814464525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175477834610619591876309683 263216751915929387814464525)
  ·
    refine ⟨98706281968473520430424197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 263216751915929387814464525 98706281968473520430424197)
    ·
      refine ⟨18507427869088785080704537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 98706281968473520430424197 18507427869088785080704537)
      ·
        refine ⟨13880570901816588810528403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18507427869088785080704537 13880570901816588810528403)
        ·
          refine ⟨20820856352724883215792605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13880570901816588810528403 20820856352724883215792605)
          ·
            refine ⟨7807821132271831205922227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20820856352724883215792605 7807821132271831205922227)
            ·
              refine ⟨11711731698407746808883341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7807821132271831205922227 11711731698407746808883341)
              ·
                refine ⟨4391899386902905053331253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11711731698407746808883341 4391899386902905053331253)
                ·
                  refine ⟨411740567522147348749805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4391899386902905053331253 411740567522147348749805)
                  ·
                    rfl

theorem cell23_7216757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 3, 1, 3, 5].length) (baseStart_7216757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7216757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7216757 prefixEnd_7216757 := by exact prefixLift 7216757
  have htrace : WordTrace (prefixWord ++ tailWord_7216757) baseStart_7216757 baseEnd_7216757 := by
    simpa [prefixWord, tailWord_7216757, baseEnd_7216757] using wordTrace_append hprefix tailTrace_7216757
  have hstable : (prefixWord ++ tailWord_7216757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7216757).length < 2 ^ (prefixWord ++ tailWord_7216757).sum := by decide
  have hdescent : baseEnd_7216757 < baseStart_7216757 := by decide
  rcases family_descends (prefixWord ++ tailWord_7216757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7216773 : List Nat := [1, 3, 1, 1, 4, 1, 3, 2, 2, 1, 4]
def baseStart_7216773 : Nat := 118140960795 + 7216773 * 2 ^ 59
def prefixEnd_7216773 : Nat := 4983230072969 + 3 ^ 40 * 7216773 * 2
def baseEnd_7216773 : Nat := 3705673323389798076148171

theorem tailTrace_7216773 : CollatzResearch.WordTrace tailWord_7216773 prefixEnd_7216773 3705673323389798076148171 := by
  unfold tailWord_7216773
  simp only [CollatzResearch.WordTrace]
  refine ⟨263217335483871422547046973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175478223655914281698031315 263217335483871422547046973)
  ·
    refine ⟨98706500806451783455142615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 263217335483871422547046973 98706500806451783455142615)
    ·
      refine ⟨148059751209677675182713923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98706500806451783455142615 148059751209677675182713923)
      ·
        refine ⟨222089626814516512774070885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148059751209677675182713923 222089626814516512774070885)
        ·
          refine ⟨41641805027721846145138291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 222089626814516512774070885 41641805027721846145138291)
          ·
            refine ⟨62462707541582769217707437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41641805027721846145138291 62462707541582769217707437)
            ·
              refine ⟨23423515328093538456640289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62462707541582769217707437 23423515328093538456640289)
              ·
                refine ⟨17567636496070153842480217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23423515328093538456640289 17567636496070153842480217)
                ·
                  refine ⟨13175727372052615381860163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17567636496070153842480217 13175727372052615381860163)
                  ·
                    refine ⟨19763591058078923072790245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13175727372052615381860163 19763591058078923072790245)
                    ·
                      refine ⟨3705673323389798076148171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19763591058078923072790245 3705673323389798076148171)
                      ·
                        rfl

theorem cell23_7216773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 3, 2, 2, 1, 4].length) (baseStart_7216773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7216773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7216773 prefixEnd_7216773 := by exact prefixLift 7216773
  have htrace : WordTrace (prefixWord ++ tailWord_7216773) baseStart_7216773 baseEnd_7216773 := by
    simpa [prefixWord, tailWord_7216773, baseEnd_7216773] using wordTrace_append hprefix tailTrace_7216773
  have hstable : (prefixWord ++ tailWord_7216773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7216773).length < 2 ^ (prefixWord ++ tailWord_7216773).sum := by decide
  have hdescent : baseEnd_7216773 < baseStart_7216773 := by decide
  rcases family_descends (prefixWord ++ tailWord_7216773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7216830 : List Nat := [4, 2, 1, 1, 2, 3, 2, 2, 6]
def baseStart_7216830 : Nat := 118140960795 + 7216830 * 2 ^ 59
def prefixEnd_7216830 : Nat := 4983230072969 + 3 ^ 40 * 7216830 * 2
def baseEnd_7216830 : Nat := 411744732420789372570601

theorem tailTrace_7216830 : CollatzResearch.WordTrace tailWord_7216830 prefixEnd_7216830 411744732420789372570601 := by
  unfold tailWord_7216830
  simp only [CollatzResearch.WordTrace]
  refine ⟨32902426805583115160233993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 175479609629776614187914629 32902426805583115160233993)
  ·
    refine ⟨24676820104187336370175495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32902426805583115160233993 24676820104187336370175495)
    ·
      refine ⟨37015230156281004555263243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24676820104187336370175495 37015230156281004555263243)
      ·
        refine ⟨55522845234421506832894865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37015230156281004555263243 55522845234421506832894865)
        ·
          refine ⟨41642133925816130124671149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55522845234421506832894865 41642133925816130124671149)
          ·
            refine ⟨15615800222181048796751681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41642133925816130124671149 15615800222181048796751681)
            ·
              refine ⟨11711850166635786597563761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15615800222181048796751681 11711850166635786597563761)
              ·
                refine ⟨8783887624976839948172821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11711850166635786597563761 8783887624976839948172821)
                ·
                  refine ⟨411744732420789372570601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8783887624976839948172821 411744732420789372570601)
                  ·
                    rfl

theorem cell23_7216830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 2, 2, 6].length) (baseStart_7216830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7216830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7216830 prefixEnd_7216830 := by exact prefixLift 7216830
  have htrace : WordTrace (prefixWord ++ tailWord_7216830) baseStart_7216830 baseEnd_7216830 := by
    simpa [prefixWord, tailWord_7216830, baseEnd_7216830] using wordTrace_append hprefix tailTrace_7216830
  have hstable : (prefixWord ++ tailWord_7216830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7216830).length < 2 ^ (prefixWord ++ tailWord_7216830).sum := by decide
  have hdescent : baseEnd_7216830 < baseStart_7216830 := by decide
  rcases family_descends (prefixWord ++ tailWord_7216830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7216840 : List Nat := [2, 1, 3, 1, 2, 2, 2, 3, 3, 1, 3]
def baseStart_7216840 : Nat := 118140960795 + 7216840 * 2 ^ 59
def prefixEnd_7216840 : Nat := 4983230072969 + 3 ^ 40 * 7216840 * 2
def baseEnd_7216840 : Nat := 3705707726593649314010363

theorem tailTrace_7216840 : CollatzResearch.WordTrace tailWord_7216840 prefixEnd_7216840 3705707726593649314010363 := by
  unfold tailWord_7216840
  simp only [CollatzResearch.WordTrace]
  refine ⟨131609889587314346494867987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175479852783085795326490649 131609889587314346494867987)
  ·
    refine ⟨197414834380971519742301981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131609889587314346494867987 197414834380971519742301981)
    ·
      refine ⟨74030562892864319903363243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 197414834380971519742301981 74030562892864319903363243)
      ·
        refine ⟨111045844339296479855044865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74030562892864319903363243 111045844339296479855044865)
        ·
          refine ⟨83284383254472359891283649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111045844339296479855044865 83284383254472359891283649)
          ·
            refine ⟨62463287440854269918462737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83284383254472359891283649 62463287440854269918462737)
            ·
              refine ⟨46847465580640702438847053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62463287440854269918462737 46847465580640702438847053)
              ·
                refine ⟨17567799592740263414567645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46847465580640702438847053 17567799592740263414567645)
                ·
                  refine ⟨6587924847277598780462867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17567799592740263414567645 6587924847277598780462867)
                  ·
                    refine ⟨9881887270916398170694301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6587924847277598780462867 9881887270916398170694301)
                    ·
                      refine ⟨3705707726593649314010363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9881887270916398170694301 3705707726593649314010363)
                      ·
                        rfl

theorem cell23_7216840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 2, 3, 3, 1, 3].length) (baseStart_7216840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7216840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7216840 prefixEnd_7216840 := by exact prefixLift 7216840
  have htrace : WordTrace (prefixWord ++ tailWord_7216840) baseStart_7216840 baseEnd_7216840 := by
    simpa [prefixWord, tailWord_7216840, baseEnd_7216840] using wordTrace_append hprefix tailTrace_7216840
  have hstable : (prefixWord ++ tailWord_7216840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7216840).length < 2 ^ (prefixWord ++ tailWord_7216840).sum := by decide
  have hdescent : baseEnd_7216840 < baseStart_7216840 := by decide
  rcases family_descends (prefixWord ++ tailWord_7216840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7216861 : List Nat := [1, 4, 3, 3, 2, 1, 1, 1, 2, 2, 3]
def baseStart_7216861 : Nat := 118140960795 + 7216861 * 2 ^ 59
def prefixEnd_7216861 : Nat := 4983230072969 + 3 ^ 40 * 7216861 * 2
def baseEnd_7216861 : Nat := 3705718509687393731847767

theorem tailTrace_7216861 : CollatzResearch.WordTrace tailWord_7216861 prefixEnd_7216861 3705718509687393731847767 := by
  unfold tailWord_7216861
  simp only [CollatzResearch.WordTrace]
  refine ⟨263220545107552613576250437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175480363405035075717500291 263220545107552613576250437)
  ·
    refine ⟨49353852207666115045546957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 263220545107552613576250437 49353852207666115045546957)
    ·
      refine ⟨18507694577874793142080109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49353852207666115045546957 18507694577874793142080109)
      ·
        refine ⟨6940385466703047428280041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18507694577874793142080109 6940385466703047428280041)
        ·
          refine ⟨5205289100027285571210031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6940385466703047428280041 5205289100027285571210031)
          ·
            refine ⟨7807933650040928356815047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5205289100027285571210031 7807933650040928356815047)
            ·
              refine ⟨11711900475061392535222571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7807933650040928356815047 11711900475061392535222571)
              ·
                refine ⟨17567850712592088802833857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11711900475061392535222571 17567850712592088802833857)
                ·
                  refine ⟨13175888034444066602125393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17567850712592088802833857 13175888034444066602125393)
                  ·
                    refine ⟨9881916025833049951594045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13175888034444066602125393 9881916025833049951594045)
                    ·
                      refine ⟨3705718509687393731847767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9881916025833049951594045 3705718509687393731847767)
                      ·
                        rfl

theorem cell23_7216861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 2, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 2, 1, 1, 1, 2, 2, 3].length) (baseStart_7216861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7216861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7216861 prefixEnd_7216861 := by exact prefixLift 7216861
  have htrace : WordTrace (prefixWord ++ tailWord_7216861) baseStart_7216861 baseEnd_7216861 := by
    simpa [prefixWord, tailWord_7216861, baseEnd_7216861] using wordTrace_append hprefix tailTrace_7216861
  have hstable : (prefixWord ++ tailWord_7216861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7216861).length < 2 ^ (prefixWord ++ tailWord_7216861).sum := by decide
  have hdescent : baseEnd_7216861 < baseStart_7216861 := by decide
  rcases family_descends (prefixWord ++ tailWord_7216861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7216863 : List Nat := [1, 1, 2, 3, 2, 2, 1, 3, 3, 1, 4]
def baseStart_7216863 : Nat := 118140960795 + 7216863 * 2 ^ 59
def prefixEnd_7216863 : Nat := 4983230072969 + 3 ^ 40 * 7216863 * 2
def baseEnd_7216863 : Nat := 3705719536648702724022757

theorem tailTrace_7216863 : CollatzResearch.WordTrace tailWord_7216863 prefixEnd_7216863 3705719536648702724022757 := by
  unfold tailWord_7216863
  simp only [CollatzResearch.WordTrace]
  refine ⟨263220618053545367917823243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175480412035696911945215495 263220618053545367917823243)
  ·
    refine ⟨394830927080318051876734865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263220618053545367917823243 394830927080318051876734865)
    ·
      refine ⟨296123195310238538907551149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 394830927080318051876734865 296123195310238538907551149)
      ·
        refine ⟨111046198241339452090331681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 296123195310238538907551149 111046198241339452090331681)
        ·
          refine ⟨83284648681004589067748761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111046198241339452090331681 83284648681004589067748761)
          ·
            refine ⟨62463486510753441800811571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83284648681004589067748761 62463486510753441800811571)
            ·
              refine ⟨93695229766130162701217357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62463486510753441800811571 93695229766130162701217357)
              ·
                refine ⟨35135711162298811012956509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 93695229766130162701217357 35135711162298811012956509)
                ·
                  refine ⟨13175891685862054129858691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35135711162298811012956509 13175891685862054129858691)
                  ·
                    refine ⟨19763837528793081194788037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13175891685862054129858691 19763837528793081194788037)
                    ·
                      refine ⟨3705719536648702724022757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19763837528793081194788037 3705719536648702724022757)
                      ·
                        rfl

theorem cell23_7216863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 3, 3, 1, 4].length) (baseStart_7216863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7216863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7216863 prefixEnd_7216863 := by exact prefixLift 7216863
  have htrace : WordTrace (prefixWord ++ tailWord_7216863) baseStart_7216863 baseEnd_7216863 := by
    simpa [prefixWord, tailWord_7216863, baseEnd_7216863] using wordTrace_append hprefix tailTrace_7216863
  have hstable : (prefixWord ++ tailWord_7216863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7216863).length < 2 ^ (prefixWord ++ tailWord_7216863).sum := by decide
  have hdescent : baseEnd_7216863 < baseStart_7216863 := by decide
  rcases family_descends (prefixWord ++ tailWord_7216863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7216867 : List Nat := [1, 1, 1, 7, 2, 1, 1, 1, 1, 5, 2]
def baseStart_7216867 : Nat := 118140960795 + 7216867 * 2 ^ 59
def prefixEnd_7216867 : Nat := 4983230072969 + 3 ^ 40 * 7216867 * 2
def baseEnd_7216867 : Nat := 3705721590571320708372739

theorem tailTrace_7216867 : CollatzResearch.WordTrace tailWord_7216867 prefixEnd_7216867 3705721590571320708372739 := by
  unfold tailWord_7216867
  simp only [CollatzResearch.WordTrace]
  refine ⟨263220763945530876600968855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175480509297020584400645903 263220763945530876600968855)
  ·
    refine ⟨394831145918296314901453283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263220763945530876600968855 394831145918296314901453283)
    ·
      refine ⟨592246718877444472352179925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 394831145918296314901453283 592246718877444472352179925)
      ·
        refine ⟨13880782473690104820754217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 592246718877444472352179925 13880782473690104820754217)
        ·
          refine ⟨10410586855267578615565663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13880782473690104820754217 10410586855267578615565663)
          ·
            refine ⟨15615880282901367923348495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10410586855267578615565663 15615880282901367923348495)
            ·
              refine ⟨23423820424352051885022743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15615880282901367923348495 23423820424352051885022743)
              ·
                refine ⟨35135730636528077827534115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23423820424352051885022743 35135730636528077827534115)
                ·
                  refine ⟨52703595954792116741301173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35135730636528077827534115 52703595954792116741301173)
                  ·
                    refine ⟨4940962120761760944496985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 52703595954792116741301173 4940962120761760944496985)
                    ·
                      refine ⟨3705721590571320708372739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4940962120761760944496985 3705721590571320708372739)
                      ·
                        rfl

theorem cell23_7216867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 1, 1, 1, 5, 2].length) (baseStart_7216867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7216867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7216867 prefixEnd_7216867 := by exact prefixLift 7216867
  have htrace : WordTrace (prefixWord ++ tailWord_7216867) baseStart_7216867 baseEnd_7216867 := by
    simpa [prefixWord, tailWord_7216867, baseEnd_7216867] using wordTrace_append hprefix tailTrace_7216867
  have hstable : (prefixWord ++ tailWord_7216867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7216867).length < 2 ^ (prefixWord ++ tailWord_7216867).sum := by decide
  have hdescent : baseEnd_7216867 < baseStart_7216867 := by decide
  rcases family_descends (prefixWord ++ tailWord_7216867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7216873 : List Nat := [1, 2, 1, 1, 1, 2, 3, 4, 4, 4]
def baseStart_7216873 : Nat := 118140960795 + 7216873 * 2 ^ 59
def prefixEnd_7216873 : Nat := 4983230072969 + 3 ^ 40 * 7216873 * 2
def baseEnd_7216873 : Nat := 1235241557151749228299237

theorem tailTrace_7216873 : CollatzResearch.WordTrace tailWord_7216873 prefixEnd_7216873 1235241557151749228299237 := by
  unfold tailWord_7216873
  simp only [CollatzResearch.WordTrace]
  refine ⟨263220982783509139625687273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175480655189006093083791515 263220982783509139625687273)
  ·
    refine ⟨197415737087631854719265455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 263220982783509139625687273 197415737087631854719265455)
    ·
      refine ⟨296123605631447782078898183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197415737087631854719265455 296123605631447782078898183)
      ·
        refine ⟨444185408447171673118347275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 296123605631447782078898183 444185408447171673118347275)
        ·
          refine ⟨666278112670757509677520913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 444185408447171673118347275 666278112670757509677520913)
          ·
            refine ⟨499708584503068132258140685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 666278112670757509677520913 499708584503068132258140685)
            ·
              refine ⟨187390719188650549596802757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 499708584503068132258140685 187390719188650549596802757)
              ·
                refine ⟨35135759847871978049400517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 187390719188650549596802757 35135759847871978049400517)
                ·
                  refine ⟨6587954971475995884262597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35135759847871978049400517 6587954971475995884262597)
                  ·
                    refine ⟨1235241557151749228299237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6587954971475995884262597 1235241557151749228299237)
                    ·
                      rfl

theorem cell23_7216873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 4, 4, 4].length) (baseStart_7216873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7216873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7216873 prefixEnd_7216873 := by exact prefixLift 7216873
  have htrace : WordTrace (prefixWord ++ tailWord_7216873) baseStart_7216873 baseEnd_7216873 := by
    simpa [prefixWord, tailWord_7216873, baseEnd_7216873] using wordTrace_append hprefix tailTrace_7216873
  have hstable : (prefixWord ++ tailWord_7216873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7216873).length < 2 ^ (prefixWord ++ tailWord_7216873).sum := by decide
  have hdescent : baseEnd_7216873 < baseStart_7216873 := by decide
  rcases family_descends (prefixWord ++ tailWord_7216873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7216877 : List Nat := [1, 5, 1, 2, 1, 2, 4, 1, 1, 5]
def baseStart_7216877 : Nat := 118140960795 + 7216877 * 2 ^ 59
def prefixEnd_7216877 : Nat := 4983230072969 + 3 ^ 40 * 7216877 * 2
def baseEnd_7216877 : Nat := 1235242241792621889749231

theorem tailTrace_7216877 : CollatzResearch.WordTrace tailWord_7216877 prefixEnd_7216877 1235242241792621889749231 := by
  unfold tailWord_7216877
  simp only [CollatzResearch.WordTrace]
  refine ⟨263221128675494648308832885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175480752450329765539221923 263221128675494648308832885)
  ·
    refine ⟨24676980813327623278953083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 263221128675494648308832885 24676980813327623278953083)
    ·
      refine ⟨37015471219991434918429625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24676980813327623278953083 37015471219991434918429625)
      ·
        refine ⟨27761603414993576188822219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37015471219991434918429625 27761603414993576188822219)
        ·
          refine ⟨41642405122490364283233329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27761603414993576188822219 41642405122490364283233329)
          ·
            refine ⟨31231803841867773212424997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41642405122490364283233329 31231803841867773212424997)
            ·
              refine ⟨5855963220350207477329687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31231803841867773212424997 5855963220350207477329687)
              ·
                refine ⟨8783944830525311215994531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5855963220350207477329687 8783944830525311215994531)
                ·
                  refine ⟨13175917245787966823991797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8783944830525311215994531 13175917245787966823991797)
                  ·
                    refine ⟨1235242241792621889749231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13175917245787966823991797 1235242241792621889749231)
                    ·
                      rfl

theorem cell23_7216877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 4, 1, 1, 5].length) (baseStart_7216877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7216877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7216877 prefixEnd_7216877 := by exact prefixLift 7216877
  have htrace : WordTrace (prefixWord ++ tailWord_7216877) baseStart_7216877 baseEnd_7216877 := by
    simpa [prefixWord, tailWord_7216877, baseEnd_7216877] using wordTrace_append hprefix tailTrace_7216877
  have hstable : (prefixWord ++ tailWord_7216877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7216877).length < 2 ^ (prefixWord ++ tailWord_7216877).sum := by decide
  have hdescent : baseEnd_7216877 < baseStart_7216877 := by decide
  rcases family_descends (prefixWord ++ tailWord_7216877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7216897 : List Nat := [1, 2, 4, 1, 1, 1, 3, 3, 3, 2, 2]
def baseStart_7216897 : Nat := 118140960795 + 7216897 * 2 ^ 59
def prefixEnd_7216897 : Nat := 4983230072969 + 3 ^ 40 * 7216897 * 2
def baseEnd_7216897 : Nat := 3705736994990955590997601

theorem tailTrace_7216897 : CollatzResearch.WordTrace tailWord_7216897 prefixEnd_7216897 3705736994990955590997601 := by
  unfold tailWord_7216897
  simp only [CollatzResearch.WordTrace]
  refine ⟨263221858135422191724560945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175481238756948127816373963 263221858135422191724560945)
  ·
    refine ⟨197416393601566643793420709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 263221858135422191724560945 197416393601566643793420709)
    ·
      refine ⟨37015573800293745711266383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 197416393601566643793420709 37015573800293745711266383)
      ·
        refine ⟨55523360700440618566899575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37015573800293745711266383 55523360700440618566899575)
        ·
          refine ⟨83285041050660927850349363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55523360700440618566899575 83285041050660927850349363)
          ·
            refine ⟨124927561575991391775524045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83285041050660927850349363 124927561575991391775524045)
            ·
              refine ⟨46847835590996771915821517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 124927561575991391775524045 46847835590996771915821517)
              ·
                refine ⟨17567938346623789468433069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46847835590996771915821517 17567938346623789468433069)
                ·
                  refine ⟨6587976879983921050662401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17567938346623789468433069 6587976879983921050662401)
                  ·
                    refine ⟨4940982659987940787996801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6587976879983921050662401 4940982659987940787996801)
                    ·
                      refine ⟨3705736994990955590997601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4940982659987940787996801 3705736994990955590997601)
                      ·
                        rfl

theorem cell23_7216897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 3, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 3, 3, 3, 2, 2].length) (baseStart_7216897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7216897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7216897 prefixEnd_7216897 := by exact prefixLift 7216897
  have htrace : WordTrace (prefixWord ++ tailWord_7216897) baseStart_7216897 baseEnd_7216897 := by
    simpa [prefixWord, tailWord_7216897, baseEnd_7216897] using wordTrace_append hprefix tailTrace_7216897
  have hstable : (prefixWord ++ tailWord_7216897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7216897).length < 2 ^ (prefixWord ++ tailWord_7216897).sum := by decide
  have hdescent : baseEnd_7216897 < baseStart_7216897 := by decide
  rcases family_descends (prefixWord ++ tailWord_7216897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7216900 : List Nat := [2, 3, 2, 2, 1, 3, 1, 2, 1, 1, 5]
def baseStart_7216900 : Nat := 118140960795 + 7216900 * 2 ^ 59
def prefixEnd_7216900 : Nat := 4983230072969 + 3 ^ 40 * 7216900 * 2
def baseEnd_7216900 : Nat := 3705738535432919079260087

theorem tailTrace_7216900 : CollatzResearch.WordTrace tailWord_7216900 prefixEnd_7216900 3705738535432919079260087 := by
  unfold tailWord_7216900
  simp only [CollatzResearch.WordTrace]
  refine ⟨131610983777205661618460077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175481311702940882157946769 131610983777205661618460077)
  ·
    refine ⟨49354118916452123106922529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 131610983777205661618460077 49354118916452123106922529)
    ·
      refine ⟨37015589187339092330191897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49354118916452123106922529 37015589187339092330191897)
      ·
        refine ⟨27761691890504319247643923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37015589187339092330191897 27761691890504319247643923)
        ·
          refine ⟨41642537835756478871465885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27761691890504319247643923 41642537835756478871465885)
          ·
            refine ⟨15615951688408679576799707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41642537835756478871465885 15615951688408679576799707)
            ·
              refine ⟨23423927532613019365199561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15615951688408679576799707 23423927532613019365199561)
              ·
                refine ⟨17567945649459764523899671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23423927532613019365199561 17567945649459764523899671)
                ·
                  refine ⟨26351918474189646785849507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17567945649459764523899671 26351918474189646785849507)
                  ·
                    refine ⟨39527877711284470178774261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26351918474189646785849507 39527877711284470178774261)
                    ·
                      refine ⟨3705738535432919079260087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39527877711284470178774261 3705738535432919079260087)
                      ·
                        rfl

theorem cell23_7216900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 1, 2, 1, 1, 5].length) (baseStart_7216900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7216900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7216900 prefixEnd_7216900 := by exact prefixLift 7216900
  have htrace : WordTrace (prefixWord ++ tailWord_7216900) baseStart_7216900 baseEnd_7216900 := by
    simpa [prefixWord, tailWord_7216900, baseEnd_7216900] using wordTrace_append hprefix tailTrace_7216900
  have hstable : (prefixWord ++ tailWord_7216900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7216900).length < 2 ^ (prefixWord ++ tailWord_7216900).sum := by decide
  have hdescent : baseEnd_7216900 < baseStart_7216900 := by decide
  rcases family_descends (prefixWord ++ tailWord_7216900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7216910 : List Nat := [4, 1, 1, 2, 1, 1, 5, 1, 1, 2, 4]
def baseStart_7216910 : Nat := 118140960795 + 7216910 * 2 ^ 59
def prefixEnd_7216910 : Nat := 4983230072969 + 3 ^ 40 * 7216910 * 2
def baseEnd_7216910 : Nat := 3705743670239464040135041

theorem tailTrace_7216910 : CollatzResearch.WordTrace tailWord_7216910 prefixEnd_7216910 3705743670239464040135041 := by
  unfold tailWord_7216910
  simp only [CollatzResearch.WordTrace]
  refine ⟨32902791535546886868098023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 175481554856250063296522789 32902791535546886868098023)
  ·
    refine ⟨49354187303320330302147035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32902791535546886868098023 49354187303320330302147035)
    ·
      refine ⟨74031280954980495453220553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49354187303320330302147035 74031280954980495453220553)
      ·
        refine ⟨55523460716235371589915415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74031280954980495453220553 55523460716235371589915415)
        ·
          refine ⟨83285191074353057384873123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55523460716235371589915415 83285191074353057384873123)
          ·
            refine ⟨124927786611529586077309685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83285191074353057384873123 124927786611529586077309685)
            ·
              refine ⟨11711979994830898694747783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 124927786611529586077309685 11711979994830898694747783)
              ·
                refine ⟨17567969992246348042121675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11711979994830898694747783 17567969992246348042121675)
                ·
                  refine ⟨26351954988369522063182513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17567969992246348042121675 26351954988369522063182513)
                  ·
                    refine ⟨19763966241277141547386885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26351954988369522063182513 19763966241277141547386885)
                    ·
                      refine ⟨3705743670239464040135041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19763966241277141547386885 3705743670239464040135041)
                      ·
                        rfl

theorem cell23_7216910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 5, 1, 1, 2, 4].length) (baseStart_7216910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7216910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7216910 prefixEnd_7216910 := by exact prefixLift 7216910
  have htrace : WordTrace (prefixWord ++ tailWord_7216910) baseStart_7216910 baseEnd_7216910 := by
    simpa [prefixWord, tailWord_7216910, baseEnd_7216910] using wordTrace_append hprefix tailTrace_7216910
  have hstable : (prefixWord ++ tailWord_7216910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7216910).length < 2 ^ (prefixWord ++ tailWord_7216910).sum := by decide
  have hdescent : baseEnd_7216910 < baseStart_7216910 := by decide
  rcases family_descends (prefixWord ++ tailWord_7216910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7216914 : List Nat := [3, 2, 4, 1, 1, 2, 2, 2, 1, 1, 4]
def baseStart_7216914 : Nat := 118140960795 + 7216914 * 2 ^ 59
def prefixEnd_7216914 : Nat := 4983230072969 + 3 ^ 40 * 7216914 * 2
def baseEnd_7216914 : Nat := 3705745724162082024485023

theorem tailTrace_7216914 : CollatzResearch.WordTrace tailWord_7216914 prefixEnd_7216914 3705745724162082024485023 := by
  unfold tailWord_7216914
  simp only [CollatzResearch.WordTrace]
  refine ⟨65805619544090150906982449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175481652117573735751953197 65805619544090150906982449)
  ·
    refine ⟨49354214658067613180236837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65805619544090150906982449 49354214658067613180236837)
    ·
      refine ⟨9253915248387677471294407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49354214658067613180236837 9253915248387677471294407)
      ·
        refine ⟨13880872872581516206941611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9253915248387677471294407 13880872872581516206941611)
        ·
          refine ⟨20821309308872274310412417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13880872872581516206941611 20821309308872274310412417)
          ·
            refine ⟨15615981981654205732809313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20821309308872274310412417 15615981981654205732809313)
            ·
              refine ⟨11711986486240654299606985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15615981981654205732809313 11711986486240654299606985)
              ·
                refine ⟨8783989864680490724705239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11711986486240654299606985 8783989864680490724705239)
                ·
                  refine ⟨13175984797020736087057859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8783989864680490724705239 13175984797020736087057859)
                  ·
                    refine ⟨19763977195531104130586789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13175984797020736087057859 19763977195531104130586789)
                    ·
                      refine ⟨3705745724162082024485023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19763977195531104130586789 3705745724162082024485023)
                      ·
                        rfl

theorem cell23_7216914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 2, 2, 1, 1, 4].length) (baseStart_7216914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7216914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7216914 prefixEnd_7216914 := by exact prefixLift 7216914
  have htrace : WordTrace (prefixWord ++ tailWord_7216914) baseStart_7216914 baseEnd_7216914 := by
    simpa [prefixWord, tailWord_7216914, baseEnd_7216914] using wordTrace_append hprefix tailTrace_7216914
  have hstable : (prefixWord ++ tailWord_7216914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7216914).length < 2 ^ (prefixWord ++ tailWord_7216914).sum := by decide
  have hdescent : baseEnd_7216914 < baseStart_7216914 := by decide
  rcases family_descends (prefixWord ++ tailWord_7216914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7216917 : List Nat := [1, 3, 2, 1, 2, 4, 2, 2, 1, 2, 3]
def baseStart_7216917 : Nat := 118140960795 + 7216917 * 2 ^ 59
def prefixEnd_7216917 : Nat := 4983230072969 + 3 ^ 40 * 7216917 * 2
def baseEnd_7216917 : Nat := 3705747264604045512747509

theorem tailTrace_7216917 : CollatzResearch.WordTrace tailWord_7216917 prefixEnd_7216917 3705747264604045512747509 := by
  unfold tailWord_7216917
  simp only [CollatzResearch.WordTrace]
  refine ⟨263222587595349735140289005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175481725063566490093526003 263222587595349735140289005)
  ·
    refine ⟨98708470348256150677608377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 263222587595349735140289005 98708470348256150677608377)
    ·
      refine ⟨74031352761192113008206283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98708470348256150677608377 74031352761192113008206283)
      ·
        refine ⟨111047029141788169512309425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74031352761192113008206283 111047029141788169512309425)
        ·
          refine ⟨83285271856341127134232069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111047029141788169512309425 83285271856341127134232069)
          ·
            refine ⟨15615988473063961337668513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 83285271856341127134232069 15615988473063961337668513)
            ·
              refine ⟨11711991354797971003251385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15615988473063961337668513 11711991354797971003251385)
              ·
                refine ⟨8783993516098478252438539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11711991354797971003251385 8783993516098478252438539)
                ·
                  refine ⟨13175990274147717378657809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8783993516098478252438539 13175990274147717378657809)
                  ·
                    refine ⟨9881992705610788033993357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13175990274147717378657809 9881992705610788033993357)
                    ·
                      refine ⟨3705747264604045512747509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9881992705610788033993357 3705747264604045512747509)
                      ·
                        rfl

theorem cell23_7216917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 2, 2, 1, 2, 3].length) (baseStart_7216917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7216917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7216917 prefixEnd_7216917 := by exact prefixLift 7216917
  have htrace : WordTrace (prefixWord ++ tailWord_7216917) baseStart_7216917 baseEnd_7216917 := by
    simpa [prefixWord, tailWord_7216917, baseEnd_7216917] using wordTrace_append hprefix tailTrace_7216917
  have hstable : (prefixWord ++ tailWord_7216917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7216917).length < 2 ^ (prefixWord ++ tailWord_7216917).sum := by decide
  have hdescent : baseEnd_7216917 < baseStart_7216917 := by decide
  rcases family_descends (prefixWord ++ tailWord_7216917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7216930 : List Nat := [3, 3, 1, 1, 2, 1, 2, 1, 3, 3, 3]
def baseStart_7216930 : Nat := 118140960795 + 7216930 * 2 ^ 59
def prefixEnd_7216930 : Nat := 4983230072969 + 3 ^ 40 * 7216930 * 2
def baseEnd_7216930 : Nat := 3705753939852553961884949

theorem tailTrace_7216930 : CollatzResearch.WordTrace tailWord_7216930 prefixEnd_7216930 3705753939852553961884949 := by
  unfold tailWord_7216930
  simp only [CollatzResearch.WordTrace]
  refine ⟨65805765436075659590128061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175482041162868425573674829 65805765436075659590128061)
  ·
    refine ⟨24677162038528372346298023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65805765436075659590128061 24677162038528372346298023)
    ·
      refine ⟨37015743057792558519447035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24677162038528372346298023 37015743057792558519447035)
      ·
        refine ⟨55523614586688837779170553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37015743057792558519447035 55523614586688837779170553)
        ·
          refine ⟨41642710940016628334377915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55523614586688837779170553 41642710940016628334377915)
          ·
            refine ⟨62464066410024942501566873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41642710940016628334377915 62464066410024942501566873)
            ·
              refine ⟨46848049807518706876175155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62464066410024942501566873 46848049807518706876175155)
              ·
                refine ⟨70272074711278060314262733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46848049807518706876175155 70272074711278060314262733)
                ·
                  refine ⟨26352028016729272617848525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 70272074711278060314262733 26352028016729272617848525)
                  ·
                    refine ⟨9882010506273477231693197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26352028016729272617848525 9882010506273477231693197)
                    ·
                      refine ⟨3705753939852553961884949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9882010506273477231693197 3705753939852553961884949)
                      ·
                        rfl

theorem cell23_7216930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 2, 1, 3, 3, 3].length) (baseStart_7216930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7216930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7216930 prefixEnd_7216930 := by exact prefixLift 7216930
  have htrace : WordTrace (prefixWord ++ tailWord_7216930) baseStart_7216930 baseEnd_7216930 := by
    simpa [prefixWord, tailWord_7216930, baseEnd_7216930] using wordTrace_append hprefix tailTrace_7216930
  have hstable : (prefixWord ++ tailWord_7216930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7216930).length < 2 ^ (prefixWord ++ tailWord_7216930).sum := by decide
  have hdescent : baseEnd_7216930 < baseStart_7216930 := by decide
  rcases family_descends (prefixWord ++ tailWord_7216930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7217000 : List Nat := [2, 1, 4, 2, 1, 1, 2, 2, 2, 2, 4]
def baseStart_7217000 : Nat := 118140960795 + 7217000 * 2 ^ 59
def prefixEnd_7217000 : Nat := 4983230072969 + 3 ^ 40 * 7217000 * 2
def baseEnd_7217000 : Nat := 3705789883498368688009627

theorem tailTrace_7217000 : CollatzResearch.WordTrace tailWord_7217000 prefixEnd_7217000 3705789883498368688009627 := by
  unfold tailWord_7217000
  simp only [CollatzResearch.WordTrace]
  refine ⟨131612807427024520157780227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175483743236032693543706969 131612807427024520157780227)
  ·
    refine ⟨197419211140536780236670341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131612807427024520157780227 197419211140536780236670341)
    ·
      refine ⟨37016102088850646294375689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 197419211140536780236670341 37016102088850646294375689)
      ·
        refine ⟨27762076566637984720781767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37016102088850646294375689 27762076566637984720781767)
        ·
          refine ⟨41643114849956977081172651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27762076566637984720781767 41643114849956977081172651)
          ·
            refine ⟨62464672274935465621758977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41643114849956977081172651 62464672274935465621758977)
            ·
              refine ⟨46848504206201599216319233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62464672274935465621758977 46848504206201599216319233)
              ·
                refine ⟨35136378154651199412239425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46848504206201599216319233 35136378154651199412239425)
                ·
                  refine ⟨26352283615988399559179569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35136378154651199412239425 26352283615988399559179569)
                  ·
                    refine ⟨19764212711991299669384677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26352283615988399559179569 19764212711991299669384677)
                    ·
                      refine ⟨3705789883498368688009627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19764212711991299669384677 3705789883498368688009627)
                      ·
                        rfl

theorem cell23_7217000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 2, 2, 2, 2, 4].length) (baseStart_7217000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7217000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7217000 prefixEnd_7217000 := by exact prefixLift 7217000
  have htrace : WordTrace (prefixWord ++ tailWord_7217000) baseStart_7217000 baseEnd_7217000 := by
    simpa [prefixWord, tailWord_7217000, baseEnd_7217000] using wordTrace_append hprefix tailTrace_7217000
  have hstable : (prefixWord ++ tailWord_7217000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7217000).length < 2 ^ (prefixWord ++ tailWord_7217000).sum := by decide
  have hdescent : baseEnd_7217000 < baseStart_7217000 := by decide
  rcases family_descends (prefixWord ++ tailWord_7217000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7217004 : List Nat := [2, 2, 1, 1, 4, 2, 1, 4, 2, 2, 2]
def baseStart_7217004 : Nat := 118140960795 + 7217004 * 2 ^ 59
def prefixEnd_7217004 : Nat := 4983230072969 + 3 ^ 40 * 7217004 * 2
def baseEnd_7217004 : Nat := 3705791937420986672359609

theorem tailTrace_7217004 : CollatzResearch.WordTrace tailWord_7217004 prefixEnd_7217004 3705791937420986672359609 := by
  unfold tailWord_7217004
  simp only [CollatzResearch.WordTrace]
  refine ⟨131612880373017274499353033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175483840497356365999137377 131612880373017274499353033)
  ·
    refine ⟨98709660279762955874514775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131612880373017274499353033 98709660279762955874514775)
    ·
      refine ⟨148064490419644433811772163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98709660279762955874514775 148064490419644433811772163)
      ·
        refine ⟨222096735629466650717658245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148064490419644433811772163 222096735629466650717658245)
        ·
          refine ⟨41643137930524997009560921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 222096735629466650717658245 41643137930524997009560921)
          ·
            refine ⟨31232353447893747757170691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41643137930524997009560921 31232353447893747757170691)
            ·
              refine ⟨46848530171840621635756037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31232353447893747757170691 46848530171840621635756037)
              ·
                refine ⟨8784099407220116556704257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46848530171840621635756037 8784099407220116556704257)
                ·
                  refine ⟨6588074555415087417528193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8784099407220116556704257 6588074555415087417528193)
                  ·
                    refine ⟨4941055916561315563146145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6588074555415087417528193 4941055916561315563146145)
                    ·
                      refine ⟨3705791937420986672359609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4941055916561315563146145 3705791937420986672359609)
                      ·
                        rfl

theorem cell23_7217004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 2, 2, 2].length) (baseStart_7217004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7217004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7217004 prefixEnd_7217004 := by exact prefixLift 7217004
  have htrace : WordTrace (prefixWord ++ tailWord_7217004) baseStart_7217004 baseEnd_7217004 := by
    simpa [prefixWord, tailWord_7217004, baseEnd_7217004] using wordTrace_append hprefix tailTrace_7217004
  have hstable : (prefixWord ++ tailWord_7217004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7217004).length < 2 ^ (prefixWord ++ tailWord_7217004).sum := by decide
  have hdescent : baseEnd_7217004 < baseStart_7217004 := by decide
  rcases family_descends (prefixWord ++ tailWord_7217004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7217023 : List Nat := [1, 1, 2, 2, 1, 1, 3, 4, 1, 7]
def baseStart_7217023 : Nat := 118140960795 + 7217023 * 2 ^ 59
def prefixEnd_7217023 : Nat := 4983230072969 + 3 ^ 40 * 7217023 * 2
def baseEnd_7217023 : Nat := 1235267231184474032674007

theorem tailTrace_7217023 : CollatzResearch.WordTrace tailWord_7217023 prefixEnd_7217023 1235267231184474032674007 := by
  unfold tailWord_7217023
  simp only [CollatzResearch.WordTrace]
  refine ⟨263226453732965715243647723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175484302488643810162431815 263226453732965715243647723)
  ·
    refine ⟨394839680599448572865471585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263226453732965715243647723 394839680599448572865471585)
    ·
      refine ⟨296129760449586429649103689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 394839680599448572865471585 296129760449586429649103689)
      ·
        refine ⟨222097320337189822236827767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 296129760449586429649103689 222097320337189822236827767)
        ·
          refine ⟨333145980505784733355241651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 222097320337189822236827767 333145980505784733355241651)
          ·
            refine ⟨499718970758677100032862477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 333145980505784733355241651 499718970758677100032862477)
            ·
              refine ⟨187394614034503912512323429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 499718970758677100032862477 187394614034503912512323429)
              ·
                refine ⟨35136490131469483596060643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 187394614034503912512323429 35136490131469483596060643)
                ·
                  refine ⟨52704735197204225394090965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35136490131469483596060643 52704735197204225394090965)
                  ·
                    refine ⟨1235267231184474032674007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 52704735197204225394090965 1235267231184474032674007)
                    ·
                      rfl

theorem cell23_7217023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 4, 1, 7].length) (baseStart_7217023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7217023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7217023 prefixEnd_7217023 := by exact prefixLift 7217023
  have htrace : WordTrace (prefixWord ++ tailWord_7217023) baseStart_7217023 baseEnd_7217023 := by
    simpa [prefixWord, tailWord_7217023, baseEnd_7217023] using wordTrace_append hprefix tailTrace_7217023
  have hstable : (prefixWord ++ tailWord_7217023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7217023).length < 2 ^ (prefixWord ++ tailWord_7217023).sum := by decide
  have hdescent : baseEnd_7217023 < baseStart_7217023 := by decide
  rcases family_descends (prefixWord ++ tailWord_7217023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7217044 : List Nat := [2, 4, 2, 1, 1, 3, 2, 3, 5]
def baseStart_7217044 : Nat := 118140960795 + 7217044 * 2 ^ 59
def prefixEnd_7217044 : Nat := 4983230072969 + 3 ^ 40 * 7217044 * 2
def baseEnd_7217044 : Nat := 411756941849685168428825

theorem tailTrace_7217044 : CollatzResearch.WordTrace tailWord_7217044 prefixEnd_7217044 411756941849685168428825 := by
  unfold tailWord_7217044
  simp only [CollatzResearch.WordTrace]
  refine ⟨131613609832944817915081093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175484813110593090553441457 131613609832944817915081093)
  ·
    refine ⟨24677551843677153359077705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 131613609832944817915081093 24677551843677153359077705)
    ·
      refine ⟨18508163882757865019308279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24677551843677153359077705 18508163882757865019308279)
      ·
        refine ⟨27762245824136797528962419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18508163882757865019308279 27762245824136797528962419)
        ·
          refine ⟨41643368736205196293443629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27762245824136797528962419 41643368736205196293443629)
          ·
            refine ⟨15616263276076948610041361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41643368736205196293443629 15616263276076948610041361)
            ·
              refine ⟨11712197457057711457531021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15616263276076948610041361 11712197457057711457531021)
              ·
                refine ⟨4392074046396641796574133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11712197457057711457531021 4392074046396641796574133)
                ·
                  refine ⟨411756941849685168428825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4392074046396641796574133 411756941849685168428825)
                  ·
                    rfl

theorem cell23_7217044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 2, 3, 5].length) (baseStart_7217044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7217044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7217044 prefixEnd_7217044 := by exact prefixLift 7217044
  have htrace : WordTrace (prefixWord ++ tailWord_7217044) baseStart_7217044 baseEnd_7217044 := by
    simpa [prefixWord, tailWord_7217044, baseEnd_7217044] using wordTrace_append hprefix tailTrace_7217044
  have hstable : (prefixWord ++ tailWord_7217044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7217044).length < 2 ^ (prefixWord ++ tailWord_7217044).sum := by decide
  have hdescent : baseEnd_7217044 < baseStart_7217044 := by decide
  rcases family_descends (prefixWord ++ tailWord_7217044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7217080 : List Nat := [2, 1, 2, 1, 2, 3, 1, 1, 3, 4, 3]
def baseStart_7217080 : Nat := 118140960795 + 7217080 * 2 ^ 59
def prefixEnd_7217080 : Nat := 4983230072969 + 3 ^ 40 * 7217080 * 2
def baseEnd_7217080 : Nat := 3705830961950728375009259

theorem tailTrace_7217080 : CollatzResearch.WordTrace tailWord_7217080 prefixEnd_7217080 3705830961950728375009259 := by
  unfold tailWord_7217080
  simp only [CollatzResearch.WordTrace]
  refine ⟨131614266346879606989236347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175485688462506142652315129 131614266346879606989236347)
  ·
    refine ⟨197421399520319410483854521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131614266346879606989236347 197421399520319410483854521)
    ·
      refine ⟨148066049640239557862890891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 197421399520319410483854521 148066049640239557862890891)
      ·
        refine ⟨222099074460359336794336337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148066049640239557862890891 222099074460359336794336337)
        ·
          refine ⟨166574305845269502595752253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 222099074460359336794336337 166574305845269502595752253)
          ·
            refine ⟨62465364691976063473407095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 166574305845269502595752253 62465364691976063473407095)
            ·
              refine ⟨93698047037964095210110643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62465364691976063473407095 93698047037964095210110643)
              ·
                refine ⟨140547070556946142815165965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 93698047037964095210110643 140547070556946142815165965)
                ·
                  refine ⟨52705151458854803555687237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 140547070556946142815165965 52705151458854803555687237)
                  ·
                    refine ⟨9882215898535275666691357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 52705151458854803555687237 9882215898535275666691357)
                    ·
                      refine ⟨3705830961950728375009259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9882215898535275666691357 3705830961950728375009259)
                      ·
                        rfl

theorem cell23_7217080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 1, 3, 4, 3].length) (baseStart_7217080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7217080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7217080 prefixEnd_7217080 := by exact prefixLift 7217080
  have htrace : WordTrace (prefixWord ++ tailWord_7217080) baseStart_7217080 baseEnd_7217080 := by
    simpa [prefixWord, tailWord_7217080, baseEnd_7217080] using wordTrace_append hprefix tailTrace_7217080
  have hstable : (prefixWord ++ tailWord_7217080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7217080).length < 2 ^ (prefixWord ++ tailWord_7217080).sum := by decide
  have hdescent : baseEnd_7217080 < baseStart_7217080 := by decide
  rcases family_descends (prefixWord ++ tailWord_7217080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7217083 : List Nat := [1, 1, 1, 1, 1, 2, 2, 4, 10]
def baseStart_7217083 : Nat := 118140960795 + 7217083 * 2 ^ 59
def prefixEnd_7217083 : Nat := 4983230072969 + 3 ^ 40 * 7217083 * 2
def baseEnd_7217083 : Nat := 411759166932521318141305

theorem tailTrace_7217083 : CollatzResearch.WordTrace tailWord_7217083 prefixEnd_7217083 411759166932521318141305 := by
  unfold tailWord_7217083
  simp only [CollatzResearch.WordTrace]
  refine ⟨263228642112748345490831903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175485761408498896993887935 263228642112748345490831903)
  ·
    refine ⟨394842963169122518236247855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263228642112748345490831903 394842963169122518236247855)
    ·
      refine ⟨592264444753683777354371783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 394842963169122518236247855 592264444753683777354371783)
      ·
        refine ⟨888396667130525666031557675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 592264444753683777354371783 888396667130525666031557675)
        ·
          refine ⟨1332595000695788499047336513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 888396667130525666031557675 1332595000695788499047336513)
          ·
            refine ⟨999446250521841374285502385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1332595000695788499047336513 999446250521841374285502385)
            ·
              refine ⟨749584687891381030714126789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 999446250521841374285502385 749584687891381030714126789)
              ·
                refine ⟨140547128979633943258898773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 749584687891381030714126789 140547128979633943258898773)
                ·
                  refine ⟨411759166932521318141305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 140547128979633943258898773 411759166932521318141305)
                  ·
                    rfl

theorem cell23_7217083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 4, 10].length) (baseStart_7217083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7217083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7217083 prefixEnd_7217083 := by exact prefixLift 7217083
  have htrace : WordTrace (prefixWord ++ tailWord_7217083) baseStart_7217083 baseEnd_7217083 := by
    simpa [prefixWord, tailWord_7217083, baseEnd_7217083] using wordTrace_append hprefix tailTrace_7217083
  have hstable : (prefixWord ++ tailWord_7217083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7217083).length < 2 ^ (prefixWord ++ tailWord_7217083).sum := by decide
  have hdescent : baseEnd_7217083 < baseStart_7217083 := by decide
  rcases family_descends (prefixWord ++ tailWord_7217083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7217100 : List Nat := [2, 2, 1, 4, 1, 2, 1, 2, 8]
def baseStart_7217100 : Nat := 118140960795 + 7217100 * 2 ^ 59
def prefixEnd_7217100 : Nat := 4983230072969 + 3 ^ 40 * 7217100 * 2
def baseEnd_7217100 : Nat := 411760136840424255195463

theorem tailTrace_7217100 : CollatzResearch.WordTrace tailWord_7217100 prefixEnd_7217100 411760136840424255195463 := by
  unfold tailWord_7217100
  simp only [CollatzResearch.WordTrace]
  refine ⟨131614631076843378697100377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175486174769124504929467169 131614631076843378697100377)
  ·
    refine ⟨98710973307632534022825283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131614631076843378697100377 98710973307632534022825283)
    ·
      refine ⟨148066459961448801034237925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98710973307632534022825283 148066459961448801034237925)
      ·
        refine ⟨27762461242771650193919611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 148066459961448801034237925 27762461242771650193919611)
        ·
          refine ⟨41643691864157475290879417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27762461242771650193919611 41643691864157475290879417)
          ·
            refine ⟨31232768898118106468159563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41643691864157475290879417 31232768898118106468159563)
            ·
              refine ⟨46849153347177159702239345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31232768898118106468159563 46849153347177159702239345)
              ·
                refine ⟨35136865010382869776679509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46849153347177159702239345 35136865010382869776679509)
                ·
                  refine ⟨411760136840424255195463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 35136865010382869776679509 411760136840424255195463)
                  ·
                    rfl

theorem cell23_7217100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 1, 2, 8].length) (baseStart_7217100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7217100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7217100 prefixEnd_7217100 := by exact prefixLift 7217100
  have htrace : WordTrace (prefixWord ++ tailWord_7217100) baseStart_7217100 baseEnd_7217100 := by
    simpa [prefixWord, tailWord_7217100, baseEnd_7217100] using wordTrace_append hprefix tailTrace_7217100
  have hstable : (prefixWord ++ tailWord_7217100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7217100).length < 2 ^ (prefixWord ++ tailWord_7217100).sum := by decide
  have hdescent : baseEnd_7217100 < baseStart_7217100 := by decide
  rcases family_descends (prefixWord ++ tailWord_7217100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7217104 : List Nat := [2, 1, 1, 1, 1, 2, 7, 3, 1, 4]
def baseStart_7217104 : Nat := 118140960795 + 7217104 * 2 ^ 59
def prefixEnd_7217104 : Nat := 4983230072969 + 3 ^ 40 * 7217104 * 2
def baseEnd_7217104 : Nat := 1235281095162145427036383

theorem tailTrace_7217104 : CollatzResearch.WordTrace tailWord_7217104 prefixEnd_7217104 1235281095162145427036383 := by
  unfold tailWord_7217104
  simp only [CollatzResearch.WordTrace]
  refine ⟨131614704022836133038673183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175486272030448177384897577 131614704022836133038673183)
  ·
    refine ⟨197422056034254199558009775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131614704022836133038673183 197422056034254199558009775)
    ·
      refine ⟨296133084051381299337014663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197422056034254199558009775 296133084051381299337014663)
      ·
        refine ⟨444199626077071949005521995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 296133084051381299337014663 444199626077071949005521995)
        ·
          refine ⟨666299439115607923508282993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 444199626077071949005521995 666299439115607923508282993)
          ·
            refine ⟨499724579336705942631212245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 666299439115607923508282993 499724579336705942631212245)
            ·
              refine ⟨11712294828204045530419037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 499724579336705942631212245 11712294828204045530419037)
              ·
                refine ⟨4392110560576517073907139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11712294828204045530419037 4392110560576517073907139)
                ·
                  refine ⟨6588165840864775610860709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4392110560576517073907139 6588165840864775610860709)
                  ·
                    refine ⟨1235281095162145427036383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6588165840864775610860709 1235281095162145427036383)
                    ·
                      rfl

theorem cell23_7217104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 7, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 7, 3, 1, 4].length) (baseStart_7217104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7217104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7217104 prefixEnd_7217104 := by exact prefixLift 7217104
  have htrace : WordTrace (prefixWord ++ tailWord_7217104) baseStart_7217104 baseEnd_7217104 := by
    simpa [prefixWord, tailWord_7217104, baseEnd_7217104] using wordTrace_append hprefix tailTrace_7217104
  have hstable : (prefixWord ++ tailWord_7217104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7217104).length < 2 ^ (prefixWord ++ tailWord_7217104).sum := by decide
  have hdescent : baseEnd_7217104 < baseStart_7217104 := by decide
  rcases family_descends (prefixWord ++ tailWord_7217104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7217114 : List Nat := [3, 1, 1, 2, 5, 1, 1, 2, 2, 2, 3]
def baseStart_7217114 : Nat := 118140960795 + 7217114 * 2 ^ 59
def prefixEnd_7217114 : Nat := 4983230072969 + 3 ^ 40 * 7217114 * 2
def baseEnd_7217114 : Nat := 3705848420292981241984103

theorem tailTrace_7217114 : CollatzResearch.WordTrace tailWord_7217114 prefixEnd_7217114 3705848420292981241984103 := by
  unfold tailWord_7217114
  simp only [CollatzResearch.WordTrace]
  refine ⟨65807443193909009446302599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175486515183757358523473597 65807443193909009446302599)
  ·
    refine ⟨98711164790863514169453899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65807443193909009446302599 98711164790863514169453899)
    ·
      refine ⟨148066747186295271254180849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98711164790863514169453899 148066747186295271254180849)
      ·
        refine ⟨111050060389721453440635637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148066747186295271254180849 111050060389721453440635637)
        ·
          refine ⟨10410943161536386260059591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 111050060389721453440635637 10410943161536386260059591)
          ·
            refine ⟨15616414742304579390089387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10410943161536386260059591 15616414742304579390089387)
            ·
              refine ⟨23424622113456869085134081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15616414742304579390089387 23424622113456869085134081)
              ·
                refine ⟨17568466585092651813850561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23424622113456869085134081 17568466585092651813850561)
                ·
                  refine ⟨13176349938819488860387921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17568466585092651813850561 13176349938819488860387921)
                  ·
                    refine ⟨9882262454114616645290941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13176349938819488860387921 9882262454114616645290941)
                    ·
                      refine ⟨3705848420292981241984103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9882262454114616645290941 3705848420292981241984103)
                      ·
                        rfl

theorem cell23_7217114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 1, 2, 2, 2, 3].length) (baseStart_7217114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7217114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7217114 prefixEnd_7217114 := by exact prefixLift 7217114
  have htrace : WordTrace (prefixWord ++ tailWord_7217114) baseStart_7217114 baseEnd_7217114 := by
    simpa [prefixWord, tailWord_7217114, baseEnd_7217114] using wordTrace_append hprefix tailTrace_7217114
  have hstable : (prefixWord ++ tailWord_7217114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7217114).length < 2 ^ (prefixWord ++ tailWord_7217114).sum := by decide
  have hdescent : baseEnd_7217114 < baseStart_7217114 := by decide
  rcases family_descends (prefixWord ++ tailWord_7217114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7217134 : List Nat := [4, 1, 2, 1, 3, 1, 4, 1, 6]
def baseStart_7217134 : Nat := 118140960795 + 7217134 * 2 ^ 59
def prefixEnd_7217134 : Nat := 4983230072969 + 3 ^ 40 * 7217134 * 2
def baseEnd_7217134 : Nat := 411762076656230129303779

theorem tailTrace_7217134 : CollatzResearch.WordTrace tailWord_7217134 prefixEnd_7217134 411762076656230129303779 := by
  unfold tailWord_7217134
  simp only [CollatzResearch.WordTrace]
  refine ⟨32903812779445447650117307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 175487001490375720800625637 32903812779445447650117307)
  ·
    refine ⟨49355719169168171475175961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32903812779445447650117307 49355719169168171475175961)
    ·
      refine ⟨37016789376876128606381971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49355719169168171475175961 37016789376876128606381971)
      ·
        refine ⟨55525184065314192909572957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37016789376876128606381971 55525184065314192909572957)
        ·
          refine ⟨20821944024492822341089859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55525184065314192909572957 20821944024492822341089859)
          ·
            refine ⟨31232916036739233511634789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20821944024492822341089859 31232916036739233511634789)
            ·
              refine ⟨5856171756888606283431523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31232916036739233511634789 5856171756888606283431523)
              ·
                refine ⟨8784257635332909425147285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5856171756888606283431523 8784257635332909425147285)
                ·
                  refine ⟨411762076656230129303779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8784257635332909425147285 411762076656230129303779)
                  ·
                    rfl

theorem cell23_7217134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 4, 1, 6].length) (baseStart_7217134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7217134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7217134 prefixEnd_7217134 := by exact prefixLift 7217134
  have htrace : WordTrace (prefixWord ++ tailWord_7217134) baseStart_7217134 baseEnd_7217134 := by
    simpa [prefixWord, tailWord_7217134, baseEnd_7217134] using wordTrace_append hprefix tailTrace_7217134
  have hstable : (prefixWord ++ tailWord_7217134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7217134).length < 2 ^ (prefixWord ++ tailWord_7217134).sum := by decide
  have hdescent : baseEnd_7217134 < baseStart_7217134 := by decide
  rcases family_descends (prefixWord ++ tailWord_7217134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7217147 : List Nat := [1, 1, 1, 1, 1, 3, 7, 2, 1, 5]
def baseStart_7217147 : Nat := 118140960795 + 7217147 * 2 ^ 59
def prefixEnd_7217147 : Nat := 4983230072969 + 3 ^ 40 * 7217147 * 2
def baseEnd_7217147 : Nat := 1235288455051526537623817

theorem tailTrace_7217147 : CollatzResearch.WordTrace tailWord_7217147 prefixEnd_7217147 1235288455051526537623817 := by
  unfold tailWord_7217147
  simp only [CollatzResearch.WordTrace]
  refine ⟨263230976384516484421161695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175487317589677656280774463 263230976384516484421161695)
  ·
    refine ⟨394846464576774726631742543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263230976384516484421161695 394846464576774726631742543)
    ·
      refine ⟨592269696865162089947613815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 394846464576774726631742543 592269696865162089947613815)
      ·
        refine ⟨888404545297743134921420723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 592269696865162089947613815 888404545297743134921420723)
        ·
          refine ⟨1332606817946614702382131085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 888404545297743134921420723 1332606817946614702382131085)
          ·
            refine ⟨499727556729980513393299157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1332606817946614702382131085 499727556729980513393299157)
            ·
              refine ⟨11712364610858918282655449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 499727556729980513393299157 11712364610858918282655449)
              ·
                refine ⟨8784273458144188711991587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11712364610858918282655449 8784273458144188711991587)
                ·
                  refine ⟨13176410187216283067987381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8784273458144188711991587 13176410187216283067987381)
                  ·
                    refine ⟨1235288455051526537623817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13176410187216283067987381 1235288455051526537623817)
                    ·
                      rfl

theorem cell23_7217147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 7, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 7, 2, 1, 5].length) (baseStart_7217147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7217147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7217147 prefixEnd_7217147 := by exact prefixLift 7217147
  have htrace : WordTrace (prefixWord ++ tailWord_7217147) baseStart_7217147 baseEnd_7217147 := by
    simpa [prefixWord, tailWord_7217147, baseEnd_7217147] using wordTrace_append hprefix tailTrace_7217147
  have hstable : (prefixWord ++ tailWord_7217147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7217147).length < 2 ^ (prefixWord ++ tailWord_7217147).sum := by decide
  have hdescent : baseEnd_7217147 < baseStart_7217147 := by decide
  rcases family_descends (prefixWord ++ tailWord_7217147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7217164 : List Nat := [2, 2, 1, 2, 3, 1, 5, 1, 1, 5]
def baseStart_7217164 : Nat := 118140960795 + 7217164 * 2 ^ 59
def prefixEnd_7217164 : Nat := 4983230072969 + 3 ^ 40 * 7217164 * 2
def baseEnd_7217164 : Nat := 1235291364775235348786291

theorem tailTrace_7217164 : CollatzResearch.WordTrace tailWord_7217164 prefixEnd_7217164 1235291364775235348786291 := by
  unfold tailWord_7217164
  simp only [CollatzResearch.WordTrace]
  refine ⟨131615798212727448162265273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175487730950303264216353697 131615798212727448162265273)
  ·
    refine ⟨98711848659545586121698955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131615798212727448162265273 98711848659545586121698955)
    ·
      refine ⟨148067772989318379182548433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98711848659545586121698955 148067772989318379182548433)
      ·
        refine ⟨111050829741988784386911325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148067772989318379182548433 111050829741988784386911325)
        ·
          refine ⟨41644061153245794145091747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 111050829741988784386911325 41644061153245794145091747)
          ·
            refine ⟨62466091729868691217637621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41644061153245794145091747 62466091729868691217637621)
            ·
              refine ⟨5856196099675189801653527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 62466091729868691217637621 5856196099675189801653527)
              ·
                refine ⟨8784294149512784702480291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5856196099675189801653527 8784294149512784702480291)
                ·
                  refine ⟨13176441224269177053720437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8784294149512784702480291 13176441224269177053720437)
                  ·
                    refine ⟨1235291364775235348786291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13176441224269177053720437 1235291364775235348786291)
                    ·
                      rfl

theorem cell23_7217164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 5, 1, 1, 5].length) (baseStart_7217164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7217164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7217164 prefixEnd_7217164 := by exact prefixLift 7217164
  have htrace : WordTrace (prefixWord ++ tailWord_7217164) baseStart_7217164 baseEnd_7217164 := by
    simpa [prefixWord, tailWord_7217164, baseEnd_7217164] using wordTrace_append hprefix tailTrace_7217164
  have hstable : (prefixWord ++ tailWord_7217164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7217164).length < 2 ^ (prefixWord ++ tailWord_7217164).sum := by decide
  have hdescent : baseEnd_7217164 < baseStart_7217164 := by decide
  rcases family_descends (prefixWord ++ tailWord_7217164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7217172 : List Nat := [2, 4, 3, 2, 1, 2, 2, 2, 1, 4]
def baseStart_7217172 : Nat := 118140960795 + 7217172 * 2 ^ 59
def prefixEnd_7217172 : Nat := 4983230072969 + 3 ^ 40 * 7217172 * 2
def baseEnd_7217172 : Nat := 1235292734056980671686279

theorem tailTrace_7217172 : CollatzResearch.WordTrace tailWord_7217172 prefixEnd_7217172 1235292734056980671686279 := by
  unfold tailWord_7217172
  simp only [CollatzResearch.WordTrace]
  refine ⟨131615944104712956845410885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175487925472950609127214513 131615944104712956845410885)
  ·
    refine ⟨24677989519633679408514541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 131615944104712956845410885 24677989519633679408514541)
    ·
      refine ⟨9254246069862629778192953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24677989519633679408514541 9254246069862629778192953)
      ·
        refine ⟨6940684552396972333644715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9254246069862629778192953 6940684552396972333644715)
        ·
          refine ⟨10411026828595458500467073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6940684552396972333644715 10411026828595458500467073)
          ·
            refine ⟨7808270121446593875350305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10411026828595458500467073 7808270121446593875350305)
            ·
              refine ⟨5856202591084945406512729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7808270121446593875350305 5856202591084945406512729)
              ·
                refine ⟨4392151943313709054884547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5856202591084945406512729 4392151943313709054884547)
                ·
                  refine ⟨6588227914970563582326821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4392151943313709054884547 6588227914970563582326821)
                  ·
                    refine ⟨1235292734056980671686279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6588227914970563582326821 1235292734056980671686279)
                    ·
                      rfl

theorem cell23_7217172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 2, 2, 2, 1, 4].length) (baseStart_7217172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7217172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7217172 prefixEnd_7217172 := by exact prefixLift 7217172
  have htrace : WordTrace (prefixWord ++ tailWord_7217172) baseStart_7217172 baseEnd_7217172 := by
    simpa [prefixWord, tailWord_7217172, baseEnd_7217172] using wordTrace_append hprefix tailTrace_7217172
  have hstable : (prefixWord ++ tailWord_7217172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7217172).length < 2 ^ (prefixWord ++ tailWord_7217172).sum := by decide
  have hdescent : baseEnd_7217172 < baseStart_7217172 := by decide
  rcases family_descends (prefixWord ++ tailWord_7217172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7217178 : List Nat := [3, 1, 1, 3, 1, 3, 4, 2, 1, 1, 3]
def baseStart_7217178 : Nat := 118140960795 + 7217178 * 2 ^ 59
def prefixEnd_7217178 : Nat := 4983230072969 + 3 ^ 40 * 7217178 * 2
def baseEnd_7217178 : Nat := 3705881283054868991583809

theorem tailTrace_7217178 : CollatzResearch.WordTrace tailWord_7217178 prefixEnd_7217178 3705881283054868991583809 := by
  unfold tailWord_7217178
  simp only [CollatzResearch.WordTrace]
  refine ⟨65808026761851044178885047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175488071364936117810360125 65808026761851044178885047)
  ·
    refine ⟨98712040142776566268327571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65808026761851044178885047 98712040142776566268327571)
    ·
      refine ⟨148068060214164849402491357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98712040142776566268327571 148068060214164849402491357)
      ·
        refine ⟨55525522580311818525934259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 148068060214164849402491357 55525522580311818525934259)
        ·
          refine ⟨83288283870467727788901389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55525522580311818525934259 83288283870467727788901389)
          ·
            refine ⟨31233106451425397920838021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 83288283870467727788901389 31233106451425397920838021)
            ·
              refine ⟨5856207459642262110157129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31233106451425397920838021 5856207459642262110157129)
              ·
                refine ⟨4392155594731696582617847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5856207459642262110157129 4392155594731696582617847)
                ·
                  refine ⟨6588233392097544873926771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4392155594731696582617847 6588233392097544873926771)
                  ·
                    refine ⟨9882350088146317310890157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6588233392097544873926771 9882350088146317310890157)
                    ·
                      refine ⟨3705881283054868991583809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9882350088146317310890157 3705881283054868991583809)
                      ·
                        rfl

theorem cell23_7217178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 4, 2, 1, 1, 3].length) (baseStart_7217178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7217178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7217178 prefixEnd_7217178 := by exact prefixLift 7217178
  have htrace : WordTrace (prefixWord ++ tailWord_7217178) baseStart_7217178 baseEnd_7217178 := by
    simpa [prefixWord, tailWord_7217178, baseEnd_7217178] using wordTrace_append hprefix tailTrace_7217178
  have hstable : (prefixWord ++ tailWord_7217178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7217178).length < 2 ^ (prefixWord ++ tailWord_7217178).sum := by decide
  have hdescent : baseEnd_7217178 < baseStart_7217178 := by decide
  rcases family_descends (prefixWord ++ tailWord_7217178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7217187 : List Nat := [1, 1, 1, 4, 3, 1, 1, 1, 5, 2, 3]
def baseStart_7217187 : Nat := 118140960795 + 7217187 * 2 ^ 59
def prefixEnd_7217187 : Nat := 4983230072969 + 3 ^ 40 * 7217187 * 2
def baseEnd_7217187 : Nat := 3705885904380759456371267

theorem tailTrace_7217187 : CollatzResearch.WordTrace tailWord_7217187 prefixEnd_7217187 3705885904380759456371267 := by
  unfold tailWord_7217187
  simp only [CollatzResearch.WordTrace]
  refine ⟨263232435304371571252617815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175488290202914380835078543 263232435304371571252617815)
  ·
    refine ⟨394848652956557356878926723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263232435304371571252617815 394848652956557356878926723)
    ·
      refine ⟨592272979434836035318390085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 394848652956557356878926723 592272979434836035318390085)
      ·
        refine ⟨111051183644031756622198141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 592272979434836035318390085 111051183644031756622198141)
        ·
          refine ⟨41644193866511908733324303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 111051183644031756622198141 41644193866511908733324303)
          ·
            refine ⟨62466290799767863099986455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41644193866511908733324303 62466290799767863099986455)
            ·
              refine ⟨93699436199651794649979683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62466290799767863099986455 93699436199651794649979683)
              ·
                refine ⟨140549154299477691974969525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 93699436199651794649979683 140549154299477691974969525)
                ·
                  refine ⟨13176483215576033622653393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 140549154299477691974969525 13176483215576033622653393)
                  ·
                    refine ⟨9882362411682025216990045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13176483215576033622653393 9882362411682025216990045)
                    ·
                      refine ⟨3705885904380759456371267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9882362411682025216990045 3705885904380759456371267)
                      ·
                        rfl

theorem cell23_7217187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 1, 5, 2, 3].length) (baseStart_7217187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7217187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7217187 prefixEnd_7217187 := by exact prefixLift 7217187
  have htrace : WordTrace (prefixWord ++ tailWord_7217187) baseStart_7217187 baseEnd_7217187 := by
    simpa [prefixWord, tailWord_7217187, baseEnd_7217187] using wordTrace_append hprefix tailTrace_7217187
  have hstable : (prefixWord ++ tailWord_7217187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7217187).length < 2 ^ (prefixWord ++ tailWord_7217187).sum := by decide
  have hdescent : baseEnd_7217187 < baseStart_7217187 := by decide
  rcases family_descends (prefixWord ++ tailWord_7217187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7217194 : List Nat := [3, 1, 4, 1, 2, 2, 2, 1, 1, 6]
def baseStart_7217194 : Nat := 118140960795 + 7217194 * 2 ^ 59
def prefixEnd_7217194 : Nat := 4983230072969 + 3 ^ 40 * 7217194 * 2
def baseEnd_7217194 : Nat := 1235296499581780309661245

theorem tailTrace_7217194 : CollatzResearch.WordTrace tailWord_7217194 prefixEnd_7217194 1235296499581780309661245 := by
  unfold tailWord_7217194
  simp only [CollatzResearch.WordTrace]
  refine ⟨65808172653836552862030659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175488460410230807632081757 65808172653836552862030659)
  ·
    refine ⟨98712258980754829293045989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65808172653836552862030659 98712258980754829293045989)
    ·
      refine ⟨18508548558891530492446123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 98712258980754829293045989 18508548558891530492446123)
      ·
        refine ⟨27762822838337295738669185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18508548558891530492446123 27762822838337295738669185)
        ·
          refine ⟨20822117128752971804001889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27762822838337295738669185 20822117128752971804001889)
          ·
            refine ⟨15616587846564728853001417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20822117128752971804001889 15616587846564728853001417)
            ·
              refine ⟨11712440884923546639751063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15616587846564728853001417 11712440884923546639751063)
              ·
                refine ⟨17568661327385319959626595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11712440884923546639751063 17568661327385319959626595)
                ·
                  refine ⟨26352991991077979939439893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17568661327385319959626595 26352991991077979939439893)
                  ·
                    refine ⟨1235296499581780309661245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26352991991077979939439893 1235296499581780309661245)
                    ·
                      rfl

theorem cell23_7217194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 2, 1, 1, 6].length) (baseStart_7217194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7217194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7217194 prefixEnd_7217194 := by exact prefixLift 7217194
  have htrace : WordTrace (prefixWord ++ tailWord_7217194) baseStart_7217194 baseEnd_7217194 := by
    simpa [prefixWord, tailWord_7217194, baseEnd_7217194] using wordTrace_append hprefix tailTrace_7217194
  have hstable : (prefixWord ++ tailWord_7217194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7217194).length < 2 ^ (prefixWord ++ tailWord_7217194).sum := by decide
  have hdescent : baseEnd_7217194 < baseStart_7217194 := by decide
  rcases family_descends (prefixWord ++ tailWord_7217194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7217201 : List Nat := [1, 2, 2, 3, 1, 4, 1, 2, 3, 2, 2]
def baseStart_7217201 : Nat := 118140960795 + 7217201 * 2 ^ 59
def prefixEnd_7217201 : Nat := 4983230072969 + 3 ^ 40 * 7217201 * 2
def baseEnd_7217201 : Nat := 3705893093109922401596203

theorem tailTrace_7217201 : CollatzResearch.WordTrace tailWord_7217201 prefixEnd_7217201 3705893093109922401596203 := by
  unfold tailWord_7217201
  simp only [CollatzResearch.WordTrace]
  refine ⟨263232945926320851643627457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175488630617547234429084971 263232945926320851643627457)
  ·
    refine ⟨197424709444740638732720593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 263232945926320851643627457 197424709444740638732720593)
    ·
      refine ⟨148068532083555479049540445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 197424709444740638732720593 148068532083555479049540445)
      ·
        refine ⟨55525699531333304643577667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 148068532083555479049540445 55525699531333304643577667)
        ·
          refine ⟨83288549296999956965366501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55525699531333304643577667 83288549296999956965366501)
          ·
            refine ⟨15616602993187491931006219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 83288549296999956965366501 15616602993187491931006219)
            ·
              refine ⟨23424904489781237896509329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15616602993187491931006219 23424904489781237896509329)
              ·
                refine ⟨17568678367335928422381997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23424904489781237896509329 17568678367335928422381997)
                ·
                  refine ⟨6588254387750973158393249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17568678367335928422381997 6588254387750973158393249)
                  ·
                    refine ⟨4941190790813229868794937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6588254387750973158393249 4941190790813229868794937)
                    ·
                      refine ⟨3705893093109922401596203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4941190790813229868794937 3705893093109922401596203)
                      ·
                        rfl

theorem cell23_7217201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 1, 2, 3, 2, 2].length) (baseStart_7217201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7217201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7217201 prefixEnd_7217201 := by exact prefixLift 7217201
  have htrace : WordTrace (prefixWord ++ tailWord_7217201) baseStart_7217201 baseEnd_7217201 := by
    simpa [prefixWord, tailWord_7217201, baseEnd_7217201] using wordTrace_append hprefix tailTrace_7217201
  have hstable : (prefixWord ++ tailWord_7217201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7217201).length < 2 ^ (prefixWord ++ tailWord_7217201).sum := by decide
  have hdescent : baseEnd_7217201 < baseStart_7217201 := by decide
  rcases family_descends (prefixWord ++ tailWord_7217201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7217277 : List Nat := [1, 4, 1, 1, 3, 2, 1, 1, 1, 3, 5]
def baseStart_7217277 : Nat := 118140960795 + 7217277 * 2 ^ 59
def prefixEnd_7217277 : Nat := 4983230072969 + 3 ^ 40 * 7217277 * 2
def baseEnd_7217277 : Nat := 3705932117639664104245853

theorem tailTrace_7217277 : CollatzResearch.WordTrace tailWord_7217277 prefixEnd_7217277 3705932117639664104245853 := by
  unfold tailWord_7217277
  simp only [CollatzResearch.WordTrace]
  refine ⟨263235717874045516623394085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175490478582697011082262723 263235717874045516623394085)
  ·
    refine ⟨49356697101383534366886391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 263235717874045516623394085 49356697101383534366886391)
    ·
      refine ⟨74035045652075301550329587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49356697101383534366886391 74035045652075301550329587)
      ·
        refine ⟨111052568478112952325494381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74035045652075301550329587 111052568478112952325494381)
        ·
          refine ⟨41644713179292357122060393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 111052568478112952325494381 41644713179292357122060393)
          ·
            refine ⟨31233534884469267841545295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41644713179292357122060393 31233534884469267841545295)
            ·
              refine ⟨46850302326703901762317943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31233534884469267841545295 46850302326703901762317943)
              ·
                refine ⟨70275453490055852643476915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46850302326703901762317943 70275453490055852643476915)
                ·
                  refine ⟨105413180235083778965215373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70275453490055852643476915 105413180235083778965215373)
                  ·
                    refine ⟨39529942588156417111955765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 105413180235083778965215373 39529942588156417111955765)
                    ·
                      refine ⟨3705932117639664104245853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39529942588156417111955765 3705932117639664104245853)
                      ·
                        rfl

theorem cell23_7217277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 1, 1, 1, 3, 5].length) (baseStart_7217277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7217277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7217277 prefixEnd_7217277 := by exact prefixLift 7217277
  have htrace : WordTrace (prefixWord ++ tailWord_7217277) baseStart_7217277 baseEnd_7217277 := by
    simpa [prefixWord, tailWord_7217277, baseEnd_7217277] using wordTrace_append hprefix tailTrace_7217277
  have hstable : (prefixWord ++ tailWord_7217277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7217277).length < 2 ^ (prefixWord ++ tailWord_7217277).sum := by decide
  have hdescent : baseEnd_7217277 < baseStart_7217277 := by decide
  rcases family_descends (prefixWord ++ tailWord_7217277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7217287 : List Nat := [1, 1, 4, 2, 1, 1, 2, 1, 4, 2, 4]
def baseStart_7217287 : Nat := 118140960795 + 7217287 * 2 ^ 59
def prefixEnd_7217287 : Nat := 4983230072969 + 3 ^ 40 * 7217287 * 2
def baseEnd_7217287 : Nat := 3705937252446209065120807

theorem tailTrace_7217287 : CollatzResearch.WordTrace tailWord_7217287 prefixEnd_7217287 3705937252446209065120807 := by
  unfold tailWord_7217287
  simp only [CollatzResearch.WordTrace]
  refine ⟨263236082604009288331258115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175490721736006192220838743 263236082604009288331258115)
  ·
    refine ⟨394854123906013932496887173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263236082604009288331258115 394854123906013932496887173)
    ·
      refine ⟨74035148232377612343166345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 394854123906013932496887173 74035148232377612343166345)
      ·
        refine ⟨55526361174283209257374759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74035148232377612343166345 55526361174283209257374759)
        ·
          refine ⟨83289541761424813886062139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55526361174283209257374759 83289541761424813886062139)
          ·
            refine ⟨124934312642137220829093209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83289541761424813886062139 124934312642137220829093209)
            ·
              refine ⟨93700734481602915621819907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 124934312642137220829093209 93700734481602915621819907)
              ·
                refine ⟨140551101722404373432729861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 93700734481602915621819907 140551101722404373432729861)
                ·
                  refine ⟨26353331572950820018636849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 140551101722404373432729861 26353331572950820018636849)
                  ·
                    refine ⟨19764998679713115013977637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26353331572950820018636849 19764998679713115013977637)
                    ·
                      refine ⟨3705937252446209065120807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19764998679713115013977637 3705937252446209065120807)
                      ·
                        rfl

theorem cell23_7217287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 1, 4, 2, 4].length) (baseStart_7217287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7217287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7217287 prefixEnd_7217287 := by exact prefixLift 7217287
  have htrace : WordTrace (prefixWord ++ tailWord_7217287) baseStart_7217287 baseEnd_7217287 := by
    simpa [prefixWord, tailWord_7217287, baseEnd_7217287] using wordTrace_append hprefix tailTrace_7217287
  have hstable : (prefixWord ++ tailWord_7217287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7217287).length < 2 ^ (prefixWord ++ tailWord_7217287).sum := by decide
  have hdescent : baseEnd_7217287 < baseStart_7217287 := by decide
  rcases family_descends (prefixWord ++ tailWord_7217287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7217308 : List Nat := [2, 2, 3, 2, 1, 1, 3, 3, 2, 2, 2]
def baseStart_7217308 : Nat := 118140960795 + 7217308 * 2 ^ 59
def prefixEnd_7217308 : Nat := 4983230072969 + 3 ^ 40 * 7217308 * 2
def baseEnd_7217308 : Nat := 3705948035539953482958211

theorem tailTrace_7217308 : CollatzResearch.WordTrace tailWord_7217308 prefixEnd_7217308 3705948035539953482958211 := by
  unfold tailWord_7217308
  simp only [CollatzResearch.WordTrace]
  refine ⟨131618424268466604458886289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175491232357955472611848385 131618424268466604458886289)
  ·
    refine ⟨98713818201349953344164717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131618424268466604458886289 98713818201349953344164717)
    ·
      refine ⟨37017681825506232504061769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98713818201349953344164717 37017681825506232504061769)
      ·
        refine ⟨27763261369129674378046327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37017681825506232504061769 27763261369129674378046327)
        ·
          refine ⟨41644892053694511567069491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27763261369129674378046327 41644892053694511567069491)
          ·
            refine ⟨62467338080541767350604237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41644892053694511567069491 62467338080541767350604237)
            ·
              refine ⟨23425251780203162756476589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62467338080541767350604237 23425251780203162756476589)
              ·
                refine ⟨8784469417576186033678721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23425251780203162756476589 8784469417576186033678721)
                ·
                  refine ⟨6588352063182139525259041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8784469417576186033678721 6588352063182139525259041)
                  ·
                    refine ⟨4941264047386604643944281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6588352063182139525259041 4941264047386604643944281)
                    ·
                      refine ⟨3705948035539953482958211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4941264047386604643944281 3705948035539953482958211)
                      ·
                        rfl

theorem cell23_7217308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 3, 3, 2, 2, 2].length) (baseStart_7217308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7217308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7217308 prefixEnd_7217308 := by exact prefixLift 7217308
  have htrace : WordTrace (prefixWord ++ tailWord_7217308) baseStart_7217308 baseEnd_7217308 := by
    simpa [prefixWord, tailWord_7217308, baseEnd_7217308] using wordTrace_append hprefix tailTrace_7217308
  have hstable : (prefixWord ++ tailWord_7217308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7217308).length < 2 ^ (prefixWord ++ tailWord_7217308).sum := by decide
  have hdescent : baseEnd_7217308 < baseStart_7217308 := by decide
  rcases family_descends (prefixWord ++ tailWord_7217308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7217337 : List Nat := [1, 2, 1, 4, 1, 2, 1, 1, 3, 2, 5]
def baseStart_7217337 : Nat := 118140960795 + 7217337 * 2 ^ 59
def prefixEnd_7217337 : Nat := 4983230072969 + 3 ^ 40 * 7217337 * 2
def baseEnd_7217337 : Nat := 3705962926478933869495577

theorem tailTrace_7217337 : CollatzResearch.WordTrace tailWord_7217337 prefixEnd_7217337 3705962926478933869495577 := by
  unfold tailWord_7217337
  simp only [CollatzResearch.WordTrace]
  refine ⟨263237906253828146870578265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175491937502552097913718843 263237906253828146870578265)
  ·
    refine ⟨197428429690371110152933699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 263237906253828146870578265 197428429690371110152933699)
    ·
      refine ⟨296142644535556665229400549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197428429690371110152933699 296142644535556665229400549)
      ·
        refine ⟨55526745850416874730512603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 296142644535556665229400549 55526745850416874730512603)
        ·
          refine ⟨83290118775625312095768905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55526745850416874730512603 83290118775625312095768905)
          ·
            refine ⟨62467589081718984071826679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83290118775625312095768905 62467589081718984071826679)
            ·
              refine ⟨93701383622578476107740019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62467589081718984071826679 93701383622578476107740019)
              ·
                refine ⟨140552075433867714161610029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 93701383622578476107740019 140552075433867714161610029)
                ·
                  refine ⟨52707028287700392810603761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 140552075433867714161610029 52707028287700392810603761)
                  ·
                    refine ⟨39530271215775294607952821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 52707028287700392810603761 39530271215775294607952821)
                    ·
                      refine ⟨3705962926478933869495577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39530271215775294607952821 3705962926478933869495577)
                      ·
                        rfl

theorem cell23_7217337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 1, 3, 2, 5].length) (baseStart_7217337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7217337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7217337 prefixEnd_7217337 := by exact prefixLift 7217337
  have htrace : WordTrace (prefixWord ++ tailWord_7217337) baseStart_7217337 baseEnd_7217337 := by
    simpa [prefixWord, tailWord_7217337, baseEnd_7217337] using wordTrace_append hprefix tailTrace_7217337
  have hstable : (prefixWord ++ tailWord_7217337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7217337).length < 2 ^ (prefixWord ++ tailWord_7217337).sum := by decide
  have hdescent : baseEnd_7217337 < baseStart_7217337 := by decide
  rcases family_descends (prefixWord ++ tailWord_7217337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7217344 : List Nat := [2, 1, 1, 2, 5, 1, 2, 2, 2, 5]
def baseStart_7217344 : Nat := 118140960795 + 7217344 * 2 ^ 59
def prefixEnd_7217344 : Nat := 4983230072969 + 3 ^ 40 * 7217344 * 2
def baseEnd_7217344 : Nat := 1235322173614505114036015

theorem tailTrace_7217344 : CollatzResearch.WordTrace tailWord_7217344 prefixEnd_7217344 1235322173614505114036015 := by
  unfold tailWord_7217344
  simp only [CollatzResearch.WordTrace]
  refine ⟨131619080782401393533041543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175492107709868524710722057 131619080782401393533041543)
  ·
    refine ⟨197428621173602090299562315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131619080782401393533041543 197428621173602090299562315)
    ·
      refine ⟨296142931760403135449343473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197428621173602090299562315 296142931760403135449343473)
      ·
        refine ⟨222107198820302351587007605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 296142931760403135449343473 222107198820302351587007605)
        ·
          refine ⟨20822549889403345461281963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 222107198820302351587007605 20822549889403345461281963)
          ·
            refine ⟨31233824834105018191922945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20822549889403345461281963 31233824834105018191922945)
            ·
              refine ⟨23425368625578763643942209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31233824834105018191922945 23425368625578763643942209)
              ·
                refine ⟨17569026469184072732956657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23425368625578763643942209 17569026469184072732956657)
                ·
                  refine ⟨13176769851888054549717493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17569026469184072732956657 13176769851888054549717493)
                  ·
                    refine ⟨1235322173614505114036015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13176769851888054549717493 1235322173614505114036015)
                    ·
                      rfl

theorem cell23_7217344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 2, 2, 2, 5].length) (baseStart_7217344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7217344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7217344 prefixEnd_7217344 := by exact prefixLift 7217344
  have htrace : WordTrace (prefixWord ++ tailWord_7217344) baseStart_7217344 baseEnd_7217344 := by
    simpa [prefixWord, tailWord_7217344, baseEnd_7217344] using wordTrace_append hprefix tailTrace_7217344
  have hstable : (prefixWord ++ tailWord_7217344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7217344).length < 2 ^ (prefixWord ++ tailWord_7217344).sum := by decide
  have hdescent : baseEnd_7217344 < baseStart_7217344 := by decide
  rcases family_descends (prefixWord ++ tailWord_7217344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7217348 : List Nat := [2, 3, 3, 1, 2, 1, 4, 2, 5]
def baseStart_7217348 : Nat := 118140960795 + 7217348 * 2 ^ 59
def prefixEnd_7217348 : Nat := 4983230072969 + 3 ^ 40 * 7217348 * 2
def baseEnd_7217348 : Nat := 411774286085125925162003

theorem tailTrace_7217348 : CollatzResearch.WordTrace tailWord_7217348 prefixEnd_7217348 411774286085125925162003 := by
  unfold tailWord_7217348
  simp only [CollatzResearch.WordTrace]
  refine ⟨131619153728394147874614349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175492204971192197166152465 131619153728394147874614349)
  ·
    refine ⟨49357182648147805452980381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 131619153728394147874614349 49357182648147805452980381)
    ·
      refine ⟨18508943493055427044867643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49357182648147805452980381 18508943493055427044867643)
      ·
        refine ⟨27763415239583140567301465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18508943493055427044867643 27763415239583140567301465)
        ·
          refine ⟨20822561429687355425476099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27763415239583140567301465 20822561429687355425476099)
          ·
            refine ⟨31233842144531033138214149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20822561429687355425476099 31233842144531033138214149)
            ·
              refine ⟨5856345402099568713415153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31233842144531033138214149 5856345402099568713415153)
              ·
                refine ⟨4392259051574676535061365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5856345402099568713415153 4392259051574676535061365)
                ·
                  refine ⟨411774286085125925162003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4392259051574676535061365 411774286085125925162003)
                  ·
                    rfl

theorem cell23_7217348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 4, 2, 5].length) (baseStart_7217348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7217348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7217348 prefixEnd_7217348 := by exact prefixLift 7217348
  have htrace : WordTrace (prefixWord ++ tailWord_7217348) baseStart_7217348 baseEnd_7217348 := by
    simpa [prefixWord, tailWord_7217348, baseEnd_7217348] using wordTrace_append hprefix tailTrace_7217348
  have hstable : (prefixWord ++ tailWord_7217348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7217348).length < 2 ^ (prefixWord ++ tailWord_7217348).sum := by decide
  have hdescent : baseEnd_7217348 < baseStart_7217348 := by decide
  rcases family_descends (prefixWord ++ tailWord_7217348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7217381 : List Nat := [1, 3, 1, 4, 2, 1, 3, 1, 2, 1, 4]
def baseStart_7217381 : Nat := 118140960795 + 7217381 * 2 ^ 59
def prefixEnd_7217381 : Nat := 4983230072969 + 3 ^ 40 * 7217381 * 2
def baseEnd_7217381 : Nat := 3705985519627731697345375

theorem tailTrace_7217381 : CollatzResearch.WordTrace tailWord_7217381 prefixEnd_7217381 3705985519627731697345375 := by
  unfold tailWord_7217381
  simp only [CollatzResearch.WordTrace]
  refine ⟨263239511065668742385179997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175493007377112494923453331 263239511065668742385179997)
  ·
    refine ⟨98714816649625778394442499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 263239511065668742385179997 98714816649625778394442499)
    ·
      refine ⟨148072224974438667591663749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98714816649625778394442499 148072224974438667591663749)
      ·
        refine ⟨27763542182707250173436953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 148072224974438667591663749 27763542182707250173436953)
        ·
          refine ⟨20822656637030437630077715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27763542182707250173436953 20822656637030437630077715)
          ·
            refine ⟨31233984955545656445116573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20822656637030437630077715 31233984955545656445116573)
            ·
              refine ⟨11712744358329621166918715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31233984955545656445116573 11712744358329621166918715)
              ·
                refine ⟨17569116537494431750378073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11712744358329621166918715 17569116537494431750378073)
                ·
                  refine ⟨13176837403120823812783555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17569116537494431750378073 13176837403120823812783555)
                  ·
                    refine ⟨19765256104681235719175333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13176837403120823812783555 19765256104681235719175333)
                    ·
                      refine ⟨3705985519627731697345375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19765256104681235719175333 3705985519627731697345375)
                      ·
                        rfl

theorem cell23_7217381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 3, 1, 2, 1, 4].length) (baseStart_7217381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7217381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7217381 prefixEnd_7217381 := by exact prefixLift 7217381
  have htrace : WordTrace (prefixWord ++ tailWord_7217381) baseStart_7217381 baseEnd_7217381 := by
    simpa [prefixWord, tailWord_7217381, baseEnd_7217381] using wordTrace_append hprefix tailTrace_7217381
  have hstable : (prefixWord ++ tailWord_7217381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7217381).length < 2 ^ (prefixWord ++ tailWord_7217381).sum := by decide
  have hdescent : baseEnd_7217381 < baseStart_7217381 := by decide
  rcases family_descends (prefixWord ++ tailWord_7217381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7217387 : List Nat := [1, 1, 1, 1, 2, 5, 2, 2, 8]
def baseStart_7217387 : Nat := 118140960795 + 7217387 * 2 ^ 59
def prefixEnd_7217387 : Nat := 4983230072969 + 3 ^ 40 * 7217387 * 2
def baseEnd_7217387 : Nat := 411776511167962074874483

theorem tailTrace_7217387 : CollatzResearch.WordTrace tailWord_7217387 prefixEnd_7217387 411776511167962074874483 := by
  unfold tailWord_7217387
  simp only [CollatzResearch.WordTrace]
  refine ⟨263239729903647005409898415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175493153269098003606598943 263239729903647005409898415)
  ·
    refine ⟨394859594855470508114847623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263239729903647005409898415 394859594855470508114847623)
    ·
      refine ⟨592289392283205762172271435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 394859594855470508114847623 592289392283205762172271435)
      ·
        refine ⟨888434088424808643258407153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 592289392283205762172271435 888434088424808643258407153)
        ·
          refine ⟨666325566318606482443805365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 888434088424808643258407153 666325566318606482443805365)
          ·
            refine ⟨62468021842369357729106753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 666325566318606482443805365 62468021842369357729106753)
            ·
              refine ⟨46851016381777018296830065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62468021842369357729106753 46851016381777018296830065)
              ·
                refine ⟨35138262286332763722622549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46851016381777018296830065 35138262286332763722622549)
                ·
                  refine ⟨411776511167962074874483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 35138262286332763722622549 411776511167962074874483)
                  ·
                    rfl

theorem cell23_7217387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 2, 2, 8].length) (baseStart_7217387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7217387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7217387 prefixEnd_7217387 := by exact prefixLift 7217387
  have htrace : WordTrace (prefixWord ++ tailWord_7217387) baseStart_7217387 baseEnd_7217387 := by
    simpa [prefixWord, tailWord_7217387, baseEnd_7217387] using wordTrace_append hprefix tailTrace_7217387
  have hstable : (prefixWord ++ tailWord_7217387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7217387).length < 2 ^ (prefixWord ++ tailWord_7217387).sum := by decide
  have hdescent : baseEnd_7217387 < baseStart_7217387 := by decide
  rcases family_descends (prefixWord ++ tailWord_7217387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7217394 : List Nat := [3, 2, 1, 3, 2, 1, 1, 1, 2, 1, 6]
def baseStart_7217394 : Nat := 118140960795 + 7217394 * 2 ^ 59
def prefixEnd_7217394 : Nat := 4983230072969 + 3 ^ 40 * 7217394 * 2
def baseEnd_7217394 : Nat := 3705992194876240146482815

theorem tailTrace_7217394 : CollatzResearch.WordTrace tailWord_7217394 prefixEnd_7217394 3705992194876240146482815 := by
  unfold tailWord_7217394
  simp only [CollatzResearch.WordTrace]
  refine ⟨65809996303655411401350809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175493323476414430403602157 65809996303655411401350809)
  ·
    refine ⟨49357497227741558551013107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65809996303655411401350809 49357497227741558551013107)
    ·
      refine ⟨74036245841612337826519661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49357497227741558551013107 74036245841612337826519661)
      ·
        refine ⟨27763592190604626684944873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74036245841612337826519661 27763592190604626684944873)
        ·
          refine ⟨20822694142953470013708655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27763592190604626684944873 20822694142953470013708655)
          ·
            refine ⟨31234041214430205020562983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20822694142953470013708655 31234041214430205020562983)
            ·
              refine ⟨46851061821645307530844475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31234041214430205020562983 46851061821645307530844475)
              ·
                refine ⟨70276592732467961296266713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46851061821645307530844475 70276592732467961296266713)
                ·
                  refine ⟨52707444549350970972200035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 70276592732467961296266713 52707444549350970972200035)
                  ·
                    refine ⟨79061166824026456458300053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 52707444549350970972200035 79061166824026456458300053)
                    ·
                      refine ⟨3705992194876240146482815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 79061166824026456458300053 3705992194876240146482815)
                      ·
                        rfl

theorem cell23_7217394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 1, 1, 2, 1, 6].length) (baseStart_7217394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7217394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7217394 prefixEnd_7217394 := by exact prefixLift 7217394
  have htrace : WordTrace (prefixWord ++ tailWord_7217394) baseStart_7217394 baseEnd_7217394 := by
    simpa [prefixWord, tailWord_7217394, baseEnd_7217394] using wordTrace_append hprefix tailTrace_7217394
  have hstable : (prefixWord ++ tailWord_7217394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7217394).length < 2 ^ (prefixWord ++ tailWord_7217394).sum := by decide
  have hdescent : baseEnd_7217394 < baseStart_7217394 := by decide
  rcases family_descends (prefixWord ++ tailWord_7217394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7217404 : List Nat := [2, 2, 2, 1, 4, 2, 1, 1, 8]
def baseStart_7217404 : Nat := 118140960795 + 7217404 * 2 ^ 59
def prefixEnd_7217404 : Nat := 4983230072969 + 3 ^ 40 * 7217404 * 2
def baseEnd_7217404 : Nat := 411777481075865011928641

theorem tailTrace_7217404 : CollatzResearch.WordTrace tailWord_7217404 prefixEnd_7217404 411777481075865011928641 := by
  unfold tailWord_7217404
  simp only [CollatzResearch.WordTrace]
  refine ⟨131620174972292708656633633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175493566629723611542178177 131620174972292708656633633)
  ·
    refine ⟨98715131229219531492475225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131620174972292708656633633 98715131229219531492475225)
    ·
      refine ⟨74036348421914648619356419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98715131229219531492475225 74036348421914648619356419)
      ·
        refine ⟨111054522632871972929034629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74036348421914648619356419 111054522632871972929034629)
        ·
          refine ⟨20822722993663494924193993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 111054522632871972929034629 20822722993663494924193993)
          ·
            refine ⟨15617042245247621193145495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20822722993663494924193993 15617042245247621193145495)
            ·
              refine ⟨23425563367871431789718243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15617042245247621193145495 23425563367871431789718243)
              ·
                refine ⟨35138345051807147684577365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23425563367871431789718243 35138345051807147684577365)
                ·
                  refine ⟨411777481075865011928641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 35138345051807147684577365 411777481075865011928641)
                  ·
                    rfl

theorem cell23_7217404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 1, 1, 8].length) (baseStart_7217404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7217404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7217404 prefixEnd_7217404 := by exact prefixLift 7217404
  have htrace : WordTrace (prefixWord ++ tailWord_7217404) baseStart_7217404 baseEnd_7217404 := by
    simpa [prefixWord, tailWord_7217404, baseEnd_7217404] using wordTrace_append hprefix tailTrace_7217404
  have hstable : (prefixWord ++ tailWord_7217404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7217404).length < 2 ^ (prefixWord ++ tailWord_7217404).sum := by decide
  have hdescent : baseEnd_7217404 < baseStart_7217404 := by decide
  rcases family_descends (prefixWord ++ tailWord_7217404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7217407 : List Nat := [1, 1, 2, 2, 1, 4, 1, 1, 1, 1, 8]
def baseStart_7217407 : Nat := 118140960795 + 7217407 * 2 ^ 59
def prefixEnd_7217407 : Nat := 4983230072969 + 3 ^ 40 * 7217407 * 2
def baseEnd_7217407 : Nat := 3705998870124748595620255

theorem tailTrace_7217407 : CollatzResearch.WordTrace tailWord_7217407 prefixEnd_7217407 3705998870124748595620255 := by
  unfold tailWord_7217407
  simp only [CollatzResearch.WordTrace]
  refine ⟨263240459363574548825626475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175493639575716365883750983 263240459363574548825626475)
  ·
    refine ⟨394860689045361823238439713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263240459363574548825626475 394860689045361823238439713)
    ·
      refine ⟨296145516784021367428829785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 394860689045361823238439713 296145516784021367428829785)
      ·
        refine ⟨222109137588016025571622339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 296145516784021367428829785 222109137588016025571622339)
        ·
          refine ⟨333163706382024038357433509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 222109137588016025571622339 333163706382024038357433509)
          ·
            refine ⟨62468194946629507192018783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 333163706382024038357433509 62468194946629507192018783)
            ·
              refine ⟨93702292419944260788028175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62468194946629507192018783 93702292419944260788028175)
              ·
                refine ⟨140553438629916391182042263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 93702292419944260788028175 140553438629916391182042263)
                ·
                  refine ⟨210830157944874586773063395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 140553438629916391182042263 210830157944874586773063395)
                  ·
                    refine ⟨316245236917311880159595093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 210830157944874586773063395 316245236917311880159595093)
                    ·
                      refine ⟨3705998870124748595620255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 316245236917311880159595093 3705998870124748595620255)
                      ·
                        rfl

theorem cell23_7217407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 1, 1, 1, 8].length) (baseStart_7217407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7217407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7217407 prefixEnd_7217407 := by exact prefixLift 7217407
  have htrace : WordTrace (prefixWord ++ tailWord_7217407) baseStart_7217407 baseEnd_7217407 := by
    simpa [prefixWord, tailWord_7217407, baseEnd_7217407] using wordTrace_append hprefix tailTrace_7217407
  have hstable : (prefixWord ++ tailWord_7217407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7217407).length < 2 ^ (prefixWord ++ tailWord_7217407).sum := by decide
  have hdescent : baseEnd_7217407 < baseStart_7217407 := by decide
  rcases family_descends (prefixWord ++ tailWord_7217407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7217427 : List Nat := [1, 1, 1, 2, 1, 3, 1, 3, 2, 1, 7]
def baseStart_7217427 : Nat := 118140960795 + 7217427 * 2 ^ 59
def prefixEnd_7217427 : Nat := 4983230072969 + 3 ^ 40 * 7217427 * 2
def baseEnd_7217427 : Nat := 3706009139737838517370163

theorem tailTrace_7217427 : CollatzResearch.WordTrace tailWord_7217427 prefixEnd_7217427 3706009139737838517370163 := by
  unfold tailWord_7217427
  simp only [CollatzResearch.WordTrace]
  refine ⟨263241188823502092241354535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175494125882334728160903023 263241188823502092241354535)
  ·
    refine ⟨394861783235253138362031803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263241188823502092241354535 394861783235253138362031803)
    ·
      refine ⟨592292674852879707543047705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 394861783235253138362031803 592292674852879707543047705)
      ·
        refine ⟨444219506139659780657285779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 592292674852879707543047705 444219506139659780657285779)
        ·
          refine ⟨666329259209489670985928669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 444219506139659780657285779 666329259209489670985928669)
          ·
            refine ⟨249873472203558626619723251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 666329259209489670985928669 249873472203558626619723251)
            ·
              refine ⟨374810208305337939929584877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 249873472203558626619723251 374810208305337939929584877)
              ·
                refine ⟨140553828114501727473594329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 374810208305337939929584877 140553828114501727473594329)
                ·
                  refine ⟨105415371085876295605195747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 140553828114501727473594329 105415371085876295605195747)
                  ·
                    refine ⟨158123056628814443407793621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 105415371085876295605195747 158123056628814443407793621)
                    ·
                      refine ⟨3706009139737838517370163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 158123056628814443407793621 3706009139737838517370163)
                      ·
                        rfl

theorem cell23_7217427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 3, 2, 1, 7].length) (baseStart_7217427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7217427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7217427 prefixEnd_7217427 := by exact prefixLift 7217427
  have htrace : WordTrace (prefixWord ++ tailWord_7217427) baseStart_7217427 baseEnd_7217427 := by
    simpa [prefixWord, tailWord_7217427, baseEnd_7217427] using wordTrace_append hprefix tailTrace_7217427
  have hstable : (prefixWord ++ tailWord_7217427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7217427).length < 2 ^ (prefixWord ++ tailWord_7217427).sum := by decide
  have hdescent : baseEnd_7217427 < baseStart_7217427 := by decide
  rcases family_descends (prefixWord ++ tailWord_7217427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7217441 : List Nat := [1, 2, 3, 2, 1, 1, 4, 1, 1, 5, 2]
def baseStart_7217441 : Nat := 118140960795 + 7217441 * 2 ^ 59
def prefixEnd_7217441 : Nat := 4983230072969 + 3 ^ 40 * 7217441 * 2
def baseEnd_7217441 : Nat := 3706016328467001462595099

theorem tailTrace_7217441 : CollatzResearch.WordTrace tailWord_7217441 prefixEnd_7217441 3706016328467001462595099 := by
  unfold tailWord_7217441
  simp only [CollatzResearch.WordTrace]
  refine ⟨263241699445451372632364177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175494466296967581754909451 263241699445451372632364177)
  ·
    refine ⟨197431274584088529474273133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 263241699445451372632364177 197431274584088529474273133)
    ·
      refine ⟨74036727969033198552852425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 197431274584088529474273133 74036727969033198552852425)
      ·
        refine ⟨55527545976774898914639319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74036727969033198552852425 55527545976774898914639319)
        ·
          refine ⟨83291318965162348371958979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55527545976774898914639319 83291318965162348371958979)
          ·
            refine ⟨124936978447743522557938469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83291318965162348371958979 124936978447743522557938469)
            ·
              refine ⟨23425683458951910479613463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 124936978447743522557938469 23425683458951910479613463)
              ·
                refine ⟨35138525188427865719420195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23425683458951910479613463 35138525188427865719420195)
                ·
                  refine ⟨52707787782641798579130293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35138525188427865719420195 52707787782641798579130293)
                  ·
                    refine ⟨4941355104622668616793465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 52707787782641798579130293 4941355104622668616793465)
                    ·
                      refine ⟨3706016328467001462595099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4941355104622668616793465 3706016328467001462595099)
                      ·
                        rfl

theorem cell23_7217441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 4, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 4, 1, 1, 5, 2].length) (baseStart_7217441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7217441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7217441 prefixEnd_7217441 := by exact prefixLift 7217441
  have htrace : WordTrace (prefixWord ++ tailWord_7217441) baseStart_7217441 baseEnd_7217441 := by
    simpa [prefixWord, tailWord_7217441, baseEnd_7217441] using wordTrace_append hprefix tailTrace_7217441
  have hstable : (prefixWord ++ tailWord_7217441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7217441).length < 2 ^ (prefixWord ++ tailWord_7217441).sum := by decide
  have hdescent : baseEnd_7217441 < baseStart_7217441 := by decide
  rcases family_descends (prefixWord ++ tailWord_7217441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7217465 : List Nat := [1, 2, 1, 6, 1, 3, 1, 1, 3, 1, 3]
def baseStart_7217465 : Nat := 118140960795 + 7217465 * 2 ^ 59
def prefixEnd_7217465 : Nat := 4983230072969 + 3 ^ 40 * 7217465 * 2
def baseEnd_7217465 : Nat := 3706028652002709368694989

theorem tailTrace_7217465 : CollatzResearch.WordTrace tailWord_7217465 prefixEnd_7217465 3706028652002709368694989 := by
  unfold tailWord_7217465
  simp only [CollatzResearch.WordTrace]
  refine ⟨263242574797364424731237849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175495049864909616487491899 263242574797364424731237849)
  ·
    refine ⟨197431931098023318548428387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 263242574797364424731237849 197431931098023318548428387)
    ·
      refine ⟨296147896647034977822642581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197431931098023318548428387 296147896647034977822642581)
      ·
        refine ⟨13881932655329764585436371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 296147896647034977822642581 13881932655329764585436371)
        ·
          refine ⟨20822898982994646878154557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13881932655329764585436371 20822898982994646878154557)
          ·
            refine ⟨7808587118622992579307959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20822898982994646878154557 7808587118622992579307959)
            ·
              refine ⟨11712880677934488868961939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7808587118622992579307959 11712880677934488868961939)
              ·
                refine ⟨17569321016901733303442909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11712880677934488868961939 17569321016901733303442909)
                ·
                  refine ⟨6588495381338149988791091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17569321016901733303442909 6588495381338149988791091)
                  ·
                    refine ⟨9882743072007224983186637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6588495381338149988791091 9882743072007224983186637)
                    ·
                      refine ⟨3706028652002709368694989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9882743072007224983186637 3706028652002709368694989)
                      ·
                        rfl

theorem cell23_7217465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 3, 1, 1, 3, 1, 3].length) (baseStart_7217465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7217465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7217465 prefixEnd_7217465 := by exact prefixLift 7217465
  have htrace : WordTrace (prefixWord ++ tailWord_7217465) baseStart_7217465 baseEnd_7217465 := by
    simpa [prefixWord, tailWord_7217465, baseEnd_7217465] using wordTrace_append hprefix tailTrace_7217465
  have hstable : (prefixWord ++ tailWord_7217465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7217465).length < 2 ^ (prefixWord ++ tailWord_7217465).sum := by decide
  have hdescent : baseEnd_7217465 < baseStart_7217465 := by decide
  rcases family_descends (prefixWord ++ tailWord_7217465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7217484 : List Nat := [2, 2, 1, 3, 2, 1, 1, 3, 1, 1, 6]
def baseStart_7217484 : Nat := 118140960795 + 7217484 * 2 ^ 59
def prefixEnd_7217484 : Nat := 4983230072969 + 3 ^ 40 * 7217484 * 2
def baseEnd_7217484 : Nat := 3706038408135144794357401

theorem tailTrace_7217484 : CollatzResearch.WordTrace tailWord_7217484 prefixEnd_7217484 3706038408135144794357401 := by
  unfold tailWord_7217484
  simp only [CollatzResearch.WordTrace]
  refine ⟨131621633892147795488089753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175495511856197060650786337 131621633892147795488089753)
  ·
    refine ⟨98716225419110846616067315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131621633892147795488089753 98716225419110846616067315)
    ·
      refine ⟨148074338128666269924100973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98716225419110846616067315 148074338128666269924100973)
      ·
        refine ⟨55527876798249851221537865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 148074338128666269924100973 55527876798249851221537865)
        ·
          refine ⟨41645907598687388416153399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55527876798249851221537865 41645907598687388416153399)
          ·
            refine ⟨62468861398031082624230099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41645907598687388416153399 62468861398031082624230099)
            ·
              refine ⟨93703292097046623936345149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62468861398031082624230099 93703292097046623936345149)
              ·
                refine ⟨35138734536392483976129431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 93703292097046623936345149 35138734536392483976129431)
                ·
                  refine ⟨52708101804588725964194147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35138734536392483976129431 52708101804588725964194147)
                  ·
                    refine ⟨79062152706883088946291221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 52708101804588725964194147 79062152706883088946291221)
                    ·
                      refine ⟨3706038408135144794357401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 79062152706883088946291221 3706038408135144794357401)
                      ·
                        rfl

theorem cell23_7217484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 3, 1, 1, 6].length) (baseStart_7217484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7217484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7217484 prefixEnd_7217484 := by exact prefixLift 7217484
  have htrace : WordTrace (prefixWord ++ tailWord_7217484) baseStart_7217484 baseEnd_7217484 := by
    simpa [prefixWord, tailWord_7217484, baseEnd_7217484] using wordTrace_append hprefix tailTrace_7217484
  have hstable : (prefixWord ++ tailWord_7217484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7217484).length < 2 ^ (prefixWord ++ tailWord_7217484).sum := by decide
  have hdescent : baseEnd_7217484 < baseStart_7217484 := by decide
  rcases family_descends (prefixWord ++ tailWord_7217484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
