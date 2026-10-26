import V185TrunkScan23Chunk0733

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_4340832 : List Nat := [2, 1, 1, 3, 2, 2, 2, 2, 4, 1, 3]
def baseStart_4340832 : Nat := 118140960795 + 4340832 * 2 ^ 59
def prefixEnd_4340832 : Nat := 4983230072969 + 3 ^ 40 * 4340832 * 2
def baseEnd_4340832 : Nat := 2228933256417665708536883

theorem tailTrace_4340832 : CollatzResearch.WordTrace tailWord_4340832 prefixEnd_4340832 2228933256417665708536883 := by
  unfold tailWord_4340832
  simp only [CollatzResearch.WordTrace]
  refine ⟨79161574904957246964208375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105548766539942995952277833 79161574904957246964208375)
  ·
    refine ⟨118742362357435870446312563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79161574904957246964208375 118742362357435870446312563)
    ·
      refine ⟨178113543536153805669468845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118742362357435870446312563 178113543536153805669468845)
      ·
        refine ⟨66792578826057677126050817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 178113543536153805669468845 66792578826057677126050817)
        ·
          refine ⟨50094434119543257844538113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66792578826057677126050817 50094434119543257844538113)
          ·
            refine ⟨37570825589657443383403585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50094434119543257844538113 37570825589657443383403585)
            ·
              refine ⟨28178119192243082537552689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37570825589657443383403585 28178119192243082537552689)
              ·
                refine ⟨21133589394182311903164517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28178119192243082537552689 21133589394182311903164517)
                ·
                  refine ⟨3962548011409183481843347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21133589394182311903164517 3962548011409183481843347)
                  ·
                    refine ⟨5943822017113775222765021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3962548011409183481843347 5943822017113775222765021)
                    ·
                      refine ⟨2228933256417665708536883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5943822017113775222765021 2228933256417665708536883)
                      ·
                        rfl

theorem cell23_4340832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 2, 2, 4, 1, 3].length) (baseStart_4340832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4340832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4340832 prefixEnd_4340832 := by exact prefixLift 4340832
  have htrace : WordTrace (prefixWord ++ tailWord_4340832) baseStart_4340832 baseEnd_4340832 := by
    simpa [prefixWord, tailWord_4340832, baseEnd_4340832] using wordTrace_append hprefix tailTrace_4340832
  have hstable : (prefixWord ++ tailWord_4340832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4340832).length < 2 ^ (prefixWord ++ tailWord_4340832).sum := by decide
  have hdescent : baseEnd_4340832 < baseStart_4340832 := by decide
  rcases family_descends (prefixWord ++ tailWord_4340832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4340875 : List Nat := [1, 1, 1, 1, 4, 1, 1, 4, 2, 4, 3]
def baseStart_4340875 : Nat := 118140960795 + 4340875 * 2 ^ 59
def prefixEnd_4340875 : Nat := 4983230072969 + 3 ^ 40 * 4340875 * 2
def baseEnd_4340875 : Nat := 2228955336085809040299185

theorem tailTrace_4340875 : CollatzResearch.WordTrace tailWord_4340875 prefixEnd_4340875 2228955336085809040299185 := by
  unfold tailWord_4340875
  simp only [CollatzResearch.WordTrace]
  refine ⟨158324718148758712272232079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105549812099172474848154719 158324718148758712272232079)
  ·
    refine ⟨237487077223138068408348119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158324718148758712272232079 237487077223138068408348119)
    ·
      refine ⟨356230615834707102612522179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 237487077223138068408348119 356230615834707102612522179)
      ·
        refine ⟨534345923752060653918783269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 356230615834707102612522179 534345923752060653918783269)
        ·
          refine ⟨100189860703511372609771863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 534345923752060653918783269 100189860703511372609771863)
          ·
            refine ⟨150284791055267058914657795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 100189860703511372609771863 150284791055267058914657795)
            ·
              refine ⟨225427186582900588371986693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 150284791055267058914657795 225427186582900588371986693)
              ·
                refine ⟨42267597484293860319747505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 225427186582900588371986693 42267597484293860319747505)
                ·
                  refine ⟨31700698113220395239810629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 42267597484293860319747505 31700698113220395239810629)
                  ·
                    refine ⟨5943880896228824107464493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 31700698113220395239810629 5943880896228824107464493)
                    ·
                      refine ⟨2228955336085809040299185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5943880896228824107464493 2228955336085809040299185)
                      ·
                        rfl

theorem cell23_4340875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 4, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 4, 2, 4, 3].length) (baseStart_4340875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4340875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4340875 prefixEnd_4340875 := by exact prefixLift 4340875
  have htrace : WordTrace (prefixWord ++ tailWord_4340875) baseStart_4340875 baseEnd_4340875 := by
    simpa [prefixWord, tailWord_4340875, baseEnd_4340875] using wordTrace_append hprefix tailTrace_4340875
  have hstable : (prefixWord ++ tailWord_4340875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4340875).length < 2 ^ (prefixWord ++ tailWord_4340875).sum := by decide
  have hdescent : baseEnd_4340875 < baseStart_4340875 := by decide
  rcases family_descends (prefixWord ++ tailWord_4340875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4340885 : List Nat := [1, 3, 2, 1, 1, 1, 2, 2, 4, 2, 4]
def baseStart_4340885 : Nat := 118140960795 + 4340885 * 2 ^ 59
def prefixEnd_4340885 : Nat := 4983230072969 + 3 ^ 40 * 4340885 * 2
def baseEnd_4340885 : Nat := 2228960470892354001174139

theorem tailTrace_4340885 : CollatzResearch.WordTrace tailWord_4340885 prefixEnd_4340885 2228960470892354001174139 := by
  unfold tailWord_4340885
  simp only [CollatzResearch.WordTrace]
  refine ⟨158325082878722483980096109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105550055252481655986730739 158325082878722483980096109)
  ·
    refine ⟨59371906079520931492536041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 158325082878722483980096109 59371906079520931492536041)
    ·
      refine ⟨44528929559640698619402031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59371906079520931492536041 44528929559640698619402031)
      ·
        refine ⟨66793394339461047929103047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44528929559640698619402031 66793394339461047929103047)
        ·
          refine ⟨100190091509191571893654571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66793394339461047929103047 100190091509191571893654571)
          ·
            refine ⟨150285137263787357840481857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 100190091509191571893654571 150285137263787357840481857)
            ·
              refine ⟨112713852947840518380361393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 150285137263787357840481857 112713852947840518380361393)
              ·
                refine ⟨84535389710880388785271045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 112713852947840518380361393 84535389710880388785271045)
                ·
                  refine ⟨15850385570790072897238321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 84535389710880388785271045 15850385570790072897238321)
                  ·
                    refine ⟨11887789178092554672928741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15850385570790072897238321 11887789178092554672928741)
                    ·
                      refine ⟨2228960470892354001174139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11887789178092554672928741 2228960470892354001174139)
                      ·
                        rfl

theorem cell23_4340885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 2, 4, 2, 4].length) (baseStart_4340885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4340885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4340885 prefixEnd_4340885 := by exact prefixLift 4340885
  have htrace : WordTrace (prefixWord ++ tailWord_4340885) baseStart_4340885 baseEnd_4340885 := by
    simpa [prefixWord, tailWord_4340885, baseEnd_4340885] using wordTrace_append hprefix tailTrace_4340885
  have hstable : (prefixWord ++ tailWord_4340885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4340885).length < 2 ^ (prefixWord ++ tailWord_4340885).sum := by decide
  have hdescent : baseEnd_4340885 < baseStart_4340885 := by decide
  rcases family_descends (prefixWord ++ tailWord_4340885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4340892 : List Nat := [2, 2, 3, 2, 1, 3, 1, 1, 2, 1, 5]
def baseStart_4340892 : Nat := 118140960795 + 4340892 * 2 ^ 59
def prefixEnd_4340892 : Nat := 4983230072969 + 3 ^ 40 * 4340892 * 2
def baseEnd_4340892 : Nat := 2228964065256935473786607

theorem tailTrace_4340892 : CollatzResearch.WordTrace tailWord_4340892 prefixEnd_4340892 2228964065256935473786607 := by
  unfold tailWord_4340892
  simp only [CollatzResearch.WordTrace]
  refine ⟨79162669094848562087800465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105550225459798082783733953 79162669094848562087800465)
  ·
    refine ⟨59372001821136421565850349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79162669094848562087800465 59372001821136421565850349)
    ·
      refine ⟨22264500682926158087193881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59372001821136421565850349 22264500682926158087193881)
      ·
        refine ⟨16698375512194618565395411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22264500682926158087193881 16698375512194618565395411)
        ·
          refine ⟨25047563268291927848093117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16698375512194618565395411 25047563268291927848093117)
          ·
            refine ⟨9392836225609472943034919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25047563268291927848093117 9392836225609472943034919)
            ·
              refine ⟨14089254338414209414552379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9392836225609472943034919 14089254338414209414552379)
              ·
                refine ⟨21133881507621314121828569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14089254338414209414552379 21133881507621314121828569)
                ·
                  refine ⟨15850411130715985591371427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21133881507621314121828569 15850411130715985591371427)
                  ·
                    refine ⟨23775616696073978387057141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15850411130715985591371427 23775616696073978387057141)
                    ·
                      refine ⟨2228964065256935473786607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23775616696073978387057141 2228964065256935473786607)
                      ·
                        rfl

theorem cell23_4340892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 1, 1, 2, 1, 5].length) (baseStart_4340892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4340892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4340892 prefixEnd_4340892 := by exact prefixLift 4340892
  have htrace : WordTrace (prefixWord ++ tailWord_4340892) baseStart_4340892 baseEnd_4340892 := by
    simpa [prefixWord, tailWord_4340892, baseEnd_4340892] using wordTrace_append hprefix tailTrace_4340892
  have hstable : (prefixWord ++ tailWord_4340892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4340892).length < 2 ^ (prefixWord ++ tailWord_4340892).sum := by decide
  have hdescent : baseEnd_4340892 < baseStart_4340892 := by decide
  rcases family_descends (prefixWord ++ tailWord_4340892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4340905 : List Nat := [1, 2, 1, 1, 1, 1, 2, 1, 5, 5, 3]
def baseStart_4340905 : Nat := 118140960795 + 4340905 * 2 ^ 59
def prefixEnd_4340905 : Nat := 4983230072969 + 3 ^ 40 * 4340905 * 2
def baseEnd_4340905 : Nat := 2228970740505443922924047

theorem tailTrace_4340905 : CollatzResearch.WordTrace tailWord_4340905 prefixEnd_4340905 2228970740505443922924047 := by
  unfold tailWord_4340905
  simp only [CollatzResearch.WordTrace]
  refine ⟨158325812338650027395824169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105550541559100018263882779 158325812338650027395824169)
  ·
    refine ⟨118744359253987520546868127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 158325812338650027395824169 118744359253987520546868127)
    ·
      refine ⟨178116538880981280820302191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118744359253987520546868127 178116538880981280820302191)
      ·
        refine ⟨267174808321471921230453287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 178116538880981280820302191 267174808321471921230453287)
        ·
          refine ⟨400762212482207881845679931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 267174808321471921230453287 400762212482207881845679931)
          ·
            refine ⟨601143318723311822768519897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 400762212482207881845679931 601143318723311822768519897)
            ·
              refine ⟨450857489042483867076389923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 601143318723311822768519897 450857489042483867076389923)
              ·
                refine ⟨676286233563725800614584885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 450857489042483867076389923 676286233563725800614584885)
                ·
                  refine ⟨63401834396599293807617333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 676286233563725800614584885 63401834396599293807617333)
                  ·
                    refine ⟨5943921974681183794464125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 63401834396599293807617333 5943921974681183794464125)
                    ·
                      refine ⟨2228970740505443922924047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5943921974681183794464125 2228970740505443922924047)
                      ·
                        rfl

theorem cell23_4340905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 1, 5, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 1, 5, 5, 3].length) (baseStart_4340905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4340905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4340905 prefixEnd_4340905 := by exact prefixLift 4340905
  have htrace : WordTrace (prefixWord ++ tailWord_4340905) baseStart_4340905 baseEnd_4340905 := by
    simpa [prefixWord, tailWord_4340905, baseEnd_4340905] using wordTrace_append hprefix tailTrace_4340905
  have hstable : (prefixWord ++ tailWord_4340905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4340905).length < 2 ^ (prefixWord ++ tailWord_4340905).sum := by decide
  have hdescent : baseEnd_4340905 < baseStart_4340905 := by decide
  rcases family_descends (prefixWord ++ tailWord_4340905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4340925 : List Nat := [1, 4, 1, 2, 1, 1, 2, 1, 3, 7]
def baseStart_4340925 : Nat := 118140960795 + 4340925 * 2 ^ 59
def prefixEnd_4340925 : Nat := 4983230072969 + 3 ^ 40 * 4340925 * 2
def baseEnd_4340925 : Nat := 742993670039511281557985

theorem tailTrace_4340925 : CollatzResearch.WordTrace tailWord_4340925 prefixEnd_4340925 742993670039511281557985 := by
  unfold tailWord_4340925
  simp only [CollatzResearch.WordTrace]
  refine ⟨158326541798577570811552229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105551027865718380541034819 158326541798577570811552229)
  ·
    refine ⟨29686226587233294527166043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 158326541798577570811552229 29686226587233294527166043)
    ·
      refine ⟨44529339880849941790749065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29686226587233294527166043 44529339880849941790749065)
      ·
        refine ⟨33397004910637456343061799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44529339880849941790749065 33397004910637456343061799)
        ·
          refine ⟨50095507365956184514592699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33397004910637456343061799 50095507365956184514592699)
          ·
            refine ⟨75143261048934276771889049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50095507365956184514592699 75143261048934276771889049)
            ·
              refine ⟨56357445786700707578916787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 75143261048934276771889049 56357445786700707578916787)
              ·
                refine ⟨84536168680051061368375181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56357445786700707578916787 84536168680051061368375181)
                ·
                  refine ⟨31701063255019148013140693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 84536168680051061368375181 31701063255019148013140693)
                  ·
                    refine ⟨742993670039511281557985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 31701063255019148013140693 742993670039511281557985)
                    ·
                      rfl

theorem cell23_4340925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 1, 3, 7].length) (baseStart_4340925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4340925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4340925 prefixEnd_4340925 := by exact prefixLift 4340925
  have htrace : WordTrace (prefixWord ++ tailWord_4340925) baseStart_4340925 baseEnd_4340925 := by
    simpa [prefixWord, tailWord_4340925, baseEnd_4340925] using wordTrace_append hprefix tailTrace_4340925
  have hstable : (prefixWord ++ tailWord_4340925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4340925).length < 2 ^ (prefixWord ++ tailWord_4340925).sum := by decide
  have hdescent : baseEnd_4340925 < baseStart_4340925 := by decide
  rcases family_descends (prefixWord ++ tailWord_4340925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4340979 : List Nat := [1, 1, 1, 2, 2, 6, 1, 1, 2, 4, 2]
def baseStart_4340979 : Nat := 118140960795 + 4340979 * 2 ^ 59
def prefixEnd_4340979 : Nat := 4983230072969 + 3 ^ 40 * 4340979 * 2
def baseEnd_4340979 : Nat := 2229008738073876633398707

theorem tailTrace_4340979 : CollatzResearch.WordTrace tailWord_4340979 prefixEnd_4340979 2229008738073876633398707 := by
  unfold tailWord_4340979
  simp only [CollatzResearch.WordTrace]
  refine ⟨158328511340381938034017991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105552340893587958689345327 158328511340381938034017991)
  ·
    refine ⟨237492767010572907051026987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158328511340381938034017991 237492767010572907051026987)
    ·
      refine ⟨356239150515859360576540481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 237492767010572907051026987 356239150515859360576540481)
      ·
        refine ⟨267179362886894520432405361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 356239150515859360576540481 267179362886894520432405361)
        ·
          refine ⟨200384522165170890324304021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 267179362886894520432405361 200384522165170890324304021)
          ·
            refine ⟨9393024476492385483951751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 200384522165170890324304021 9393024476492385483951751)
            ·
              refine ⟨14089536714738578225927627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9393024476492385483951751 14089536714738578225927627)
              ·
                refine ⟨21134305072107867338891441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14089536714738578225927627 21134305072107867338891441)
                ·
                  refine ⟨15850728804080900504168581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21134305072107867338891441 15850728804080900504168581)
                  ·
                    refine ⟨2972011650765168844531609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15850728804080900504168581 2972011650765168844531609)
                    ·
                      refine ⟨2229008738073876633398707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2972011650765168844531609 2229008738073876633398707)
                      ·
                        rfl

theorem cell23_4340979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 1, 1, 2, 4, 2].length) (baseStart_4340979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4340979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4340979 prefixEnd_4340979 := by exact prefixLift 4340979
  have htrace : WordTrace (prefixWord ++ tailWord_4340979) baseStart_4340979 baseEnd_4340979 := by
    simpa [prefixWord, tailWord_4340979, baseEnd_4340979] using wordTrace_append hprefix tailTrace_4340979
  have hstable : (prefixWord ++ tailWord_4340979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4340979).length < 2 ^ (prefixWord ++ tailWord_4340979).sum := by decide
  have hdescent : baseEnd_4340979 < baseStart_4340979 := by decide
  rcases family_descends (prefixWord ++ tailWord_4340979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4340996 : List Nat := [2, 3, 2, 2, 2, 3, 1, 1, 2, 1, 4]
def baseStart_4340996 : Nat := 118140960795 + 4340996 * 2 ^ 59
def prefixEnd_4340996 : Nat := 4983230072969 + 3 ^ 40 * 4340996 * 2
def baseEnd_4340996 : Nat := 2229017467245003066886129

theorem tailTrace_4340996 : CollatzResearch.WordTrace tailWord_4340996 prefixEnd_4340996 2229017467245003066886129 := by
  unfold tailWord_4340996
  simp only [CollatzResearch.WordTrace]
  refine ⟨79164565690660174968693421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105552754254213566624924561 79164565690660174968693421)
  ·
    refine ⟨29686712133997565613260033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79164565690660174968693421 29686712133997565613260033)
    ·
      refine ⟨22265034100498174209945025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29686712133997565613260033 22265034100498174209945025)
      ·
        refine ⟨16698775575373630657458769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22265034100498174209945025 16698775575373630657458769)
        ·
          refine ⟨12524081681530222993094077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16698775575373630657458769 12524081681530222993094077)
          ·
            refine ⟨4696530630573833622410279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12524081681530222993094077 4696530630573833622410279)
            ·
              refine ⟨7044795945860750433615419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4696530630573833622410279 7044795945860750433615419)
              ·
                refine ⟨10567193918791125650423129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7044795945860750433615419 10567193918791125650423129)
                ·
                  refine ⟨7925395439093344237817347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10567193918791125650423129 7925395439093344237817347)
                  ·
                    refine ⟨11888093158640016356726021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7925395439093344237817347 11888093158640016356726021)
                    ·
                      refine ⟨2229017467245003066886129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11888093158640016356726021 2229017467245003066886129)
                      ·
                        rfl

theorem cell23_4340996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 3, 1, 1, 2, 1, 4].length) (baseStart_4340996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4340996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4340996 prefixEnd_4340996 := by exact prefixLift 4340996
  have htrace : WordTrace (prefixWord ++ tailWord_4340996) baseStart_4340996 baseEnd_4340996 := by
    simpa [prefixWord, tailWord_4340996, baseEnd_4340996] using wordTrace_append hprefix tailTrace_4340996
  have hstable : (prefixWord ++ tailWord_4340996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4340996).length < 2 ^ (prefixWord ++ tailWord_4340996).sum := by decide
  have hdescent : baseEnd_4340996 < baseStart_4340996 := by decide
  rcases family_descends (prefixWord ++ tailWord_4340996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4341006 : List Nat := [4, 1, 1, 2, 1, 3, 1, 5, 1, 4]
def baseStart_4341006 : Nat := 118140960795 + 4341006 * 2 ^ 59
def prefixEnd_4341006 : Nat := 4983230072969 + 3 ^ 40 * 4341006 * 2
def baseEnd_4341006 : Nat := 743007534017182675920361

theorem tailTrace_4341006 : CollatzResearch.WordTrace tailWord_4341006 prefixEnd_4341006 743007534017182675920361 := by
  unfold tailWord_4341006
  simp only [CollatzResearch.WordTrace]
  refine ⟨19791187013910515205656359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 105552997407522747763500581 19791187013910515205656359)
  ·
    refine ⟨29686780520865772808484539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19791187013910515205656359 29686780520865772808484539)
    ·
      refine ⟨44530170781298659212726809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29686780520865772808484539 44530170781298659212726809)
      ·
        refine ⟨33397628085973994409545107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44530170781298659212726809 33397628085973994409545107)
        ·
          refine ⟨50096442128960991614317661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33397628085973994409545107 50096442128960991614317661)
          ·
            refine ⟨18786165798360371855369123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50096442128960991614317661 18786165798360371855369123)
            ·
              refine ⟨28179248697540557783053685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18786165798360371855369123 28179248697540557783053685)
              ·
                refine ⟨2641804565394427292161283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 28179248697540557783053685 2641804565394427292161283)
                ·
                  refine ⟨3962706848091640938241925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2641804565394427292161283 3962706848091640938241925)
                  ·
                    refine ⟨743007534017182675920361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3962706848091640938241925 743007534017182675920361)
                    ·
                      rfl

theorem cell23_4341006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 1, 5, 1, 4].length) (baseStart_4341006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4341006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4341006 prefixEnd_4341006 := by exact prefixLift 4341006
  have htrace : WordTrace (prefixWord ++ tailWord_4341006) baseStart_4341006 baseEnd_4341006 := by
    simpa [prefixWord, tailWord_4341006, baseEnd_4341006] using wordTrace_append hprefix tailTrace_4341006
  have hstable : (prefixWord ++ tailWord_4341006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4341006).length < 2 ^ (prefixWord ++ tailWord_4341006).sum := by decide
  have hdescent : baseEnd_4341006 < baseStart_4341006 := by decide
  rcases family_descends (prefixWord ++ tailWord_4341006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4341035 : List Nat := [1, 1, 1, 1, 2, 1, 2, 1, 2, 1, 10]
def baseStart_4341035 : Nat := 118140960795 + 4341035 * 2 ^ 59
def prefixEnd_4341035 : Nat := 4983230072969 + 3 ^ 40 * 4341035 * 2
def baseEnd_4341035 : Nat := 2229037492990528414298449

theorem tailTrace_4341035 : CollatzResearch.WordTrace tailWord_4341035 prefixEnd_4341035 2229037492990528414298449 := by
  unfold tailWord_4341035
  simp only [CollatzResearch.WordTrace]
  refine ⟨158330553828179059598056559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105553702552119373065371039 158330553828179059598056559)
  ·
    refine ⟨237495830742268589397084839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158330553828179059598056559 237495830742268589397084839)
    ·
      refine ⟨356243746113402884095627259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 237495830742268589397084839 356243746113402884095627259)
      ·
        refine ⟨534365619170104326143440889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 356243746113402884095627259 534365619170104326143440889)
        ·
          refine ⟨400774214377578244607580667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 534365619170104326143440889 400774214377578244607580667)
          ·
            refine ⟨601161321566367366911371001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 400774214377578244607580667 601161321566367366911371001)
            ·
              refine ⟨450870991174775525183528251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 601161321566367366911371001 450870991174775525183528251)
              ·
                refine ⟨676306486762163287775292377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 450870991174775525183528251 676306486762163287775292377)
                ·
                  refine ⟨507229865071622465831469283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 676306486762163287775292377 507229865071622465831469283)
                  ·
                    refine ⟨760844797607433698747203925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 507229865071622465831469283 760844797607433698747203925)
                    ·
                      refine ⟨2229037492990528414298449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 10 760844797607433698747203925 2229037492990528414298449)
                      ·
                        rfl

theorem cell23_4341035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 1, 2, 1, 10].length) (baseStart_4341035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4341035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4341035 prefixEnd_4341035 := by exact prefixLift 4341035
  have htrace : WordTrace (prefixWord ++ tailWord_4341035) baseStart_4341035 baseEnd_4341035 := by
    simpa [prefixWord, tailWord_4341035, baseEnd_4341035] using wordTrace_append hprefix tailTrace_4341035
  have hstable : (prefixWord ++ tailWord_4341035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4341035).length < 2 ^ (prefixWord ++ tailWord_4341035).sum := by decide
  have hdescent : baseEnd_4341035 < baseStart_4341035 := by decide
  rcases family_descends (prefixWord ++ tailWord_4341035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4341063 : List Nat := [1, 1, 4, 1, 2, 3, 3, 3, 1, 1, 3]
def baseStart_4341063 : Nat := 118140960795 + 4341063 * 2 ^ 59
def prefixEnd_4341063 : Nat := 4983230072969 + 3 ^ 40 * 4341063 * 2
def baseEnd_4341063 : Nat := 2229051870448854304748321

theorem tailTrace_4341063 : CollatzResearch.WordTrace tailWord_4341063 prefixEnd_4341063 2229051870448854304748321 := by
  unfold tailWord_4341063
  simp only [CollatzResearch.WordTrace]
  refine ⟨158331575072077620380075843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105554383381385080253383895 158331575072077620380075843)
  ·
    refine ⟨237497362608116430570113765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158331575072077620380075843 237497362608116430570113765)
    ·
      refine ⟨44530755489021830731896331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 237497362608116430570113765 44530755489021830731896331)
      ·
        refine ⟨66796133233532746097844497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44530755489021830731896331 66796133233532746097844497)
        ·
          refine ⟨50097099925149559573383373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66796133233532746097844497 50097099925149559573383373)
          ·
            refine ⟨18786412471931084840018765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50097099925149559573383373 18786412471931084840018765)
            ·
              refine ⟨7044904676974156815007037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18786412471931084840018765 7044904676974156815007037)
              ·
                refine ⟨2641839253865308805627639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7044904676974156815007037 2641839253865308805627639)
                ·
                  refine ⟨3962758880797963208441459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2641839253865308805627639 3962758880797963208441459)
                  ·
                    refine ⟨5944138321196944812662189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3962758880797963208441459 5944138321196944812662189)
                    ·
                      refine ⟨2229051870448854304748321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5944138321196944812662189 2229051870448854304748321)
                      ·
                        rfl

theorem cell23_4341063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 3, 3, 1, 1, 3].length) (baseStart_4341063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4341063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4341063 prefixEnd_4341063 := by exact prefixLift 4341063
  have htrace : WordTrace (prefixWord ++ tailWord_4341063) baseStart_4341063 baseEnd_4341063 := by
    simpa [prefixWord, tailWord_4341063, baseEnd_4341063] using wordTrace_append hprefix tailTrace_4341063
  have hstable : (prefixWord ++ tailWord_4341063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4341063).length < 2 ^ (prefixWord ++ tailWord_4341063).sum := by decide
  have hdescent : baseEnd_4341063 < baseStart_4341063 := by decide
  rcases family_descends (prefixWord ++ tailWord_4341063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4341079 : List Nat := [1, 1, 3, 2, 3, 2, 2, 1, 4, 4]
def baseStart_4341079 : Nat := 118140960795 + 4341079 * 2 ^ 59
def prefixEnd_4341079 : Nat := 4983230072969 + 3 ^ 40 * 4341079 * 2
def baseEnd_4341079 : Nat := 743020028713108747382749

theorem tailTrace_4341079 : CollatzResearch.WordTrace tailWord_4341079 prefixEnd_4341079 743020028713108747382749 := by
  unfold tailWord_4341079
  simp only [CollatzResearch.WordTrace]
  refine ⟨158332158640019655112658291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105554772426679770075105527 158332158640019655112658291)
  ·
    refine ⟨237498237960029482668987437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158332158640019655112658291 237498237960029482668987437)
    ·
      refine ⟨89061839235011056000870289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 237498237960029482668987437 89061839235011056000870289)
      ·
        refine ⟨66796379426258292000652717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89061839235011056000870289 66796379426258292000652717)
        ·
          refine ⟨25048642284846859500244769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 66796379426258292000652717 25048642284846859500244769)
          ·
            refine ⟨18786481713635144625183577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25048642284846859500244769 18786481713635144625183577)
            ·
              refine ⟨14089861285226358468887683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18786481713635144625183577 14089861285226358468887683)
              ·
                refine ⟨21134791927839537703331525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14089861285226358468887683 21134791927839537703331525)
                ·
                  refine ⟨3962773486469913319374661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21134791927839537703331525 3962773486469913319374661)
                  ·
                    refine ⟨743020028713108747382749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3962773486469913319374661 743020028713108747382749)
                    ·
                      rfl

theorem cell23_4341079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 2, 1, 4, 4].length) (baseStart_4341079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4341079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4341079 prefixEnd_4341079 := by exact prefixLift 4341079
  have htrace : WordTrace (prefixWord ++ tailWord_4341079) baseStart_4341079 baseEnd_4341079 := by
    simpa [prefixWord, tailWord_4341079, baseEnd_4341079] using wordTrace_append hprefix tailTrace_4341079
  have hstable : (prefixWord ++ tailWord_4341079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4341079).length < 2 ^ (prefixWord ++ tailWord_4341079).sum := by decide
  have hdescent : baseEnd_4341079 < baseStart_4341079 := by decide
  rcases family_descends (prefixWord ++ tailWord_4341079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4341082 : List Nat := [3, 1, 1, 2, 1, 2, 3, 2, 1, 1, 6]
def baseStart_4341082 : Nat := 118140960795 + 4341082 * 2 ^ 59
def prefixEnd_4341082 : Nat := 4983230072969 + 3 ^ 40 * 4341082 * 2
def baseEnd_4341082 : Nat := 2229061626581289730410733

theorem tailTrace_4341082 : CollatzResearch.WordTrace tailWord_4341082 prefixEnd_4341082 2229061626581289730410733 := by
  unfold tailWord_4341082
  simp only [CollatzResearch.WordTrace]
  refine ⟨39583067014752196656254375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105554845372672524416678333 39583067014752196656254375)
  ·
    refine ⟨59374600522128294984381563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39583067014752196656254375 59374600522128294984381563)
    ·
      refine ⟨89061900783192442476572345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59374600522128294984381563 89061900783192442476572345)
      ·
        refine ⟨66796425587394331857429259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89061900783192442476572345 66796425587394331857429259)
        ·
          refine ⟨100194638381091497786143889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66796425587394331857429259 100194638381091497786143889)
          ·
            refine ⟨75145978785818623339607917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 100194638381091497786143889 75145978785818623339607917)
            ·
              refine ⟨28179742044681983752352969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 75145978785818623339607917 28179742044681983752352969)
              ·
                refine ⟨21134806533511487814264727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28179742044681983752352969 21134806533511487814264727)
                ·
                  refine ⟨31702209800267231721397091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21134806533511487814264727 31702209800267231721397091)
                  ·
                    refine ⟨47553314700400847582095637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 31702209800267231721397091 47553314700400847582095637)
                    ·
                      refine ⟨2229061626581289730410733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 47553314700400847582095637 2229061626581289730410733)
                      ·
                        rfl

theorem cell23_4341082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 3, 2, 1, 1, 6].length) (baseStart_4341082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4341082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4341082 prefixEnd_4341082 := by exact prefixLift 4341082
  have htrace : WordTrace (prefixWord ++ tailWord_4341082) baseStart_4341082 baseEnd_4341082 := by
    simpa [prefixWord, tailWord_4341082, baseEnd_4341082] using wordTrace_append hprefix tailTrace_4341082
  have hstable : (prefixWord ++ tailWord_4341082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4341082).length < 2 ^ (prefixWord ++ tailWord_4341082).sum := by decide
  have hdescent : baseEnd_4341082 < baseStart_4341082 := by decide
  rcases family_descends (prefixWord ++ tailWord_4341082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4341092 : List Nat := [2, 3, 1, 1, 3, 2, 1, 10]
def baseStart_4341092 : Nat := 118140960795 + 4341092 * 2 ^ 59
def prefixEnd_4341092 : Nat := 4983230072969 + 3 ^ 40 * 4341092 * 2
def baseEnd_4341092 : Nat := 82558028199549433010581

theorem tailTrace_4341092 : CollatzResearch.WordTrace tailWord_4341092 prefixEnd_4341092 82558028199549433010581 := by
  unfold tailWord_4341092
  simp only [CollatzResearch.WordTrace]
  refine ⟨79166316394486279166440765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105555088525981705555254353 79166316394486279166440765)
  ·
    refine ⟨29687368647932354687415287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79166316394486279166440765 29687368647932354687415287)
    ·
      refine ⟨44531052971898532031122931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29687368647932354687415287 44531052971898532031122931)
      ·
        refine ⟨66796579457847798046684397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44531052971898532031122931 66796579457847798046684397)
        ·
          refine ⟨25048717296692924267506649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 66796579457847798046684397 25048717296692924267506649)
          ·
            refine ⟨18786537972519693200629987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25048717296692924267506649 18786537972519693200629987)
            ·
              refine ⟨28179806958779539800944981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18786537972519693200629987 28179806958779539800944981)
              ·
                refine ⟨82558028199549433010581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 28179806958779539800944981 82558028199549433010581)
                ·
                  rfl

theorem cell23_4341092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 1, 10].length) (baseStart_4341092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4341092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4341092 prefixEnd_4341092 := by exact prefixLift 4341092
  have htrace : WordTrace (prefixWord ++ tailWord_4341092) baseStart_4341092 baseEnd_4341092 := by
    simpa [prefixWord, tailWord_4341092, baseEnd_4341092] using wordTrace_append hprefix tailTrace_4341092
  have hstable : (prefixWord ++ tailWord_4341092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4341092).length < 2 ^ (prefixWord ++ tailWord_4341092).sum := by decide
  have hdescent : baseEnd_4341092 < baseStart_4341092 := by decide
  rcases family_descends (prefixWord ++ tailWord_4341092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4341123 : List Nat := [1, 1, 1, 3, 5, 2, 3, 1, 1, 2, 3]
def baseStart_4341123 : Nat := 118140960795 + 4341123 * 2 ^ 59
def prefixEnd_4341123 : Nat := 4983230072969 + 3 ^ 40 * 4341123 * 2
def baseEnd_4341123 : Nat := 2229082679288124069998045

theorem tailTrace_4341123 : CollatzResearch.WordTrace tailWord_4341123 prefixEnd_4341123 2229082679288124069998045 := by
  unfold tailWord_4341123
  simp only [CollatzResearch.WordTrace]
  refine ⟨158333763451860250627260023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105555842301240167084840015 158333763451860250627260023)
  ·
    refine ⟨237500645177790375940890035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158333763451860250627260023 237500645177790375940890035)
    ·
      refine ⟨356250967766685563911335053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 237500645177790375940890035 356250967766685563911335053)
      ·
        refine ⟨133594112912507086466750645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 356250967766685563911335053 133594112912507086466750645)
        ·
          refine ⟨12524448085547539356257873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 133594112912507086466750645 12524448085547539356257873)
          ·
            refine ⟨9393336064160654517193405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12524448085547539356257873 9393336064160654517193405)
            ·
              refine ⟨3522501024060245443947527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9393336064160654517193405 3522501024060245443947527)
              ·
                refine ⟨5283751536090368165921291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3522501024060245443947527 5283751536090368165921291)
                ·
                  refine ⟨7925627304135552248881937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5283751536090368165921291 7925627304135552248881937)
                  ·
                    refine ⟨5944220478101664186661453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7925627304135552248881937 5944220478101664186661453)
                    ·
                      refine ⟨2229082679288124069998045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5944220478101664186661453 2229082679288124069998045)
                      ·
                        rfl

theorem cell23_4341123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 3, 1, 1, 2, 3].length) (baseStart_4341123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4341123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4341123 prefixEnd_4341123 := by exact prefixLift 4341123
  have htrace : WordTrace (prefixWord ++ tailWord_4341123) baseStart_4341123 baseEnd_4341123 := by
    simpa [prefixWord, tailWord_4341123, baseEnd_4341123] using wordTrace_append hprefix tailTrace_4341123
  have hstable : (prefixWord ++ tailWord_4341123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4341123).length < 2 ^ (prefixWord ++ tailWord_4341123).sum := by decide
  have hdescent : baseEnd_4341123 < baseStart_4341123 := by decide
  rcases family_descends (prefixWord ++ tailWord_4341123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4341146 : List Nat := [3, 1, 1, 4, 1, 1, 1, 1, 5, 3, 2]
def baseStart_4341146 : Nat := 118140960795 + 4341146 * 2 ^ 59
def prefixEnd_4341146 : Nat := 4983230072969 + 3 ^ 40 * 4341146 * 2
def baseEnd_4341146 : Nat := 2229094489343177480010439

theorem tailTrace_4341146 : CollatzResearch.WordTrace tailWord_4341146 prefixEnd_4341146 2229094489343177480010439 := by
  unfold tailWord_4341146
  simp only [CollatzResearch.WordTrace]
  refine ⟨39583650582694231388836823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105556401553851283703564861 39583650582694231388836823)
  ·
    refine ⟨59375475874041347083255235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39583650582694231388836823 59375475874041347083255235)
    ·
      refine ⟨89063213811062020624882853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59375475874041347083255235 89063213811062020624882853)
      ·
        refine ⟨16699352589574128867165535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 89063213811062020624882853 16699352589574128867165535)
        ·
          refine ⟨25049028884361193300748303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16699352589574128867165535 25049028884361193300748303)
          ·
            refine ⟨37573543326541789951122455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25049028884361193300748303 37573543326541789951122455)
            ·
              refine ⟨56360314989812684926683683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37573543326541789951122455 56360314989812684926683683)
              ·
                refine ⟨84540472484719027390025525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56360314989812684926683683 84540472484719027390025525)
                ·
                  refine ⟨7925669295442408817814893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 84540472484719027390025525 7925669295442408817814893)
                  ·
                    refine ⟨2972125985790903306680585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7925669295442408817814893 2972125985790903306680585)
                    ·
                      refine ⟨2229094489343177480010439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2972125985790903306680585 2229094489343177480010439)
                      ·
                        rfl

theorem cell23_4341146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 1, 5, 3, 2].length) (baseStart_4341146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4341146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4341146 prefixEnd_4341146 := by exact prefixLift 4341146
  have htrace : WordTrace (prefixWord ++ tailWord_4341146) baseStart_4341146 baseEnd_4341146 := by
    simpa [prefixWord, tailWord_4341146, baseEnd_4341146] using wordTrace_append hprefix tailTrace_4341146
  have hstable : (prefixWord ++ tailWord_4341146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4341146).length < 2 ^ (prefixWord ++ tailWord_4341146).sum := by decide
  have hdescent : baseEnd_4341146 < baseStart_4341146 := by decide
  rcases family_descends (prefixWord ++ tailWord_4341146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4341159 : List Nat := [1, 1, 6, 1, 1, 1, 1, 2, 2, 3, 4]
def baseStart_4341159 : Nat := 118140960795 + 4341159 * 2 ^ 59
def prefixEnd_4341159 : Nat := 4983230072969 + 3 ^ 40 * 4341159 * 2
def baseEnd_4341159 : Nat := 2229101164591685929147879

theorem tailTrace_4341159 : CollatzResearch.WordTrace tailWord_4341159 prefixEnd_4341159 2229101164591685929147879 := by
  unfold tailWord_4341159
  simp only [CollatzResearch.WordTrace]
  refine ⟨158335076479729828775570531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105556717653153219183713687 158335076479729828775570531)
  ·
    refine ⟨237502614719594743163355797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158335076479729828775570531 237502614719594743163355797)
    ·
      refine ⟨11132935064981003585782303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 237502614719594743163355797 11132935064981003585782303)
      ·
        refine ⟨16699402597471505378673455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11132935064981003585782303 16699402597471505378673455)
        ·
          refine ⟨25049103896207258068010183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16699402597471505378673455 25049103896207258068010183)
          ·
            refine ⟨37573655844310887102015275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25049103896207258068010183 37573655844310887102015275)
            ·
              refine ⟨56360483766466330653022913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37573655844310887102015275 56360483766466330653022913)
              ·
                refine ⟨42270362824849747989767185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 56360483766466330653022913 42270362824849747989767185)
                ·
                  refine ⟨31702772118637310992325389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 42270362824849747989767185 31702772118637310992325389)
                  ·
                    refine ⟨11888539544488991622122021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 31702772118637310992325389 11888539544488991622122021)
                    ·
                      refine ⟨2229101164591685929147879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11888539544488991622122021 2229101164591685929147879)
                      ·
                        rfl

theorem cell23_4341159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 2, 2, 3, 4].length) (baseStart_4341159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4341159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4341159 prefixEnd_4341159 := by exact prefixLift 4341159
  have htrace : WordTrace (prefixWord ++ tailWord_4341159) baseStart_4341159 baseEnd_4341159 := by
    simpa [prefixWord, tailWord_4341159, baseEnd_4341159] using wordTrace_append hprefix tailTrace_4341159
  have hstable : (prefixWord ++ tailWord_4341159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4341159).length < 2 ^ (prefixWord ++ tailWord_4341159).sum := by decide
  have hdescent : baseEnd_4341159 < baseStart_4341159 := by decide
  rcases family_descends (prefixWord ++ tailWord_4341159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4341176 : List Nat := [2, 1, 2, 1, 2, 2, 4, 2, 1, 4, 2]
def baseStart_4341176 : Nat := 118140960795 + 4341176 * 2 ^ 59
def prefixEnd_4341176 : Nat := 4983230072969 + 3 ^ 40 * 4341176 * 2
def baseEnd_4341176 : Nat := 2229109893762812362635301

theorem tailTrace_4341176 : CollatzResearch.WordTrace tailWord_4341176 prefixEnd_4341176 2229109893762812362635301 := by
  unfold tailWord_4341176
  simp only [CollatzResearch.WordTrace]
  refine ⟨79167848260334120339469691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105557131013778827119292921 79167848260334120339469691)
  ·
    refine ⟨118751772390501180509204537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79167848260334120339469691 118751772390501180509204537)
    ·
      refine ⟨89063829292875885381903403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 118751772390501180509204537 89063829292875885381903403)
      ·
        refine ⟨133595743939313828072855105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89063829292875885381903403 133595743939313828072855105)
        ·
          refine ⟨100196807954485371054641329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 133595743939313828072855105 100196807954485371054641329)
          ·
            refine ⟨75147605965864028290980997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 100196807954485371054641329 75147605965864028290980997)
            ·
              refine ⟨14090176118599505304558937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 75147605965864028290980997 14090176118599505304558937)
              ·
                refine ⟨10567632088949628978419203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14090176118599505304558937 10567632088949628978419203)
                ·
                  refine ⟨15851448133424443467628805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10567632088949628978419203 15851448133424443467628805)
                  ·
                    refine ⟨2972146525017083150180401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15851448133424443467628805 2972146525017083150180401)
                    ·
                      refine ⟨2229109893762812362635301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2972146525017083150180401 2229109893762812362635301)
                      ·
                        rfl

theorem cell23_4341176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 4, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 4, 2, 1, 4, 2].length) (baseStart_4341176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4341176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4341176 prefixEnd_4341176 := by exact prefixLift 4341176
  have htrace : WordTrace (prefixWord ++ tailWord_4341176) baseStart_4341176 baseEnd_4341176 := by
    simpa [prefixWord, tailWord_4341176, baseEnd_4341176] using wordTrace_append hprefix tailTrace_4341176
  have hstable : (prefixWord ++ tailWord_4341176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4341176).length < 2 ^ (prefixWord ++ tailWord_4341176).sum := by decide
  have hdescent : baseEnd_4341176 < baseStart_4341176 := by decide
  rcases family_descends (prefixWord ++ tailWord_4341176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4341180 : List Nat := [2, 2, 2, 4, 2, 1, 1, 3, 1, 3, 2]
def baseStart_4341180 : Nat := 118140960795 + 4341180 * 2 ^ 59
def prefixEnd_4341180 : Nat := 4983230072969 + 3 ^ 40 * 4341180 * 2
def baseEnd_4341180 : Nat := 2229111947685430346985283

theorem tailTrace_4341180 : CollatzResearch.WordTrace tailWord_4341180 prefixEnd_4341180 2229111947685430346985283 := by
  unfold tailWord_4341180
  simp only [CollatzResearch.WordTrace]
  refine ⟨79167921206326874681042497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105557228275102499574723329 79167921206326874681042497)
  ·
    refine ⟨59375940904745156010781873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79167921206326874681042497 59375940904745156010781873)
    ·
      refine ⟨44531955678558867008086405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59375940904745156010781873 44531955678558867008086405)
      ·
        refine ⟨8349741689729787564016201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 44531955678558867008086405 8349741689729787564016201)
        ·
          refine ⟨6262306267297340673012151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8349741689729787564016201 6262306267297340673012151)
          ·
            refine ⟨9393459400946011009518227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6262306267297340673012151 9393459400946011009518227)
            ·
              refine ⟨14090189101419016514277341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9393459400946011009518227 14090189101419016514277341)
              ·
                refine ⟨5283820913032131192854003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14090189101419016514277341 5283820913032131192854003)
                ·
                  refine ⟨7925731369548196789281005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5283820913032131192854003 7925731369548196789281005)
                  ·
                    refine ⟨2972149263580573795980377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7925731369548196789281005 2972149263580573795980377)
                    ·
                      refine ⟨2229111947685430346985283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2972149263580573795980377 2229111947685430346985283)
                      ·
                        rfl

theorem cell23_4341180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 1, 3, 1, 3, 2].length) (baseStart_4341180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4341180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4341180 prefixEnd_4341180 := by exact prefixLift 4341180
  have htrace : WordTrace (prefixWord ++ tailWord_4341180) baseStart_4341180 baseEnd_4341180 := by
    simpa [prefixWord, tailWord_4341180, baseEnd_4341180] using wordTrace_append hprefix tailTrace_4341180
  have hstable : (prefixWord ++ tailWord_4341180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4341180).length < 2 ^ (prefixWord ++ tailWord_4341180).sum := by decide
  have hdescent : baseEnd_4341180 < baseStart_4341180 := by decide
  rcases family_descends (prefixWord ++ tailWord_4341180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4341233 : List Nat := [1, 2, 2, 2, 3, 4, 1, 3, 5]
def baseStart_4341233 : Nat := 118140960795 + 4341233 * 2 ^ 59
def prefixEnd_4341233 : Nat := 4983230072969 + 3 ^ 40 * 4341233 * 2
def baseEnd_4341233 : Nat := 247682129128902071069171

theorem tailTrace_4341233 : CollatzResearch.WordTrace tailWord_4341233 prefixEnd_4341233 247682129128902071069171 := by
  unfold tailWord_4341233
  simp only [CollatzResearch.WordTrace]
  refine ⟨158337775481461739413764353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105558516987641159609176235 158337775481461739413764353)
  ·
    refine ⟨118753331611096304560323265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 158337775481461739413764353 118753331611096304560323265)
    ·
      refine ⟨89064998708322228420242449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 118753331611096304560323265 89064998708322228420242449)
      ·
        refine ⟨66798749031241671315181837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89064998708322228420242449 66798749031241671315181837)
        ·
          refine ⟨25049530886715626743193189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 66798749031241671315181837 25049530886715626743193189)
          ·
            refine ⟨4696787041259180014348723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25049530886715626743193189 4696787041259180014348723)
            ·
              refine ⟨7045180561888770021523085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4696787041259180014348723 7045180561888770021523085)
              ·
                refine ⟨2641942710708288758071157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7045180561888770021523085 2641942710708288758071157)
                ·
                  refine ⟨247682129128902071069171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2641942710708288758071157 247682129128902071069171)
                  ·
                    rfl

theorem cell23_4341233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 4, 1, 3, 5].length) (baseStart_4341233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4341233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4341233 prefixEnd_4341233 := by exact prefixLift 4341233
  have htrace : WordTrace (prefixWord ++ tailWord_4341233) baseStart_4341233 baseEnd_4341233 := by
    simpa [prefixWord, tailWord_4341233, baseEnd_4341233] using wordTrace_append hprefix tailTrace_4341233
  have hstable : (prefixWord ++ tailWord_4341233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4341233).length < 2 ^ (prefixWord ++ tailWord_4341233).sum := by decide
  have hdescent : baseEnd_4341233 < baseStart_4341233 := by decide
  rcases family_descends (prefixWord ++ tailWord_4341233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4341276 : List Nat := [2, 2, 3, 1, 2, 1, 2, 1, 5, 4]
def baseStart_4341276 : Nat := 118140960795 + 4341276 * 2 ^ 59
def prefixEnd_4341276 : Nat := 4983230072969 + 3 ^ 40 * 4341276 * 2
def baseEnd_4341276 : Nat := 743053747276087323794947

theorem tailTrace_4341276 : CollatzResearch.WordTrace tailWord_4341276 prefixEnd_4341276 743053747276087323794947 := by
  unfold tailWord_4341276
  simp only [CollatzResearch.WordTrace]
  refine ⟨79169671910152978878789841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105559562546870638505053121 79169671910152978878789841)
  ·
    refine ⟨59377253932614734159092381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79169671910152978878789841 59377253932614734159092381)
    ·
      refine ⟨22266470224730525309659643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59377253932614734159092381 22266470224730525309659643)
      ·
        refine ⟨33399705337095787964489465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22266470224730525309659643 33399705337095787964489465)
        ·
          refine ⟨25049779002821840973367099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33399705337095787964489465 25049779002821840973367099)
          ·
            refine ⟨37574668504232761460050649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25049779002821840973367099 37574668504232761460050649)
            ·
              refine ⟨28181001378174571095037987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37574668504232761460050649 28181001378174571095037987)
              ·
                refine ⟨42271502067261856642556981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28181001378174571095037987 42271502067261856642556981)
                ·
                  refine ⟨3962953318805799060239717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 42271502067261856642556981 3962953318805799060239717)
                  ·
                    refine ⟨743053747276087323794947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3962953318805799060239717 743053747276087323794947)
                    ·
                      rfl

theorem cell23_4341276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 2, 1, 5, 4].length) (baseStart_4341276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4341276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4341276 prefixEnd_4341276 := by exact prefixLift 4341276
  have htrace : WordTrace (prefixWord ++ tailWord_4341276) baseStart_4341276 baseEnd_4341276 := by
    simpa [prefixWord, tailWord_4341276, baseEnd_4341276] using wordTrace_append hprefix tailTrace_4341276
  have hstable : (prefixWord ++ tailWord_4341276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4341276).length < 2 ^ (prefixWord ++ tailWord_4341276).sum := by decide
  have hdescent : baseEnd_4341276 < baseStart_4341276 := by decide
  rcases family_descends (prefixWord ++ tailWord_4341276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4341279 : List Nat := [1, 1, 2, 4, 1, 1, 2, 1, 2, 4, 4]
def baseStart_4341279 : Nat := 118140960795 + 4341279 * 2 ^ 59
def prefixEnd_4341279 : Nat := 4983230072969 + 3 ^ 40 * 4341279 * 2
def baseEnd_4341279 : Nat := 2229162782270225459647327

theorem tailTrace_4341279 : CollatzResearch.WordTrace tailWord_4341279 prefixEnd_4341279 2229162782270225459647327 := by
  unfold tailWord_4341279
  simp only [CollatzResearch.WordTrace]
  refine ⟨158339453239295089269938891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105559635492863392846625927 158339453239295089269938891)
  ·
    refine ⟨237509179858942633904908337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158339453239295089269938891 237509179858942633904908337)
    ·
      refine ⟨178131884894206975428681253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 237509179858942633904908337 178131884894206975428681253)
      ·
        refine ⟨33399728417663807892877735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 178131884894206975428681253 33399728417663807892877735)
        ·
          refine ⟨50099592626495711839316603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33399728417663807892877735 50099592626495711839316603)
          ·
            refine ⟨75149388939743567758974905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50099592626495711839316603 75149388939743567758974905)
            ·
              refine ⟨56362041704807675819231179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 75149388939743567758974905 56362041704807675819231179)
              ·
                refine ⟨84543062557211513728846769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56362041704807675819231179 84543062557211513728846769)
                ·
                  refine ⟨63407296917908635296635077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 84543062557211513728846769 63407296917908635296635077)
                  ·
                    refine ⟨11888868172107869118119077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 63407296917908635296635077 11888868172107869118119077)
                    ·
                      refine ⟨2229162782270225459647327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11888868172107869118119077 2229162782270225459647327)
                      ·
                        rfl

theorem cell23_4341279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 1, 2, 4, 4].length) (baseStart_4341279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4341279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4341279 prefixEnd_4341279 := by exact prefixLift 4341279
  have htrace : WordTrace (prefixWord ++ tailWord_4341279) baseStart_4341279 baseEnd_4341279 := by
    simpa [prefixWord, tailWord_4341279, baseEnd_4341279] using wordTrace_append hprefix tailTrace_4341279
  have hstable : (prefixWord ++ tailWord_4341279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4341279).length < 2 ^ (prefixWord ++ tailWord_4341279).sum := by decide
  have hdescent : baseEnd_4341279 < baseStart_4341279 := by decide
  rcases family_descends (prefixWord ++ tailWord_4341279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4341283 : List Nat := [1, 1, 1, 4, 5, 1, 2, 1, 2, 1, 4]
def baseStart_4341283 : Nat := 118140960795 + 4341283 * 2 ^ 59
def prefixEnd_4341283 : Nat := 4983230072969 + 3 ^ 40 * 4341283 * 2
def baseEnd_4341283 : Nat := 2229164836192843443997309

theorem tailTrace_4341283 : CollatzResearch.WordTrace tailWord_4341283 prefixEnd_4341283 2229164836192843443997309 := by
  unfold tailWord_4341283
  simp only [CollatzResearch.WordTrace]
  refine ⟨158339599131280597953084503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105559732754187065302056335 158339599131280597953084503)
  ·
    refine ⟨237509398696920896929626755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158339599131280597953084503 237509398696920896929626755)
    ·
      refine ⟨356264098045381345394440133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 237509398696920896929626755 356264098045381345394440133)
      ·
        refine ⟨66799518383509002261457525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 356264098045381345394440133 66799518383509002261457525)
        ·
          refine ⟨6262454848453968962011643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 66799518383509002261457525 6262454848453968962011643)
          ·
            refine ⟨9393682272680953443017465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6262454848453968962011643 9393682272680953443017465)
            ·
              refine ⟨7045261704510715082263099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9393682272680953443017465 7045261704510715082263099)
              ·
                refine ⟨10567892556766072623394649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7045261704510715082263099 10567892556766072623394649)
                ·
                  refine ⟨7925919417574554467545987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10567892556766072623394649 7925919417574554467545987)
                  ·
                    refine ⟨11888879126361831701318981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7925919417574554467545987 11888879126361831701318981)
                    ·
                      refine ⟨2229164836192843443997309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11888879126361831701318981 2229164836192843443997309)
                      ·
                        rfl

theorem cell23_4341283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 2, 1, 2, 1, 4].length) (baseStart_4341283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4341283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4341283 prefixEnd_4341283 := by exact prefixLift 4341283
  have htrace : WordTrace (prefixWord ++ tailWord_4341283) baseStart_4341283 baseEnd_4341283 := by
    simpa [prefixWord, tailWord_4341283, baseEnd_4341283] using wordTrace_append hprefix tailTrace_4341283
  have hstable : (prefixWord ++ tailWord_4341283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4341283).length < 2 ^ (prefixWord ++ tailWord_4341283).sum := by decide
  have hdescent : baseEnd_4341283 < baseStart_4341283 := by decide
  rcases family_descends (prefixWord ++ tailWord_4341283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4341306 : List Nat := [3, 1, 1, 1, 3, 2, 4, 2, 6]
def baseStart_4341306 : Nat := 118140960795 + 4341306 * 2 ^ 59
def prefixEnd_4341306 : Nat := 4983230072969 + 3 ^ 40 * 4341306 * 2
def baseEnd_4341306 : Nat := 247686294027544094889967

theorem tailTrace_4341306 : CollatzResearch.WordTrace tailWord_4341306 prefixEnd_4341306 247686294027544094889967 := by
  unfold tailWord_4341306
  simp only [CollatzResearch.WordTrace]
  refine ⟨39585109502549318220292943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105560292006798181920781181 39585109502549318220292943)
  ·
    refine ⟨59377664253823977330439415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39585109502549318220292943 59377664253823977330439415)
    ·
      refine ⟨89066496380735965995659123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59377664253823977330439415 89066496380735965995659123)
      ·
        refine ⟨133599744571103948993488685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89066496380735965995659123 133599744571103948993488685)
        ·
          refine ⟨50099904214163980872558257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 133599744571103948993488685 50099904214163980872558257)
          ·
            refine ⟨37574928160622985654418693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50099904214163980872558257 37574928160622985654418693)
            ·
              refine ⟨7045299030116809810203505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 37574928160622985654418693 7045299030116809810203505)
              ·
                refine ⟨5283974272587607357652629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7045299030116809810203505 5283974272587607357652629)
                ·
                  refine ⟨247686294027544094889967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5283974272587607357652629 247686294027544094889967)
                  ·
                    rfl

theorem cell23_4341306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 4, 2, 6].length) (baseStart_4341306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4341306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4341306 prefixEnd_4341306 := by exact prefixLift 4341306
  have htrace : WordTrace (prefixWord ++ tailWord_4341306) baseStart_4341306 baseEnd_4341306 := by
    simpa [prefixWord, tailWord_4341306, baseEnd_4341306] using wordTrace_append hprefix tailTrace_4341306
  have hstable : (prefixWord ++ tailWord_4341306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4341306).length < 2 ^ (prefixWord ++ tailWord_4341306).sum := by decide
  have hdescent : baseEnd_4341306 < baseStart_4341306 := by decide
  rcases family_descends (prefixWord ++ tailWord_4341306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4341329 : List Nat := [1, 2, 2, 1, 3, 2, 1, 1, 2, 1, 7]
def baseStart_4341329 : Nat := 118140960795 + 4341329 * 2 ^ 59
def prefixEnd_4341329 : Nat := 4983230072969 + 3 ^ 40 * 4341329 * 2
def baseEnd_4341329 : Nat := 2229188456302950264022097

theorem tailTrace_4341329 : CollatzResearch.WordTrace tailWord_4341329 prefixEnd_4341329 2229188456302950264022097 := by
  unfold tailWord_4341329
  simp only [CollatzResearch.WordTrace]
  refine ⟨158341276889113947809259041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105560851259409298539506027 158341276889113947809259041)
  ·
    refine ⟨118755957666835460856944281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 158341276889113947809259041 118755957666835460856944281)
    ·
      refine ⟨89066968250126595642708211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 118755957666835460856944281 89066968250126595642708211)
      ·
        refine ⟨133600452375189893464062317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89066968250126595642708211 133600452375189893464062317)
        ·
          refine ⟨50100169640696210049023369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 133600452375189893464062317 50100169640696210049023369)
          ·
            refine ⟨37575127230522157536767527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50100169640696210049023369 37575127230522157536767527)
            ·
              refine ⟨56362690845783236305151291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37575127230522157536767527 56362690845783236305151291)
              ·
                refine ⟨84544036268674854457726937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56362690845783236305151291 84544036268674854457726937)
                ·
                  refine ⟨63408027201506140843295203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 84544036268674854457726937 63408027201506140843295203)
                  ·
                    refine ⟨95112040802259211264942805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 63408027201506140843295203 95112040802259211264942805)
                    ·
                      refine ⟨2229188456302950264022097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 95112040802259211264942805 2229188456302950264022097)
                      ·
                        rfl

theorem cell23_4341329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 1, 2, 1, 7].length) (baseStart_4341329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4341329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4341329 prefixEnd_4341329 := by exact prefixLift 4341329
  have htrace : WordTrace (prefixWord ++ tailWord_4341329) baseStart_4341329 baseEnd_4341329 := by
    simpa [prefixWord, tailWord_4341329, baseEnd_4341329] using wordTrace_append hprefix tailTrace_4341329
  have hstable : (prefixWord ++ tailWord_4341329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4341329).length < 2 ^ (prefixWord ++ tailWord_4341329).sum := by decide
  have hdescent : baseEnd_4341329 < baseStart_4341329 := by decide
  rcases family_descends (prefixWord ++ tailWord_4341329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4341334 : List Nat := [5, 2, 2, 2, 1, 2, 1, 1, 2, 1, 4]
def baseStart_4341334 : Nat := 118140960795 + 4341334 * 2 ^ 59
def prefixEnd_4341334 : Nat := 4983230072969 + 3 ^ 40 * 4341334 * 2
def baseEnd_4341334 : Nat := 2229191023706222744459575

theorem tailTrace_4341334 : CollatzResearch.WordTrace tailWord_4341334 prefixEnd_4341334 2229191023706222744459575 := by
  unfold tailWord_4341334
  simp only [CollatzResearch.WordTrace]
  refine ⟨9896341203380989603949441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 105560972836063889108794037 9896341203380989603949441)
  ·
    refine ⟨7422255902535742202962081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9896341203380989603949441 7422255902535742202962081)
    ·
      refine ⟨5566691926901806652221561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7422255902535742202962081 5566691926901806652221561)
      ·
        refine ⟨4175018945176354989166171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5566691926901806652221561 4175018945176354989166171)
        ·
          refine ⟨6262528417764532483749257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4175018945176354989166171 6262528417764532483749257)
          ·
            refine ⟨4696896313323399362811943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6262528417764532483749257 4696896313323399362811943)
            ·
              refine ⟨7045344469985099044217915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4696896313323399362811943 7045344469985099044217915)
              ·
                refine ⟨10568016704977648566326873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7045344469985099044217915 10568016704977648566326873)
                ·
                  refine ⟨7926012528733236424745155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10568016704977648566326873 7926012528733236424745155)
                  ·
                    refine ⟨11889018793099854637117733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7926012528733236424745155 11889018793099854637117733)
                    ·
                      refine ⟨2229191023706222744459575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11889018793099854637117733 2229191023706222744459575)
                      ·
                        rfl

theorem cell23_4341334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 2, 1, 1, 2, 1, 4].length) (baseStart_4341334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4341334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4341334 prefixEnd_4341334 := by exact prefixLift 4341334
  have htrace : WordTrace (prefixWord ++ tailWord_4341334) baseStart_4341334 baseEnd_4341334 := by
    simpa [prefixWord, tailWord_4341334, baseEnd_4341334] using wordTrace_append hprefix tailTrace_4341334
  have hstable : (prefixWord ++ tailWord_4341334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4341334).length < 2 ^ (prefixWord ++ tailWord_4341334).sum := by decide
  have hdescent : baseEnd_4341334 < baseStart_4341334 := by decide
  rcases family_descends (prefixWord ++ tailWord_4341334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4341336 : List Nat := [2, 1, 2, 2, 1, 2, 1, 6, 1, 5]
def baseStart_4341336 : Nat := 118140960795 + 4341336 * 2 ^ 59
def prefixEnd_4341336 : Nat := 4983230072969 + 3 ^ 40 * 4341336 * 2
def baseEnd_4341336 : Nat := 743064016889177245544855

theorem tailTrace_4341336 : CollatzResearch.WordTrace tailWord_4341336 prefixEnd_4341336 743064016889177245544855 := by
  unfold tailWord_4341336
  simp only [CollatzResearch.WordTrace]
  refine ⟨79170766100044294002381931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105561021466725725336509241 79170766100044294002381931)
  ·
    refine ⟨118756149150066441003572897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79170766100044294002381931 118756149150066441003572897)
    ·
      refine ⟨89067111862549830752679673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 118756149150066441003572897 89067111862549830752679673)
      ·
        refine ⟨66800333896912373064509755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89067111862549830752679673 66800333896912373064509755)
        ·
          refine ⟨100200500845368559596764633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66800333896912373064509755 100200500845368559596764633)
          ·
            refine ⟨75150375634026419697573475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 100200500845368559596764633 75150375634026419697573475)
            ·
              refine ⟨112725563451039629546360213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75150375634026419697573475 112725563451039629546360213)
              ·
                refine ⟨5284010786767482634985635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 112725563451039629546360213 5284010786767482634985635)
                ·
                  refine ⟨7926016180151223952478453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5284010786767482634985635 7926016180151223952478453)
                  ·
                    refine ⟨743064016889177245544855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7926016180151223952478453 743064016889177245544855)
                    ·
                      rfl

theorem cell23_4341336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 6, 1, 5].length) (baseStart_4341336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4341336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4341336 prefixEnd_4341336 := by exact prefixLift 4341336
  have htrace : WordTrace (prefixWord ++ tailWord_4341336) baseStart_4341336 baseEnd_4341336 := by
    simpa [prefixWord, tailWord_4341336, baseEnd_4341336] using wordTrace_append hprefix tailTrace_4341336
  have hstable : (prefixWord ++ tailWord_4341336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4341336).length < 2 ^ (prefixWord ++ tailWord_4341336).sum := by decide
  have hdescent : baseEnd_4341336 < baseStart_4341336 := by decide
  rcases family_descends (prefixWord ++ tailWord_4341336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4341353 : List Nat := [1, 2, 1, 1, 1, 4, 6, 1, 1, 5]
def baseStart_4341353 : Nat := 118140960795 + 4341353 * 2 ^ 59
def prefixEnd_4341353 : Nat := 4983230072969 + 3 ^ 40 * 4341353 * 2
def baseEnd_4341353 : Nat := 743066926612886056707329

theorem tailTrace_4341353 : CollatzResearch.WordTrace tailWord_4341353 prefixEnd_4341353 743066926612886056707329 := by
  unfold tailWord_4341353
  simp only [CollatzResearch.WordTrace]
  refine ⟨158342152241026999908132713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105561434827351333272088475 158342152241026999908132713)
  ·
    refine ⟨118756614180770249931099535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 158342152241026999908132713 118756614180770249931099535)
    ·
      refine ⟨178134921271155374896649303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118756614180770249931099535 178134921271155374896649303)
      ·
        refine ⟨267202381906733062344973955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 178134921271155374896649303 267202381906733062344973955)
        ·
          refine ⟨400803572860099593517460933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 267202381906733062344973955 400803572860099593517460933)
          ·
            refine ⟨75150669911268673784523925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 400803572860099593517460933 75150669911268673784523925)
            ·
              refine ⟨3522687652090719083649559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 75150669911268673784523925 3522687652090719083649559)
              ·
                refine ⟨5284031478136078625474339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3522687652090719083649559 5284031478136078625474339)
                ·
                  refine ⟨7926047217204117938211509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5284031478136078625474339 7926047217204117938211509)
                  ·
                    refine ⟨743066926612886056707329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7926047217204117938211509 743066926612886056707329)
                    ·
                      rfl

theorem cell23_4341353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 6, 1, 1, 5].length) (baseStart_4341353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4341353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4341353 prefixEnd_4341353 := by exact prefixLift 4341353
  have htrace : WordTrace (prefixWord ++ tailWord_4341353) baseStart_4341353 baseEnd_4341353 := by
    simpa [prefixWord, tailWord_4341353, baseEnd_4341353] using wordTrace_append hprefix tailTrace_4341353
  have hstable : (prefixWord ++ tailWord_4341353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4341353).length < 2 ^ (prefixWord ++ tailWord_4341353).sum := by decide
  have hdescent : baseEnd_4341353 < baseStart_4341353 := by decide
  rcases family_descends (prefixWord ++ tailWord_4341353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4341376 : List Nat := [2, 1, 1, 2, 1, 4, 3, 2, 1, 1, 5]
def baseStart_4341376 : Nat := 118140960795 + 4341376 * 2 ^ 59
def prefixEnd_4341376 : Nat := 4983230072969 + 3 ^ 40 * 4341376 * 2
def baseEnd_4341376 : Nat := 2229212589893711580134381

theorem tailTrace_4341376 : CollatzResearch.WordTrace tailWord_4341376 prefixEnd_4341376 2229212589893711580134381 := by
  unfold tailWord_4341376
  simp only [CollatzResearch.WordTrace]
  refine ⟨79171495559971837418109991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105561994079962449890813321 79171495559971837418109991)
  ·
    refine ⟨118757243339957756127164987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79171495559971837418109991 118757243339957756127164987)
    ·
      refine ⟨178135865009936634190747481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118757243339957756127164987 178135865009936634190747481)
      ·
        refine ⟨133601898757452475643060611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 178135865009936634190747481 133601898757452475643060611)
        ·
          refine ⟨200402848136178713464590917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 133601898757452475643060611 200402848136178713464590917)
          ·
            refine ⟨37575534025533508774610797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 200402848136178713464590917 37575534025533508774610797)
            ·
              refine ⟨14090825259575065790479049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37575534025533508774610797 14090825259575065790479049)
              ·
                refine ⟨10568118944681299342859287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14090825259575065790479049 10568118944681299342859287)
                ·
                  refine ⟨15852178417021949014288931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10568118944681299342859287 15852178417021949014288931)
                  ·
                    refine ⟨23778267625532923521433397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15852178417021949014288931 23778267625532923521433397)
                    ·
                      refine ⟨2229212589893711580134381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23778267625532923521433397 2229212589893711580134381)
                      ·
                        rfl

theorem cell23_4341376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 3, 2, 1, 1, 5].length) (baseStart_4341376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4341376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4341376 prefixEnd_4341376 := by exact prefixLift 4341376
  have htrace : WordTrace (prefixWord ++ tailWord_4341376) baseStart_4341376 baseEnd_4341376 := by
    simpa [prefixWord, tailWord_4341376, baseEnd_4341376] using wordTrace_append hprefix tailTrace_4341376
  have hstable : (prefixWord ++ tailWord_4341376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4341376).length < 2 ^ (prefixWord ++ tailWord_4341376).sum := by decide
  have hdescent : baseEnd_4341376 < baseStart_4341376 := by decide
  rcases family_descends (prefixWord ++ tailWord_4341376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4341379 : List Nat := [1, 1, 1, 3, 3, 1, 1, 12]
def baseStart_4341379 : Nat := 118140960795 + 4341379 * 2 ^ 59
def prefixEnd_4341379 : Nat := 4983230072969 + 3 ^ 40 * 4341379 * 2
def baseEnd_4341379 : Nat := 82563486308728706236921

theorem tailTrace_4341379 : CollatzResearch.WordTrace tailWord_4341379 prefixEnd_4341379 82563486308728706236921 := by
  unfold tailWord_4341379
  simp only [CollatzResearch.WordTrace]
  refine ⟨158343100538932806348579191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105562067025955204232386127 158343100538932806348579191)
  ·
    refine ⟨237514650808399209522868787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158343100538932806348579191 237514650808399209522868787)
    ·
      refine ⟨356271976212598814284303181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 237514650808399209522868787 356271976212598814284303181)
      ·
        refine ⟨133601991079724555356613693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 356271976212598814284303181 133601991079724555356613693)
        ·
          refine ⟨50100746654896708258730135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 133601991079724555356613693 50100746654896708258730135)
          ·
            refine ⟨75151119982345062388095203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50100746654896708258730135 75151119982345062388095203)
            ·
              refine ⟨112726679973517593582142805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75151119982345062388095203 112726679973517593582142805)
              ·
                refine ⟨82563486308728706236921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 112726679973517593582142805 82563486308728706236921)
                ·
                  rfl

theorem cell23_4341379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 12].length) (baseStart_4341379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4341379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4341379 prefixEnd_4341379 := by exact prefixLift 4341379
  have htrace : WordTrace (prefixWord ++ tailWord_4341379) baseStart_4341379 baseEnd_4341379 := by
    simpa [prefixWord, tailWord_4341379, baseEnd_4341379] using wordTrace_append hprefix tailTrace_4341379
  have hstable : (prefixWord ++ tailWord_4341379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4341379).length < 2 ^ (prefixWord ++ tailWord_4341379).sum := by decide
  have hdescent : baseEnd_4341379 < baseStart_4341379 := by decide
  rcases family_descends (prefixWord ++ tailWord_4341379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4341383 : List Nat := [1, 1, 4, 2, 1, 5, 1, 1, 1, 6]
def baseStart_4341383 : Nat := 118140960795 + 4341383 * 2 ^ 59
def prefixEnd_4341383 : Nat := 4983230072969 + 3 ^ 40 * 4341383 * 2
def baseEnd_4341383 : Nat := 743072061419431017582283

theorem tailTrace_4341383 : CollatzResearch.WordTrace tailWord_4341383 prefixEnd_4341383 743072061419431017582283 := by
  unfold tailWord_4341383
  simp only [CollatzResearch.WordTrace]
  refine ⟨158343246430918315031724803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105562164287278876687816535 158343246430918315031724803)
  ·
    refine ⟨237514869646377472547587205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158343246430918315031724803 237514869646377472547587205)
    ·
      refine ⟨44534038058695776102672601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 237514869646377472547587205 44534038058695776102672601)
      ·
        refine ⟨33400528544021832077004451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44534038058695776102672601 33400528544021832077004451)
        ·
          refine ⟨50100792816032748115506677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33400528544021832077004451 50100792816032748115506677)
          ·
            refine ⟨4696949326503070135828751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 50100792816032748115506677 4696949326503070135828751)
            ·
              refine ⟨7045423989754605203743127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4696949326503070135828751 7045423989754605203743127)
              ·
                refine ⟨10568135984631907805614691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7045423989754605203743127 10568135984631907805614691)
                ·
                  refine ⟨15852203976947861708422037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10568135984631907805614691 15852203976947861708422037)
                  ·
                    refine ⟨743072061419431017582283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15852203976947861708422037 743072061419431017582283)
                    ·
                      rfl

theorem cell23_4341383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 5, 1, 1, 1, 6].length) (baseStart_4341383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4341383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4341383 prefixEnd_4341383 := by exact prefixLift 4341383
  have htrace : WordTrace (prefixWord ++ tailWord_4341383) baseStart_4341383 baseEnd_4341383 := by
    simpa [prefixWord, tailWord_4341383, baseEnd_4341383] using wordTrace_append hprefix tailTrace_4341383
  have hstable : (prefixWord ++ tailWord_4341383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4341383).length < 2 ^ (prefixWord ++ tailWord_4341383).sum := by decide
  have hdescent : baseEnd_4341383 < baseStart_4341383 := by decide
  rcases family_descends (prefixWord ++ tailWord_4341383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4341390 : List Nat := [4, 1, 1, 3, 1, 3, 2, 2, 1, 1, 4]
def baseStart_4341390 : Nat := 118140960795 + 4341390 * 2 ^ 59
def prefixEnd_4341390 : Nat := 4983230072969 + 3 ^ 40 * 4341390 * 2
def baseEnd_4341390 : Nat := 2229219778622874525359317

theorem tailTrace_4341390 : CollatzResearch.WordTrace tailWord_4341390 prefixEnd_4341390 2229219778622874525359317 := by
  unfold tailWord_4341390
  simp only [CollatzResearch.WordTrace]
  refine ⟨19792937717736619403403703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 105562334494595303484819749 19792937717736619403403703)
  ·
    refine ⟨29689406576604929105105555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19792937717736619403403703 29689406576604929105105555)
    ·
      refine ⟨44534109864907393657658333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29689406576604929105105555 44534109864907393657658333)
      ·
        refine ⟨16700291199340272621621875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44534109864907393657658333 16700291199340272621621875)
        ·
          refine ⟨25050436799010408932432813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16700291199340272621621875 25050436799010408932432813)
          ·
            refine ⟨9393913799628903349662305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25050436799010408932432813 9393913799628903349662305)
            ·
              refine ⟨7045435349721677512246729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9393913799628903349662305 7045435349721677512246729)
              ·
                refine ⟨5284076512291258134185047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7045435349721677512246729 5284076512291258134185047)
                ·
                  refine ⟨7926114768436887201277571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5284076512291258134185047 7926114768436887201277571)
                  ·
                    refine ⟨11889172152655330801916357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7926114768436887201277571 11889172152655330801916357)
                    ·
                      refine ⟨2229219778622874525359317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11889172152655330801916357 2229219778622874525359317)
                      ·
                        rfl

theorem cell23_4341390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 2, 2, 1, 1, 4].length) (baseStart_4341390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4341390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4341390 prefixEnd_4341390 := by exact prefixLift 4341390
  have htrace : WordTrace (prefixWord ++ tailWord_4341390) baseStart_4341390 baseEnd_4341390 := by
    simpa [prefixWord, tailWord_4341390, baseEnd_4341390] using wordTrace_append hprefix tailTrace_4341390
  have hstable : (prefixWord ++ tailWord_4341390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4341390).length < 2 ^ (prefixWord ++ tailWord_4341390).sum := by decide
  have hdescent : baseEnd_4341390 < baseStart_4341390 := by decide
  rcases family_descends (prefixWord ++ tailWord_4341390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4341423 : List Nat := [1, 1, 2, 1, 2, 4, 1, 3, 4, 1, 3]
def baseStart_4341423 : Nat := 118140960795 + 4341423 * 2 ^ 59
def prefixEnd_4341423 : Nat := 4983230072969 + 3 ^ 40 * 4341423 * 2
def baseEnd_4341423 : Nat := 2229236723484472896246665

theorem tailTrace_4341423 : CollatzResearch.WordTrace tailWord_4341423 prefixEnd_4341423 2229236723484472896246665 := by
  unfold tailWord_4341423
  simp only [CollatzResearch.WordTrace]
  refine ⟨158344705350773401863180923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105563136900515601242120615 158344705350773401863180923)
  ·
    refine ⟨237517058026160102794771385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158344705350773401863180923 237517058026160102794771385)
    ·
      refine ⟨178137793519620077096078539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 237517058026160102794771385 178137793519620077096078539)
      ·
        refine ⟨267206690279430115644117809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 178137793519620077096078539 267206690279430115644117809)
        ·
          refine ⟨200405017709572586733088357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 267206690279430115644117809 200405017709572586733088357)
          ·
            refine ⟨37575940820544860012454067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 200405017709572586733088357 37575940820544860012454067)
            ·
              refine ⟨56363911230817290018681101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37575940820544860012454067 56363911230817290018681101)
              ·
                refine ⟨21136466711556483757005413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 56363911230817290018681101 21136466711556483757005413)
                ·
                  refine ⟨3963087508416840704438515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21136466711556483757005413 3963087508416840704438515)
                  ·
                    refine ⟨5944631262625261056657773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3963087508416840704438515 5944631262625261056657773)
                    ·
                      refine ⟨2229236723484472896246665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5944631262625261056657773 2229236723484472896246665)
                      ·
                        rfl

theorem cell23_4341423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 3, 4, 1, 3].length) (baseStart_4341423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4341423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4341423 prefixEnd_4341423 := by exact prefixLift 4341423
  have htrace : WordTrace (prefixWord ++ tailWord_4341423) baseStart_4341423 baseEnd_4341423 := by
    simpa [prefixWord, tailWord_4341423, baseEnd_4341423] using wordTrace_append hprefix tailTrace_4341423
  have hstable : (prefixWord ++ tailWord_4341423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4341423).length < 2 ^ (prefixWord ++ tailWord_4341423).sum := by decide
  have hdescent : baseEnd_4341423 < baseStart_4341423 := by decide
  rcases family_descends (prefixWord ++ tailWord_4341423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4341430 : List Nat := [5, 1, 3, 1, 1, 2, 2, 8]
def baseStart_4341430 : Nat := 118140960795 + 4341430 * 2 ^ 59
def prefixEnd_4341430 : Nat := 4983230072969 + 3 ^ 40 * 4341430 * 2
def baseEnd_4341430 : Nat := 82564456216631643291079

theorem tailTrace_4341430 : CollatzResearch.WordTrace tailWord_4341430 prefixEnd_4341430 82564456216631643291079 := by
  unfold tailWord_4341430
  simp only [CollatzResearch.WordTrace]
  refine ⟨9896560041359252628667859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 105563307107832028039123829 9896560041359252628667859)
  ·
    refine ⟨14844840062038878943001789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9896560041359252628667859 14844840062038878943001789)
    ·
      refine ⟨5566815023264579603625671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14844840062038878943001789 5566815023264579603625671)
      ·
        refine ⟨8350222534896869405438507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5566815023264579603625671 8350222534896869405438507)
        ·
          refine ⟨12525333802345304108157761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8350222534896869405438507 12525333802345304108157761)
          ·
            refine ⟨9394000351758978081118321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12525333802345304108157761 9394000351758978081118321)
            ·
              refine ⟨7045500263819233560838741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9394000351758978081118321 7045500263819233560838741)
              ·
                refine ⟨82564456216631643291079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7045500263819233560838741 82564456216631643291079)
                ·
                  rfl

theorem cell23_4341430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 2, 8].length) (baseStart_4341430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4341430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4341430 prefixEnd_4341430 := by exact prefixLift 4341430
  have htrace : WordTrace (prefixWord ++ tailWord_4341430) baseStart_4341430 baseEnd_4341430 := by
    simpa [prefixWord, tailWord_4341430, baseEnd_4341430] using wordTrace_append hprefix tailTrace_4341430
  have hstable : (prefixWord ++ tailWord_4341430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4341430).length < 2 ^ (prefixWord ++ tailWord_4341430).sum := by decide
  have hdescent : baseEnd_4341430 < baseStart_4341430 := by decide
  rcases family_descends (prefixWord ++ tailWord_4341430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4341440 : List Nat := [2, 1, 1, 2, 4, 1, 3, 3, 2, 1, 3]
def baseStart_4341440 : Nat := 118140960795 + 4341440 * 2 ^ 59
def prefixEnd_4341440 : Nat := 4983230072969 + 3 ^ 40 * 4341440 * 2
def baseEnd_4341440 : Nat := 2229245452655599329734087

theorem tailTrace_4341440 : CollatzResearch.WordTrace tailWord_4341440 prefixEnd_4341440 2229245452655599329734087 := by
  unfold tailWord_4341440
  simp only [CollatzResearch.WordTrace]
  refine ⟨79172662695855906883274887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105563550261141209177699849 79172662695855906883274887)
  ·
    refine ⟨118758994043783860324912331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79172662695855906883274887 118758994043783860324912331)
    ·
      refine ⟨178138491065675790487368497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118758994043783860324912331 178138491065675790487368497)
      ·
        refine ⟨133603868299256842865526373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 178138491065675790487368497 133603868299256842865526373)
        ·
          refine ⟨25050725306110658037286195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 133603868299256842865526373 25050725306110658037286195)
          ·
            refine ⟨37576087959165987055929293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25050725306110658037286195 37576087959165987055929293)
            ·
              refine ⟨14091032984687245145973485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37576087959165987055929293 14091032984687245145973485)
              ·
                refine ⟨5284137369257716929740057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14091032984687245145973485 5284137369257716929740057)
                ·
                  refine ⟨3963103026943287697305043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5284137369257716929740057 3963103026943287697305043)
                  ·
                    refine ⟨5944654540414931545957565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3963103026943287697305043 5944654540414931545957565)
                    ·
                      refine ⟨2229245452655599329734087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5944654540414931545957565 2229245452655599329734087)
                      ·
                        rfl

theorem cell23_4341440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 3, 3, 2, 1, 3].length) (baseStart_4341440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4341440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4341440 prefixEnd_4341440 := by exact prefixLift 4341440
  have htrace : WordTrace (prefixWord ++ tailWord_4341440) baseStart_4341440 baseEnd_4341440 := by
    simpa [prefixWord, tailWord_4341440, baseEnd_4341440] using wordTrace_append hprefix tailTrace_4341440
  have hstable : (prefixWord ++ tailWord_4341440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4341440).length < 2 ^ (prefixWord ++ tailWord_4341440).sum := by decide
  have hdescent : baseEnd_4341440 < baseStart_4341440 := by decide
  rcases family_descends (prefixWord ++ tailWord_4341440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4341523 : List Nat := [1, 1, 1, 2, 1, 3, 2, 2, 1, 7, 2]
def baseStart_4341523 : Nat := 118140960795 + 4341523 * 2 ^ 59
def prefixEnd_4341523 : Nat := 4983230072969 + 3 ^ 40 * 4341523 * 2
def baseEnd_4341523 : Nat := 2229288071549922504996205

theorem tailTrace_4341523 : CollatzResearch.WordTrace tailWord_4341523 prefixEnd_4341523 2229288071549922504996205 := by
  unfold tailWord_4341523
  simp only [CollatzResearch.WordTrace]
  refine ⟨158348352650411118941821223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105565568433607412627880815 158348352650411118941821223)
  ·
    refine ⟨237522528975616678412731835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158348352650411118941821223 237522528975616678412731835)
    ·
      refine ⟨356283793463425017619097753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 237522528975616678412731835 356283793463425017619097753)
      ·
        refine ⟨267212845097568763214323315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 356283793463425017619097753 267212845097568763214323315)
        ·
          refine ⟨400819267646353144821484973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 267212845097568763214323315 400819267646353144821484973)
          ·
            refine ⟨150307225367382429308056865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 400819267646353144821484973 150307225367382429308056865)
            ·
              refine ⟨112730419025536821981042649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 150307225367382429308056865 112730419025536821981042649)
              ·
                refine ⟨84547814269152616485781987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 112730419025536821981042649 84547814269152616485781987)
                ·
                  refine ⟨126821721403728924728672981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 84547814269152616485781987 126821721403728924728672981)
                  ·
                    refine ⟨2972384095399896673328273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 126821721403728924728672981 2972384095399896673328273)
                    ·
                      refine ⟨2229288071549922504996205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2972384095399896673328273 2229288071549922504996205)
                      ·
                        rfl

theorem cell23_4341523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 2, 1, 7, 2].length) (baseStart_4341523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4341523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4341523 prefixEnd_4341523 := by exact prefixLift 4341523
  have htrace : WordTrace (prefixWord ++ tailWord_4341523) baseStart_4341523 baseEnd_4341523 := by
    simpa [prefixWord, tailWord_4341523, baseEnd_4341523] using wordTrace_append hprefix tailTrace_4341523
  have hstable : (prefixWord ++ tailWord_4341523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4341523).length < 2 ^ (prefixWord ++ tailWord_4341523).sum := by decide
  have hdescent : baseEnd_4341523 < baseStart_4341523 := by decide
  rcases family_descends (prefixWord ++ tailWord_4341523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4341553 : List Nat := [1, 2, 2, 3, 2, 2, 1, 2, 1, 3, 4]
def baseStart_4341553 : Nat := 118140960795 + 4341553 * 2 ^ 59
def prefixEnd_4341553 : Nat := 4983230072969 + 3 ^ 40 * 4341553 * 2
def baseEnd_4341553 : Nat := 2229303475969557387621067

theorem tailTrace_4341553 : CollatzResearch.WordTrace tailWord_4341553 prefixEnd_4341553 2229303475969557387621067 := by
  unfold tailWord_4341553
  simp only [CollatzResearch.WordTrace]
  refine ⟨158349446840302434065413313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105566297893534956043608875 158349446840302434065413313)
  ·
    refine ⟨118762085130226825549059985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 158349446840302434065413313 118762085130226825549059985)
    ·
      refine ⟨89071563847670119161794989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 118762085130226825549059985 89071563847670119161794989)
      ·
        refine ⟨33401836442876294685673121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 89071563847670119161794989 33401836442876294685673121)
        ·
          refine ⟨25051377332157221014254841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33401836442876294685673121 25051377332157221014254841)
          ·
            refine ⟨18788532999117915760691131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25051377332157221014254841 18788532999117915760691131)
            ·
              refine ⟨28182799498676873641036697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18788532999117915760691131 28182799498676873641036697)
              ·
                refine ⟨21137099624007655230777523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28182799498676873641036697 21137099624007655230777523)
                ·
                  refine ⟨31705649436011482846166285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21137099624007655230777523 31705649436011482846166285)
                  ·
                    refine ⟨11889618538504306067312357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 31705649436011482846166285 11889618538504306067312357)
                    ·
                      refine ⟨2229303475969557387621067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11889618538504306067312357 2229303475969557387621067)
                      ·
                        rfl

theorem cell23_4341553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 1, 2, 1, 3, 4].length) (baseStart_4341553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4341553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4341553 prefixEnd_4341553 := by exact prefixLift 4341553
  have htrace : WordTrace (prefixWord ++ tailWord_4341553) baseStart_4341553 baseEnd_4341553 := by
    simpa [prefixWord, tailWord_4341553, baseEnd_4341553] using wordTrace_append hprefix tailTrace_4341553
  have hstable : (prefixWord ++ tailWord_4341553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4341553).length < 2 ^ (prefixWord ++ tailWord_4341553).sum := by decide
  have hdescent : baseEnd_4341553 < baseStart_4341553 := by decide
  rcases family_descends (prefixWord ++ tailWord_4341553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4341573 : List Nat := [1, 3, 1, 1, 1, 2, 3, 3, 1, 4, 3]
def baseStart_4341573 : Nat := 118140960795 + 4341573 * 2 ^ 59
def prefixEnd_4341573 : Nat := 4983230072969 + 3 ^ 40 * 4341573 * 2
def baseEnd_4341573 : Nat := 2229313745582647309370975

theorem tailTrace_4341573 : CollatzResearch.WordTrace tailWord_4341573 prefixEnd_4341573 2229313745582647309370975 := by
  unfold tailWord_4341573
  simp only [CollatzResearch.WordTrace]
  refine ⟨158350176300229977481141373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105566784200153318320760915 158350176300229977481141373)
  ·
    refine ⟨59381316112586241555428015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 158350176300229977481141373 59381316112586241555428015)
    ·
      refine ⟨89071974168879362333142023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59381316112586241555428015 89071974168879362333142023)
      ·
        refine ⟨133607961253319043499713035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89071974168879362333142023 133607961253319043499713035)
        ·
          refine ⟨200411941879978565249569553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 133607961253319043499713035 200411941879978565249569553)
          ·
            refine ⟨150308956409983923937177165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 200411941879978565249569553 150308956409983923937177165)
            ·
              refine ⟨56365858653743971476441437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 150308956409983923937177165 56365858653743971476441437)
              ·
                refine ⟨21137196995153989303665539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 56365858653743971476441437 21137196995153989303665539)
                ·
                  refine ⟨31705795492730983955498309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21137196995153989303665539 31705795492730983955498309)
                  ·
                    refine ⟨5944836654887059491655933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 31705795492730983955498309 5944836654887059491655933)
                    ·
                      refine ⟨2229313745582647309370975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5944836654887059491655933 2229313745582647309370975)
                      ·
                        rfl

theorem cell23_4341573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 3, 1, 4, 3].length) (baseStart_4341573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4341573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4341573 prefixEnd_4341573 := by exact prefixLift 4341573
  have htrace : WordTrace (prefixWord ++ tailWord_4341573) baseStart_4341573 baseEnd_4341573 := by
    simpa [prefixWord, tailWord_4341573, baseEnd_4341573] using wordTrace_append hprefix tailTrace_4341573
  have hstable : (prefixWord ++ tailWord_4341573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4341573).length < 2 ^ (prefixWord ++ tailWord_4341573).sum := by decide
  have hdescent : baseEnd_4341573 < baseStart_4341573 := by decide
  rcases family_descends (prefixWord ++ tailWord_4341573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4341593 : List Nat := [1, 2, 1, 2, 2, 3, 2, 4, 6]
def baseStart_4341593 : Nat := 118140960795 + 4341593 * 2 ^ 59
def prefixEnd_4341593 : Nat := 4983230072969 + 3 ^ 40 * 4341593 * 2
def baseEnd_4341593 : Nat := 247702668355081914568987

theorem tailTrace_4341593 : CollatzResearch.WordTrace tailWord_4341593 prefixEnd_4341593 247702668355081914568987 := by
  unfold tailWord_4341593
  simp only [CollatzResearch.WordTrace]
  refine ⟨158350905760157520896869433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105567270506771680597912955 158350905760157520896869433)
  ·
    refine ⟨118763179320118140672652075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 158350905760157520896869433 118763179320118140672652075)
    ·
      refine ⟨178144768980177211008978113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118763179320118140672652075 178144768980177211008978113)
      ·
        refine ⟨133608576735132908256733585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 178144768980177211008978113 133608576735132908256733585)
        ·
          refine ⟨100206432551349681192550189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 133608576735132908256733585 100206432551349681192550189)
          ·
            refine ⟨37577412206756130447206321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 100206432551349681192550189 37577412206756130447206321)
            ·
              refine ⟨28183059155067097835404741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37577412206756130447206321 28183059155067097835404741)
              ·
                refine ⟨5284323591575080844138389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28183059155067097835404741 5284323591575080844138389)
                ·
                  refine ⟨247702668355081914568987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5284323591575080844138389 247702668355081914568987)
                  ·
                    rfl

theorem cell23_4341593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 2, 4, 6].length) (baseStart_4341593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4341593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4341593 prefixEnd_4341593 := by exact prefixLift 4341593
  have htrace : WordTrace (prefixWord ++ tailWord_4341593) baseStart_4341593 baseEnd_4341593 := by
    simpa [prefixWord, tailWord_4341593, baseEnd_4341593] using wordTrace_append hprefix tailTrace_4341593
  have hstable : (prefixWord ++ tailWord_4341593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4341593).length < 2 ^ (prefixWord ++ tailWord_4341593).sum := by decide
  have hdescent : baseEnd_4341593 < baseStart_4341593 := by decide
  rcases family_descends (prefixWord ++ tailWord_4341593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4341613 : List Nat := [1, 5, 1, 1, 1, 1, 2, 2, 1, 2, 6]
def baseStart_4341613 : Nat := 118140960795 + 4341613 * 2 ^ 59
def prefixEnd_4341613 : Nat := 4983230072969 + 3 ^ 40 * 4341613 * 2
def baseEnd_4341613 : Nat := 2229334284808827152870791

theorem tailTrace_4341613 : CollatzResearch.WordTrace tailWord_4341613 prefixEnd_4341613 2229334284808827152870791 := by
  unfold tailWord_4341613
  simp only [CollatzResearch.WordTrace]
  refine ⟨158351635220085064312597493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105567756813390042875064995 158351635220085064312597493)
  ·
    refine ⟨14845465801882974779306015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 158351635220085064312597493 14845465801882974779306015)
    ·
      refine ⟨22268198702824462168959023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14845465801882974779306015 22268198702824462168959023)
      ·
        refine ⟨33402298054236693253438535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22268198702824462168959023 33402298054236693253438535)
        ·
          refine ⟨50103447081355039880157803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33402298054236693253438535 50103447081355039880157803)
          ·
            refine ⟨75155170622032559820236705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50103447081355039880157803 75155170622032559820236705)
            ·
              refine ⟨56366377966524419865177529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 75155170622032559820236705 56366377966524419865177529)
              ·
                refine ⟨42274783474893314898883147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 56366377966524419865177529 42274783474893314898883147)
                ·
                  refine ⟨63412175212339972348324721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 42274783474893314898883147 63412175212339972348324721)
                  ·
                    refine ⟨47559131409254979261243541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 63412175212339972348324721 47559131409254979261243541)
                    ·
                      refine ⟨2229334284808827152870791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 47559131409254979261243541 2229334284808827152870791)
                      ·
                        rfl

theorem cell23_4341613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 2, 1, 2, 6].length) (baseStart_4341613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4341613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4341613 prefixEnd_4341613 := by exact prefixLift 4341613
  have htrace : WordTrace (prefixWord ++ tailWord_4341613) baseStart_4341613 baseEnd_4341613 := by
    simpa [prefixWord, tailWord_4341613, baseEnd_4341613] using wordTrace_append hprefix tailTrace_4341613
  have hstable : (prefixWord ++ tailWord_4341613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4341613).length < 2 ^ (prefixWord ++ tailWord_4341613).sum := by decide
  have hdescent : baseEnd_4341613 < baseStart_4341613 := by decide
  rcases family_descends (prefixWord ++ tailWord_4341613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4341653 : List Nat := [1, 3, 2, 1, 1, 3, 1, 2, 3, 6]
def baseStart_4341653 : Nat := 118140960795 + 4341653 * 2 ^ 59
def prefixEnd_4341653 : Nat := 4983230072969 + 3 ^ 40 * 4341653 * 2
def baseEnd_4341653 : Nat := 743118274678335665456869

theorem tailTrace_4341653 : CollatzResearch.WordTrace tailWord_4341653 prefixEnd_4341653 743118274678335665456869 := by
  unfold tailWord_4341653
  simp only [CollatzResearch.WordTrace]
  refine ⟨158353094139940151144053613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105568729426626767429369075 158353094139940151144053613)
  ·
    refine ⟨59382410302477556679020105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 158353094139940151144053613 59382410302477556679020105)
    ·
      refine ⟨44536807726858167509265079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59382410302477556679020105 44536807726858167509265079)
      ·
        refine ⟨66805211590287251263897619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44536807726858167509265079 66805211590287251263897619)
        ·
          refine ⟨100207817385430876895846429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66805211590287251263897619 100207817385430876895846429)
          ·
            refine ⟨37577931519536578835942411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 100207817385430876895846429 37577931519536578835942411)
            ·
              refine ⟨56366897279304868253913617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37577931519536578835942411 56366897279304868253913617)
              ·
                refine ⟨42275172959478651190435213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 56366897279304868253913617 42275172959478651190435213)
                ·
                  refine ⟨15853189859804494196413205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 42275172959478651190435213 15853189859804494196413205)
                  ·
                    refine ⟨743118274678335665456869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15853189859804494196413205 743118274678335665456869)
                    ·
                      rfl

theorem cell23_4341653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 2, 3, 6].length) (baseStart_4341653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4341653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4341653 prefixEnd_4341653 := by exact prefixLift 4341653
  have htrace : WordTrace (prefixWord ++ tailWord_4341653) baseStart_4341653 baseEnd_4341653 := by
    simpa [prefixWord, tailWord_4341653, baseEnd_4341653] using wordTrace_append hprefix tailTrace_4341653
  have hstable : (prefixWord ++ tailWord_4341653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4341653).length < 2 ^ (prefixWord ++ tailWord_4341653).sum := by decide
  have hdescent : baseEnd_4341653 < baseStart_4341653 := by decide
  rcases family_descends (prefixWord ++ tailWord_4341653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4341694 : List Nat := [4, 2, 1, 1, 1, 3, 4, 1, 1, 1, 4]
def baseStart_4341694 : Nat := 118140960795 + 4341694 * 2 ^ 59
def prefixEnd_4341694 : Nat := 4983230072969 + 3 ^ 40 * 4341694 * 2
def baseEnd_4341694 : Nat := 2229375876741841335957919

theorem tailTrace_4341694 : CollatzResearch.WordTrace tailWord_4341694 prefixEnd_4341694 2229375876741841335957919 := by
  unfold tailWord_4341694
  simp only [CollatzResearch.WordTrace]
  refine ⟨19794323691598951893287017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 105569726355194410097530757 19794323691598951893287017)
  ·
    refine ⟨14845742768699213919965263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19794323691598951893287017 14845742768699213919965263)
    ·
      refine ⟨22268614153048820879947895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14845742768699213919965263 22268614153048820879947895)
      ·
        refine ⟨33402921229573231319921843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22268614153048820879947895 33402921229573231319921843)
        ·
          refine ⟨50104381844359846979882765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33402921229573231319921843 50104381844359846979882765)
          ·
            refine ⟨18789143191634942617456037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50104381844359846979882765 18789143191634942617456037)
            ·
              refine ⟨3522964348431551740773007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18789143191634942617456037 3522964348431551740773007)
              ·
                refine ⟨5284446522647327611159511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3522964348431551740773007 5284446522647327611159511)
                ·
                  refine ⟨7926669783970991416739267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5284446522647327611159511 7926669783970991416739267)
                  ·
                    refine ⟨11890004675956487125108901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7926669783970991416739267 11890004675956487125108901)
                    ·
                      refine ⟨2229375876741841335957919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11890004675956487125108901 2229375876741841335957919)
                      ·
                        rfl

theorem cell23_4341694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 4, 1, 1, 1, 4].length) (baseStart_4341694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4341694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4341694 prefixEnd_4341694 := by exact prefixLift 4341694
  have htrace : WordTrace (prefixWord ++ tailWord_4341694) baseStart_4341694 baseEnd_4341694 := by
    simpa [prefixWord, tailWord_4341694, baseEnd_4341694] using wordTrace_append hprefix tailTrace_4341694
  have hstable : (prefixWord ++ tailWord_4341694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4341694).length < 2 ^ (prefixWord ++ tailWord_4341694).sum := by decide
  have hdescent : baseEnd_4341694 < baseStart_4341694 := by decide
  rcases family_descends (prefixWord ++ tailWord_4341694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4341703 : List Nat := [1, 1, 4, 1, 1, 2, 1, 2, 2, 2, 6]
def baseStart_4341703 : Nat := 118140960795 + 4341703 * 2 ^ 59
def prefixEnd_4341703 : Nat := 4983230072969 + 3 ^ 40 * 4341703 * 2
def baseEnd_4341703 : Nat := 2229380498067731800745377

theorem tailTrace_4341703 : CollatzResearch.WordTrace tailWord_4341703 prefixEnd_4341703 2229380498067731800745377 := by
  unfold tailWord_4341703
  simp only [CollatzResearch.WordTrace]
  refine ⟨158354917789759009683373763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105569945193172673122249175 158354917789759009683373763)
  ·
    refine ⟨237532376684638514525060645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158354917789759009683373763 237532376684638514525060645)
    ·
      refine ⟨44537320628369721473448871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 237532376684638514525060645 44537320628369721473448871)
      ·
        refine ⟨66805980942554582210173307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44537320628369721473448871 66805980942554582210173307)
        ·
          refine ⟨100208971413831873315259961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66805980942554582210173307 100208971413831873315259961)
          ·
            refine ⟨75156728560373904986444971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 100208971413831873315259961 75156728560373904986444971)
            ·
              refine ⟨112735092840560857479667457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75156728560373904986444971 112735092840560857479667457)
              ·
                refine ⟨84551319630420643109750593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 112735092840560857479667457 84551319630420643109750593)
                ·
                  refine ⟨63413489722815482332312945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 84551319630420643109750593 63413489722815482332312945)
                  ·
                    refine ⟨47560117292111611749234709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 63413489722815482332312945 47560117292111611749234709)
                    ·
                      refine ⟨2229380498067731800745377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 47560117292111611749234709 2229380498067731800745377)
                      ·
                        rfl

theorem cell23_4341703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 2, 2, 2, 6].length) (baseStart_4341703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4341703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4341703 prefixEnd_4341703 := by exact prefixLift 4341703
  have htrace : WordTrace (prefixWord ++ tailWord_4341703) baseStart_4341703 baseEnd_4341703 := by
    simpa [prefixWord, tailWord_4341703, baseEnd_4341703] using wordTrace_append hprefix tailTrace_4341703
  have hstable : (prefixWord ++ tailWord_4341703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4341703).length < 2 ^ (prefixWord ++ tailWord_4341703).sum := by decide
  have hdescent : baseEnd_4341703 < baseStart_4341703 := by decide
  rcases family_descends (prefixWord ++ tailWord_4341703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4341704 : List Nat := [2, 1, 3, 1, 4, 3, 1, 2, 2, 4]
def baseStart_4341704 : Nat := 118140960795 + 4341704 * 2 ^ 59
def prefixEnd_4341704 : Nat := 4983230072969 + 3 ^ 40 * 4341704 * 2
def baseEnd_4341704 : Nat := 743127003849462098944291

theorem tailTrace_4341704 : CollatzResearch.WordTrace tailWord_4341704 prefixEnd_4341704 743127003849462098944291 := by
  unfold tailWord_4341704
  simp only [CollatzResearch.WordTrace]
  refine ⟨79177477131377693427080083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105569969508503591236106777 79177477131377693427080083)
  ·
    refine ⟨118766215697066540140620125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79177477131377693427080083 118766215697066540140620125)
    ·
      refine ⟨44537330886399952552732547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 118766215697066540140620125 44537330886399952552732547)
      ·
        refine ⟨66805996329599928829098821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44537330886399952552732547 66805996329599928829098821)
        ·
          refine ⟨12526124311799986655456029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 66805996329599928829098821 12526124311799986655456029)
          ·
            refine ⟨4697296616924994995796011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12526124311799986655456029 4697296616924994995796011)
            ·
              refine ⟨7045944925387492493694017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4697296616924994995796011 7045944925387492493694017)
              ·
                refine ⟨5284458694040619370270513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7045944925387492493694017 5284458694040619370270513)
                ·
                  refine ⟨3963344020530464527702885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5284458694040619370270513 3963344020530464527702885)
                  ·
                    refine ⟨743127003849462098944291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3963344020530464527702885 743127003849462098944291)
                    ·
                      rfl

theorem cell23_4341704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 3, 1, 2, 2, 4].length) (baseStart_4341704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4341704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4341704 prefixEnd_4341704 := by exact prefixLift 4341704
  have htrace : WordTrace (prefixWord ++ tailWord_4341704) baseStart_4341704 baseEnd_4341704 := by
    simpa [prefixWord, tailWord_4341704, baseEnd_4341704] using wordTrace_append hprefix tailTrace_4341704
  have hstable : (prefixWord ++ tailWord_4341704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4341704).length < 2 ^ (prefixWord ++ tailWord_4341704).sum := by decide
  have hdescent : baseEnd_4341704 < baseStart_4341704 := by decide
  rcases family_descends (prefixWord ++ tailWord_4341704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4341713 : List Nat := [1, 2, 2, 1, 2, 1, 2, 3, 2, 7]
def baseStart_4341713 : Nat := 118140960795 + 4341713 * 2 ^ 59
def prefixEnd_4341713 : Nat := 4983230072969 + 3 ^ 40 * 4341713 * 2
def baseEnd_4341713 : Nat := 743128544291425587206777

theorem tailTrace_4341713 : CollatzResearch.WordTrace tailWord_4341713 prefixEnd_4341713 743128544291425587206777 := by
  unfold tailWord_4341713
  simp only [CollatzResearch.WordTrace]
  refine ⟨158355282519722781391237793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105570188346481854260825195 158355282519722781391237793)
  ·
    refine ⟨118766461889792086043428345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 158355282519722781391237793 118766461889792086043428345)
    ·
      refine ⟨89074846417344064532571259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 118766461889792086043428345 89074846417344064532571259)
      ·
        refine ⟨133612269626016096798856889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89074846417344064532571259 133612269626016096798856889)
        ·
          refine ⟨100209202219512072599142667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 133612269626016096798856889 100209202219512072599142667)
          ·
            refine ⟨150313803329268108898714001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 100209202219512072599142667 150313803329268108898714001)
            ·
              refine ⟨112735352496951081674035501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 150313803329268108898714001 112735352496951081674035501)
              ·
                refine ⟨42275757186356655627763313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 112735352496951081674035501 42275757186356655627763313)
                ·
                  refine ⟨31706817889767491720822485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 42275757186356655627763313 31706817889767491720822485)
                  ·
                    refine ⟨743128544291425587206777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 31706817889767491720822485 743128544291425587206777)
                    ·
                      rfl

theorem cell23_4341713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 3, 2, 7].length) (baseStart_4341713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4341713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4341713 prefixEnd_4341713 := by exact prefixLift 4341713
  have htrace : WordTrace (prefixWord ++ tailWord_4341713) baseStart_4341713 baseEnd_4341713 := by
    simpa [prefixWord, tailWord_4341713, baseEnd_4341713] using wordTrace_append hprefix tailTrace_4341713
  have hstable : (prefixWord ++ tailWord_4341713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4341713).length < 2 ^ (prefixWord ++ tailWord_4341713).sum := by decide
  have hdescent : baseEnd_4341713 < baseStart_4341713 := by decide
  rcases family_descends (prefixWord ++ tailWord_4341713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4341727 : List Nat := [1, 1, 2, 3, 4, 1, 3, 1, 1, 3, 3]
def baseStart_4341727 : Nat := 118140960795 + 4341727 * 2 ^ 59
def prefixEnd_4341727 : Nat := 4983230072969 + 3 ^ 40 * 4341727 * 2
def baseEnd_4341727 : Nat := 2229392821603439706845267

theorem tailTrace_4341727 : CollatzResearch.WordTrace tailWord_4341727 prefixEnd_4341727 2229392821603439706845267 := by
  unfold tailWord_4341727
  simp only [CollatzResearch.WordTrace]
  refine ⟨158355793141672061782247435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105570528761114707854831623 158355793141672061782247435)
  ·
    refine ⟨237533689712508092673371153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158355793141672061782247435 237533689712508092673371153)
    ·
      refine ⟨178150267284381069505028365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 237533689712508092673371153 178150267284381069505028365)
      ·
        refine ⟨66806350231642901064385637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 178150267284381069505028365 66806350231642901064385637)
        ·
          refine ⟨12526190668433043949572307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 66806350231642901064385637 12526190668433043949572307)
          ·
            refine ⟨18789286002649565924358461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12526190668433043949572307 18789286002649565924358461)
            ·
              refine ⟨7045982250993587221634423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18789286002649565924358461 7045982250993587221634423)
              ·
                refine ⟨10568973376490380832451635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7045982250993587221634423 10568973376490380832451635)
                ·
                  refine ⟨15853460064735571248677453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10568973376490380832451635 15853460064735571248677453)
                  ·
                    refine ⟨5945047524275839218254045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15853460064735571248677453 5945047524275839218254045)
                    ·
                      refine ⟨2229392821603439706845267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5945047524275839218254045 2229392821603439706845267)
                      ·
                        rfl

theorem cell23_4341727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 3, 1, 1, 3, 3].length) (baseStart_4341727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4341727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4341727 prefixEnd_4341727 := by exact prefixLift 4341727
  have htrace : WordTrace (prefixWord ++ tailWord_4341727) baseStart_4341727 baseEnd_4341727 := by
    simpa [prefixWord, tailWord_4341727, baseEnd_4341727] using wordTrace_append hprefix tailTrace_4341727
  have hstable : (prefixWord ++ tailWord_4341727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4341727).length < 2 ^ (prefixWord ++ tailWord_4341727).sum := by decide
  have hdescent : baseEnd_4341727 < baseStart_4341727 := by decide
  rcases family_descends (prefixWord ++ tailWord_4341727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4341745 : List Nat := [1, 2, 2, 2, 6, 1, 1, 3, 1, 2, 2]
def baseStart_4341745 : Nat := 118140960795 + 4341745 * 2 ^ 59
def prefixEnd_4341745 : Nat := 4983230072969 + 3 ^ 40 * 4341745 * 2
def baseEnd_4341745 : Nat := 2229402064255220636420185

theorem tailTrace_4341745 : CollatzResearch.WordTrace tailWord_4341745 prefixEnd_4341745 2229402064255220636420185 := by
  unfold tailWord_4341745
  simp only [CollatzResearch.WordTrace]
  refine ⟨158356449655606850856402689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105570966437071233904268459 158356449655606850856402689)
  ·
    refine ⟨118767337241705138142302017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 158356449655606850856402689 118767337241705138142302017)
    ·
      refine ⟨89075502931278853606726513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 118767337241705138142302017 89075502931278853606726513)
      ·
        refine ⟨66806627198459140205044885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89075502931278853606726513 66806627198459140205044885)
        ·
          refine ⟨3131560649927772197111479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 66806627198459140205044885 3131560649927772197111479)
          ·
            refine ⟨4697340974891658295667219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3131560649927772197111479 4697340974891658295667219)
            ·
              refine ⟨7046011462337487443500829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4697340974891658295667219 7046011462337487443500829)
              ·
                refine ⟨2642254298376557791312811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7046011462337487443500829 2642254298376557791312811)
                ·
                  refine ⟨3963381447564836686969217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2642254298376557791312811 3963381447564836686969217)
                  ·
                    refine ⟨2972536085673627515226913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3963381447564836686969217 2972536085673627515226913)
                    ·
                      refine ⟨2229402064255220636420185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2972536085673627515226913 2229402064255220636420185)
                      ·
                        rfl

theorem cell23_4341745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 6, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 6, 1, 1, 3, 1, 2, 2].length) (baseStart_4341745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4341745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4341745 prefixEnd_4341745 := by exact prefixLift 4341745
  have htrace : WordTrace (prefixWord ++ tailWord_4341745) baseStart_4341745 baseEnd_4341745 := by
    simpa [prefixWord, tailWord_4341745, baseEnd_4341745] using wordTrace_append hprefix tailTrace_4341745
  have hstable : (prefixWord ++ tailWord_4341745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4341745).length < 2 ^ (prefixWord ++ tailWord_4341745).sum := by decide
  have hdescent : baseEnd_4341745 < baseStart_4341745 := by decide
  rcases family_descends (prefixWord ++ tailWord_4341745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4341824 : List Nat := [2, 1, 1, 2, 2, 4, 4, 2, 5]
def baseStart_4341824 : Nat := 118140960795 + 4341824 * 2 ^ 59
def prefixEnd_4341824 : Nat := 4983230072969 + 3 ^ 40 * 4341824 * 2
def baseEnd_4341824 : Nat := 247715847691880647481369

theorem tailTrace_4341824 : CollatzResearch.WordTrace tailWord_4341824 prefixEnd_4341824 247715847691880647481369 := by
  unfold tailWord_4341824
  simp only [CollatzResearch.WordTrace]
  refine ⟨79179665511160323674264263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105572887348213764899019017 79179665511160323674264263)
  ·
    refine ⟨118769498266740485511396395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79179665511160323674264263 118769498266740485511396395)
    ·
      refine ⟨178154247400110728267094593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118769498266740485511396395 178154247400110728267094593)
      ·
        refine ⟨133615685550083046200320945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 178154247400110728267094593 133615685550083046200320945)
        ·
          refine ⟨100211764162562284650240709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 133615685550083046200320945 100211764162562284650240709)
          ·
            refine ⟨18789705780480428371920133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 100211764162562284650240709 18789705780480428371920133)
            ·
              refine ⟨3523069833840080319735025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18789705780480428371920133 3523069833840080319735025)
              ·
                refine ⟨2642302375380060239801269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3523069833840080319735025 2642302375380060239801269)
                ·
                  refine ⟨247715847691880647481369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2642302375380060239801269 247715847691880647481369)
                  ·
                    rfl

theorem cell23_4341824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 4, 2, 5].length) (baseStart_4341824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4341824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4341824 prefixEnd_4341824 := by exact prefixLift 4341824
  have htrace : WordTrace (prefixWord ++ tailWord_4341824) baseStart_4341824 baseEnd_4341824 := by
    simpa [prefixWord, tailWord_4341824, baseEnd_4341824] using wordTrace_append hprefix tailTrace_4341824
  have hstable : (prefixWord ++ tailWord_4341824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4341824).length < 2 ^ (prefixWord ++ tailWord_4341824).sum := by decide
  have hdescent : baseEnd_4341824 < baseStart_4341824 := by decide
  rcases family_descends (prefixWord ++ tailWord_4341824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4341837 : List Nat := [1, 6, 1, 1, 1, 1, 2, 2, 1, 7]
def baseStart_4341837 : Nat := 118140960795 + 4341837 * 2 ^ 59
def prefixEnd_4341837 : Nat := 4983230072969 + 3 ^ 40 * 4341837 * 2
def baseEnd_4341837 : Nat := 743149768158478092156587

theorem tailTrace_4341837 : CollatzResearch.WordTrace tailWord_4341837 prefixEnd_4341837 743149768158478092156587 := by
  unfold tailWord_4341837
  simp only [CollatzResearch.WordTrace]
  refine ⟨158359805171273550568751765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105573203447515700379167843 158359805171273550568751765)
  ·
    refine ⟨7423115867403447682910239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 158359805171273550568751765 7423115867403447682910239)
    ·
      refine ⟨11134673801105171524365359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7423115867403447682910239 11134673801105171524365359)
      ·
        refine ⟨16702010701657757286548039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11134673801105171524365359 16702010701657757286548039)
        ·
          refine ⟨25053016052486635929822059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16702010701657757286548039 25053016052486635929822059)
          ·
            refine ⟨37579524078729953894733089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25053016052486635929822059 37579524078729953894733089)
            ·
              refine ⟨28184643059047465421049817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37579524078729953894733089 28184643059047465421049817)
              ·
                refine ⟨21138482294285599065787363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28184643059047465421049817 21138482294285599065787363)
                ·
                  refine ⟨31707723441428398598681045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21138482294285599065787363 31707723441428398598681045)
                  ·
                    refine ⟨743149768158478092156587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 31707723441428398598681045 743149768158478092156587)
                    ·
                      rfl

theorem cell23_4341837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 2, 2, 1, 7].length) (baseStart_4341837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4341837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4341837 prefixEnd_4341837 := by exact prefixLift 4341837
  have htrace : WordTrace (prefixWord ++ tailWord_4341837) baseStart_4341837 baseEnd_4341837 := by
    simpa [prefixWord, tailWord_4341837, baseEnd_4341837] using wordTrace_append hprefix tailTrace_4341837
  have hstable : (prefixWord ++ tailWord_4341837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4341837).length < 2 ^ (prefixWord ++ tailWord_4341837).sum := by decide
  have hdescent : baseEnd_4341837 < baseStart_4341837 := by decide
  rcases family_descends (prefixWord ++ tailWord_4341837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4341857 : List Nat := [1, 2, 3, 1, 1, 2, 1, 1, 3, 6, 2]
def baseStart_4341857 : Nat := 118140960795 + 4341857 * 2 ^ 59
def prefixEnd_4341857 : Nat := 4983230072969 + 3 ^ 40 * 4341857 * 2
def baseEnd_4341857 : Nat := 2229459574088524198219669

theorem tailTrace_4341857 : CollatzResearch.WordTrace tailWord_4341857 prefixEnd_4341857 2229459574088524198219669 := by
  unfold tailWord_4341857
  simp only [CollatzResearch.WordTrace]
  refine ⟨158360534631201093984479825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105573689754134062656319883 158360534631201093984479825)
  ·
    refine ⟨118770400973400820488359869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 158360534631201093984479825 118770400973400820488359869)
    ·
      refine ⟨44538900365025307683134951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 118770400973400820488359869 44538900365025307683134951)
      ·
        refine ⟨66808350547537961524702427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44538900365025307683134951 66808350547537961524702427)
        ·
          refine ⟨100212525821306942287053641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66808350547537961524702427 100212525821306942287053641)
          ·
            refine ⟨75159394365980206715290231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 100212525821306942287053641 75159394365980206715290231)
            ·
              refine ⟨112739091548970310072935347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75159394365980206715290231 112739091548970310072935347)
              ·
                refine ⟨169108637323455465109403021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 112739091548970310072935347 169108637323455465109403021)
                ·
                  refine ⟨63415738996295799416026133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 169108637323455465109403021 63415738996295799416026133)
                  ·
                    refine ⟨2972612765451365597626225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 63415738996295799416026133 2972612765451365597626225)
                    ·
                      refine ⟨2229459574088524198219669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2972612765451365597626225 2229459574088524198219669)
                      ·
                        rfl

theorem cell23_4341857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 1, 3, 6, 2].length) (baseStart_4341857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4341857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4341857 prefixEnd_4341857 := by exact prefixLift 4341857
  have htrace : WordTrace (prefixWord ++ tailWord_4341857) baseStart_4341857 baseEnd_4341857 := by
    simpa [prefixWord, tailWord_4341857, baseEnd_4341857] using wordTrace_append hprefix tailTrace_4341857
  have hstable : (prefixWord ++ tailWord_4341857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4341857).length < 2 ^ (prefixWord ++ tailWord_4341857).sum := by decide
  have hdescent : baseEnd_4341857 < baseStart_4341857 := by decide
  rcases family_descends (prefixWord ++ tailWord_4341857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4341874 : List Nat := [3, 2, 1, 2, 2, 2, 1, 2, 2, 4, 2]
def baseStart_4341874 : Nat := 118140960795 + 4341874 * 2 ^ 59
def prefixEnd_4341874 : Nat := 4983230072969 + 3 ^ 40 * 4341874 * 2
def baseEnd_4341874 : Nat := 2229468303259650631707091

theorem tailTrace_4341874 : CollatzResearch.WordTrace tailWord_4341874 prefixEnd_4341874 2229468303259650631707091 := by
  unfold tailWord_4341874
  simp only [CollatzResearch.WordTrace]
  refine ⟨39590288668034876471962169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105574103114759670591899117 39590288668034876471962169)
  ·
    refine ⟨29692716501026157353971627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39590288668034876471962169 29692716501026157353971627)
    ·
      refine ⟨44539074751539236030957441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29692716501026157353971627 44539074751539236030957441)
      ·
        refine ⟨33404306063654427023218081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44539074751539236030957441 33404306063654427023218081)
        ·
          refine ⟨25053229547740820267413561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33404306063654427023218081 25053229547740820267413561)
          ·
            refine ⟨18789922160805615200560171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25053229547740820267413561 18789922160805615200560171)
            ·
              refine ⟨28184883241208422800840257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18789922160805615200560171 28184883241208422800840257)
              ·
                refine ⟨21138662430906317100630193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28184883241208422800840257 21138662430906317100630193)
                ·
                  refine ⟨15853996823179737825472645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21138662430906317100630193 15853996823179737825472645)
                  ·
                    refine ⟨2972624404346200842276121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15853996823179737825472645 2972624404346200842276121)
                    ·
                      refine ⟨2229468303259650631707091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2972624404346200842276121 2229468303259650631707091)
                      ·
                        rfl

theorem cell23_4341874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 1, 2, 2, 4, 2].length) (baseStart_4341874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4341874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4341874 prefixEnd_4341874 := by exact prefixLift 4341874
  have htrace : WordTrace (prefixWord ++ tailWord_4341874) baseStart_4341874 baseEnd_4341874 := by
    simpa [prefixWord, tailWord_4341874, baseEnd_4341874] using wordTrace_append hprefix tailTrace_4341874
  have hstable : (prefixWord ++ tailWord_4341874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4341874).length < 2 ^ (prefixWord ++ tailWord_4341874).sum := by decide
  have hdescent : baseEnd_4341874 < baseStart_4341874 := by decide
  rcases family_descends (prefixWord ++ tailWord_4341874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4341884 : List Nat := [2, 2, 2, 1, 1, 5, 2, 1, 3, 4]
def baseStart_4341884 : Nat := 118140960795 + 4341884 * 2 ^ 59
def prefixEnd_4341884 : Nat := 4983230072969 + 3 ^ 40 * 4341884 * 2
def baseEnd_4341884 : Nat := 743157812688731864194015

theorem tailTrace_4341884 : CollatzResearch.WordTrace tailWord_4341884 prefixEnd_4341884 743157812688731864194015 := by
  unfold tailWord_4341884
  simp only [CollatzResearch.WordTrace]
  refine ⟨79180759701051638797856353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105574346268068851730475137 79180759701051638797856353)
  ·
    refine ⟨59385569775788729098392265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79180759701051638797856353 59385569775788729098392265)
    ·
      refine ⟨44539177331841546823794199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59385569775788729098392265 44539177331841546823794199)
      ·
        refine ⟨66808765997762320235691299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44539177331841546823794199 66808765997762320235691299)
        ·
          refine ⟨100213148996643480353536949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66808765997762320235691299 100213148996643480353536949)
          ·
            refine ⟨9394982718435326283144089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 100213148996643480353536949 9394982718435326283144089)
            ·
              refine ⟨7046237038826494712358067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9394982718435326283144089 7046237038826494712358067)
              ·
                refine ⟨10569355558239742068537101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7046237038826494712358067 10569355558239742068537101)
                ·
                  refine ⟨3963508334339903275701413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10569355558239742068537101 3963508334339903275701413)
                  ·
                    refine ⟨743157812688731864194015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3963508334339903275701413 743157812688731864194015)
                    ·
                      rfl

theorem cell23_4341884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 2, 1, 3, 4].length) (baseStart_4341884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4341884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4341884 prefixEnd_4341884 := by exact prefixLift 4341884
  have htrace : WordTrace (prefixWord ++ tailWord_4341884) baseStart_4341884 baseEnd_4341884 := by
    simpa [prefixWord, tailWord_4341884, baseEnd_4341884] using wordTrace_append hprefix tailTrace_4341884
  have hstable : (prefixWord ++ tailWord_4341884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4341884).length < 2 ^ (prefixWord ++ tailWord_4341884).sum := by decide
  have hdescent : baseEnd_4341884 < baseStart_4341884 := by decide
  rcases family_descends (prefixWord ++ tailWord_4341884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4341947 : List Nat := [1, 1, 1, 1, 1, 2, 6, 2, 3, 1, 4]
def baseStart_4341947 : Nat := 118140960795 + 4341947 * 2 ^ 59
def prefixEnd_4341947 : Nat := 4983230072969 + 3 ^ 40 * 4341947 * 2
def baseEnd_4341947 : Nat := 2229505787347428846094255

theorem tailTrace_4341947 : CollatzResearch.WordTrace tailWord_4341947 prefixEnd_4341947 2229505787347428846094255 := by
  unfold tailWord_4341947
  simp only [CollatzResearch.WordTrace]
  refine ⟨158363817200875039355256095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105575878133916692903504063 158363817200875039355256095)
  ·
    refine ⟨237545725801312559032884143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158363817200875039355256095 237545725801312559032884143)
    ·
      refine ⟨356318588701968838549326215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 237545725801312559032884143 356318588701968838549326215)
      ·
        refine ⟨534477883052953257823989323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 356318588701968838549326215 534477883052953257823989323)
        ·
          refine ⟨801716824579429886735983985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 534477883052953257823989323 801716824579429886735983985)
          ·
            refine ⟨601287618434572415051987989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 801716824579429886735983985 601287618434572415051987989)
            ·
              refine ⟨28185357114120581955561937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 601287618434572415051987989 28185357114120581955561937)
              ·
                refine ⟨21139017835590436466671453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28185357114120581955561937 21139017835590436466671453)
                ·
                  refine ⟨7927131688346413675001795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21139017835590436466671453 7927131688346413675001795)
                  ·
                    refine ⟨11890697532519620512502693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7927131688346413675001795 11890697532519620512502693)
                    ·
                      refine ⟨2229505787347428846094255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11890697532519620512502693 2229505787347428846094255)
                      ·
                        rfl

theorem cell23_4341947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 6, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 6, 2, 3, 1, 4].length) (baseStart_4341947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4341947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4341947 prefixEnd_4341947 := by exact prefixLift 4341947
  have htrace : WordTrace (prefixWord ++ tailWord_4341947) baseStart_4341947 baseEnd_4341947 := by
    simpa [prefixWord, tailWord_4341947, baseEnd_4341947] using wordTrace_append hprefix tailTrace_4341947
  have hstable : (prefixWord ++ tailWord_4341947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4341947).length < 2 ^ (prefixWord ++ tailWord_4341947).sum := by decide
  have hdescent : baseEnd_4341947 < baseStart_4341947 := by decide
  rcases family_descends (prefixWord ++ tailWord_4341947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4341948 : List Nat := [2, 2, 2, 3, 4, 1, 2, 1, 6]
def baseStart_4341948 : Nat := 118140960795 + 4341948 * 2 ^ 59
def prefixEnd_4341948 : Nat := 4983230072969 + 3 ^ 40 * 4341948 * 2
def baseEnd_4341948 : Nat := 247722922314231482464639

theorem tailTrace_4341948 : CollatzResearch.WordTrace tailWord_4341948 prefixEnd_4341948 247722922314231482464639 := by
  unfold tailWord_4341948
  simp only [CollatzResearch.WordTrace]
  refine ⟨79181926836935708263021249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105575902449247611017361665 79181926836935708263021249)
  ·
    refine ⟨59386445127701781197265937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79181926836935708263021249 59386445127701781197265937)
    ·
      refine ⟨44539833845776335897949453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59386445127701781197265937 44539833845776335897949453)
      ·
        refine ⟨16702437692166125961731045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44539833845776335897949453 16702437692166125961731045)
        ·
          refine ⟨3131707067281148617824571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16702437692166125961731045 3131707067281148617824571)
          ·
            refine ⟨4697560600921722926736857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3131707067281148617824571 4697560600921722926736857)
            ·
              refine ⟨3523170450691292195052643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4697560600921722926736857 3523170450691292195052643)
              ·
                refine ⟨5284755676036938292578965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3523170450691292195052643 5284755676036938292578965)
                ·
                  refine ⟨247722922314231482464639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5284755676036938292578965 247722922314231482464639)
                  ·
                    rfl

theorem cell23_4341948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 4, 1, 2, 1, 6].length) (baseStart_4341948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4341948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4341948 prefixEnd_4341948 := by exact prefixLift 4341948
  have htrace : WordTrace (prefixWord ++ tailWord_4341948) baseStart_4341948 baseEnd_4341948 := by
    simpa [prefixWord, tailWord_4341948, baseEnd_4341948] using wordTrace_append hprefix tailTrace_4341948
  have hstable : (prefixWord ++ tailWord_4341948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4341948).length < 2 ^ (prefixWord ++ tailWord_4341948).sum := by decide
  have hdescent : baseEnd_4341948 < baseStart_4341948 := by decide
  rcases family_descends (prefixWord ++ tailWord_4341948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4341977 : List Nat := [1, 2, 1, 2, 3, 1, 3, 1, 3, 2, 4]
def baseStart_4341977 : Nat := 118140960795 + 4341977 * 2 ^ 59
def prefixEnd_4341977 : Nat := 4983230072969 + 3 ^ 40 * 4341977 * 2
def baseEnd_4341977 : Nat := 2229521191767063728719117

theorem tailTrace_4341977 : CollatzResearch.WordTrace tailWord_4341977 prefixEnd_4341977 2229521191767063728719117 := by
  unfold tailWord_4341977
  simp only [CollatzResearch.WordTrace]
  refine ⟨158364911390766354478848185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105576607593844236319232123 158364911390766354478848185)
  ·
    refine ⟨118773683543074765859136139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 158364911390766354478848185 118773683543074765859136139)
    ·
      refine ⟨178160525314612148788704209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118773683543074765859136139 178160525314612148788704209)
      ·
        refine ⟨133620393985959111591528157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 178160525314612148788704209 133620393985959111591528157)
        ·
          refine ⟨50107647744734666846823059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 133620393985959111591528157 50107647744734666846823059)
          ·
            refine ⟨75161471617102000270234589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50107647744734666846823059 75161471617102000270234589)
            ·
              refine ⟨28185551856413250101337971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 75161471617102000270234589 28185551856413250101337971)
              ·
                refine ⟨42278327784619875152006957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28185551856413250101337971 42278327784619875152006957)
                ·
                  refine ⟨15854372919232453182002609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 42278327784619875152006957 15854372919232453182002609)
                  ·
                    refine ⟨11890779689424339886501957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15854372919232453182002609 11890779689424339886501957)
                    ·
                      refine ⟨2229521191767063728719117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11890779689424339886501957 2229521191767063728719117)
                      ·
                        rfl

theorem cell23_4341977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 3, 1, 3, 2, 4].length) (baseStart_4341977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4341977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4341977 prefixEnd_4341977 := by exact prefixLift 4341977
  have htrace : WordTrace (prefixWord ++ tailWord_4341977) baseStart_4341977 baseEnd_4341977 := by
    simpa [prefixWord, tailWord_4341977, baseEnd_4341977] using wordTrace_append hprefix tailTrace_4341977
  have hstable : (prefixWord ++ tailWord_4341977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4341977).length < 2 ^ (prefixWord ++ tailWord_4341977).sum := by decide
  have hdescent : baseEnd_4341977 < baseStart_4341977 := by decide
  rcases family_descends (prefixWord ++ tailWord_4341977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4341986 : List Nat := [3, 3, 4, 1, 2, 1, 2, 2, 1, 4]
def baseStart_4341986 : Nat := 118140960795 + 4341986 * 2 ^ 59
def prefixEnd_4341986 : Nat := 4983230072969 + 3 ^ 40 * 4341986 * 2
def baseEnd_4341986 : Nat := 743175271030984731168859

theorem tailTrace_4341986 : CollatzResearch.WordTrace tailWord_4341986 prefixEnd_4341986 743175271030984731168859 := by
  unfold tailWord_4341986
  simp only [CollatzResearch.WordTrace]
  refine ⟨39591309911933437253981453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105576826431822499343950541 39591309911933437253981453)
  ·
    refine ⟨14846741216975038970243045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39591309911933437253981453 14846741216975038970243045)
    ·
      refine ⟨2783763978182819806920571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14846741216975038970243045 2783763978182819806920571)
      ·
        refine ⟨4175645967274229710380857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2783763978182819806920571 4175645967274229710380857)
        ·
          refine ⟨3131734475455672282785643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4175645967274229710380857 3131734475455672282785643)
          ·
            refine ⟨4697601713183508424178465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3131734475455672282785643 4697601713183508424178465)
            ·
              refine ⟨3523201284887631318133849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4697601713183508424178465 3523201284887631318133849)
              ·
                refine ⟨2642400963665723488600387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3523201284887631318133849 2642400963665723488600387)
                ·
                  refine ⟨3963601445498585232900581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2642400963665723488600387 3963601445498585232900581)
                  ·
                    refine ⟨743175271030984731168859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3963601445498585232900581 743175271030984731168859)
                    ·
                      rfl

theorem cell23_4341986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 2, 1, 2, 2, 1, 4].length) (baseStart_4341986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4341986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4341986 prefixEnd_4341986 := by exact prefixLift 4341986
  have htrace : WordTrace (prefixWord ++ tailWord_4341986) baseStart_4341986 baseEnd_4341986 := by
    simpa [prefixWord, tailWord_4341986, baseEnd_4341986] using wordTrace_append hprefix tailTrace_4341986
  have hstable : (prefixWord ++ tailWord_4341986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4341986).length < 2 ^ (prefixWord ++ tailWord_4341986).sum := by decide
  have hdescent : baseEnd_4341986 < baseStart_4341986 := by decide
  rcases family_descends (prefixWord ++ tailWord_4341986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4341987 : List Nat := [1, 1, 1, 8, 12]
def baseStart_4341987 : Nat := 118140960795 + 4341987 * 2 ^ 59
def prefixEnd_4341987 : Nat := 4983230072969 + 3 ^ 40 * 4341987 * 2
def baseEnd_4341987 : Nat := 3058335153050217681199

theorem tailTrace_4341987 : CollatzResearch.WordTrace tailWord_4341987 prefixEnd_4341987 3058335153050217681199 := by
  unfold tailWord_4341987
  simp only [CollatzResearch.WordTrace]
  refine ⟨158365276120730126186712215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105576850747153417457808143 158365276120730126186712215)
  ·
    refine ⟨237547914181095189280068323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158365276120730126186712215 237547914181095189280068323)
    ·
      refine ⟨356321871271642783920102485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 237547914181095189280068323 356321871271642783920102485)
      ·
        refine ⟨4175646928964563874063701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 356321871271642783920102485 4175646928964563874063701)
        ·
          refine ⟨3058335153050217681199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 4175646928964563874063701 3058335153050217681199)
          ·
            rfl

theorem cell23_4341987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 12].length) (baseStart_4341987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4341987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4341987 prefixEnd_4341987 := by exact prefixLift 4341987
  have htrace : WordTrace (prefixWord ++ tailWord_4341987) baseStart_4341987 baseEnd_4341987 := by
    simpa [prefixWord, tailWord_4341987, baseEnd_4341987] using wordTrace_append hprefix tailTrace_4341987
  have hstable : (prefixWord ++ tailWord_4341987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4341987).length < 2 ^ (prefixWord ++ tailWord_4341987).sum := by decide
  have hdescent : baseEnd_4341987 < baseStart_4341987 := by decide
  rcases family_descends (prefixWord ++ tailWord_4341987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4341991 : List Nat := [1, 1, 5, 3, 1, 1, 1, 4, 2, 4]
def baseStart_4341991 : Nat := 118140960795 + 4341991 * 2 ^ 59
def prefixEnd_4341991 : Nat := 4983230072969 + 3 ^ 40 * 4341991 * 2
def baseEnd_4341991 : Nat := 743176126832075557981351

theorem tailTrace_4341991 : CollatzResearch.WordTrace tailWord_4341991 prefixEnd_4341991 743176126832075557981351 := by
  unfold tailWord_4341991
  simp only [CollatzResearch.WordTrace]
  refine ⟨158365422012715634869857827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105576948008477089913238551 158365422012715634869857827)
  ·
    refine ⟨237548133019073452304786741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158365422012715634869857827 237548133019073452304786741)
    ·
      refine ⟨22270137470538136153573757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 237548133019073452304786741 22270137470538136153573757)
      ·
        refine ⟨8351301551451801057590159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22270137470538136153573757 8351301551451801057590159)
        ·
          refine ⟨12526952327177701586385239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8351301551451801057590159 12526952327177701586385239)
          ·
            refine ⟨18790428490766552379577859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12526952327177701586385239 18790428490766552379577859)
            ·
              refine ⟨28185642736149828569366789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18790428490766552379577859 28185642736149828569366789)
              ·
                refine ⟨5284808013028092856756273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28185642736149828569366789 5284808013028092856756273)
                ·
                  refine ⟨3963606009771069642567205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5284808013028092856756273 3963606009771069642567205)
                  ·
                    refine ⟨743176126832075557981351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3963606009771069642567205 743176126832075557981351)
                    ·
                      rfl

theorem cell23_4341991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 1, 4, 2, 4].length) (baseStart_4341991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4341991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4341991 prefixEnd_4341991 := by exact prefixLift 4341991
  have htrace : WordTrace (prefixWord ++ tailWord_4341991) baseStart_4341991 baseEnd_4341991 := by
    simpa [prefixWord, tailWord_4341991, baseEnd_4341991] using wordTrace_append hprefix tailTrace_4341991
  have hstable : (prefixWord ++ tailWord_4341991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4341991).length < 2 ^ (prefixWord ++ tailWord_4341991).sum := by decide
  have hdescent : baseEnd_4341991 < baseStart_4341991 := by decide
  rcases family_descends (prefixWord ++ tailWord_4341991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4342017 : List Nat := [1, 2, 4, 1, 1, 2, 1, 2, 2, 7]
def baseStart_4342017 : Nat := 118140960795 + 4342017 * 2 ^ 59
def prefixEnd_4342017 : Nat := 4983230072969 + 3 ^ 40 * 4342017 * 2
def baseEnd_4342017 : Nat := 743180576997747857406311

theorem tailTrace_4342017 : CollatzResearch.WordTrace tailWord_4342017 prefixEnd_4342017 743180576997747857406311 := by
  unfold tailWord_4342017
  simp only [CollatzResearch.WordTrace]
  refine ⟨158366370310621441310304305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105577580207080960873536203 158366370310621441310304305)
  ·
    refine ⟨118774777732966080982728229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 158366370310621441310304305 118774777732966080982728229)
    ·
      refine ⟨22270270824931140184261543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 118774777732966080982728229 22270270824931140184261543)
      ·
        refine ⟨33405406237396710276392315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22270270824931140184261543 33405406237396710276392315)
        ·
          refine ⟨50108109356095065414588473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33405406237396710276392315 50108109356095065414588473)
          ·
            refine ⟨37581082017071299060941355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50108109356095065414588473 37581082017071299060941355)
            ·
              refine ⟨56371623025606948591412033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37581082017071299060941355 56371623025606948591412033)
              ·
                refine ⟨42278717269205211443559025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 56371623025606948591412033 42278717269205211443559025)
                ·
                  refine ⟨31709037951903908582669269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 42278717269205211443559025 31709037951903908582669269)
                  ·
                    refine ⟨743180576997747857406311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 31709037951903908582669269 743180576997747857406311)
                    ·
                      rfl

theorem cell23_4342017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 2, 2, 7].length) (baseStart_4342017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4342017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4342017 prefixEnd_4342017 := by exact prefixLift 4342017
  have htrace : WordTrace (prefixWord ++ tailWord_4342017) baseStart_4342017 baseEnd_4342017 := by
    simpa [prefixWord, tailWord_4342017, baseEnd_4342017] using wordTrace_append hprefix tailTrace_4342017
  have hstable : (prefixWord ++ tailWord_4342017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4342017).length < 2 ^ (prefixWord ++ tailWord_4342017).sum := by decide
  have hdescent : baseEnd_4342017 < baseStart_4342017 := by decide
  rcases family_descends (prefixWord ++ tailWord_4342017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4342027 : List Nat := [1, 1, 1, 1, 5, 2, 2, 1, 2, 2, 5]
def baseStart_4342027 : Nat := 118140960795 + 4342027 * 2 ^ 59
def prefixEnd_4342027 : Nat := 4983230072969 + 3 ^ 40 * 4342027 * 2
def baseEnd_4342027 : Nat := 2229546865799788533093887

theorem tailTrace_4342027 : CollatzResearch.WordTrace tailWord_4342027 prefixEnd_4342027 2229546865799788533093887 := by
  unfold tailWord_4342027
  simp only [CollatzResearch.WordTrace]
  refine ⟨158366735040585213018168335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105577823360390142012112223 158366735040585213018168335)
  ·
    refine ⟨237550102560877819527252503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158366735040585213018168335 237550102560877819527252503)
    ·
      refine ⟨356325153841316729290878755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 237550102560877819527252503 356325153841316729290878755)
      ·
        refine ⟨534487730761975093936318133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 356325153841316729290878755 534487730761975093936318133)
        ·
          refine ⟨50108224758935165056529825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 534487730761975093936318133 50108224758935165056529825)
          ·
            refine ⟨37581168569201373792397369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50108224758935165056529825 37581168569201373792397369)
            ·
              refine ⟨28185876426901030344298027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37581168569201373792397369 28185876426901030344298027)
              ·
                refine ⟨42278814640351545516447041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28185876426901030344298027 42278814640351545516447041)
                ·
                  refine ⟨31709110980263659137335281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 42278814640351545516447041 31709110980263659137335281)
                  ·
                    refine ⟨23781833235197744353001461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 31709110980263659137335281 23781833235197744353001461)
                    ·
                      refine ⟨2229546865799788533093887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23781833235197744353001461 2229546865799788533093887)
                      ·
                        rfl

theorem cell23_4342027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 2, 1, 2, 2, 5].length) (baseStart_4342027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4342027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4342027 prefixEnd_4342027 := by exact prefixLift 4342027
  have htrace : WordTrace (prefixWord ++ tailWord_4342027) baseStart_4342027 baseEnd_4342027 := by
    simpa [prefixWord, tailWord_4342027, baseEnd_4342027] using wordTrace_append hprefix tailTrace_4342027
  have hstable : (prefixWord ++ tailWord_4342027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4342027).length < 2 ^ (prefixWord ++ tailWord_4342027).sum := by decide
  have hdescent : baseEnd_4342027 < baseStart_4342027 := by decide
  rcases family_descends (prefixWord ++ tailWord_4342027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4342048 : List Nat := [2, 1, 1, 5, 2, 1, 3, 2, 2, 1, 3]
def baseStart_4342048 : Nat := 118140960795 + 4342048 * 2 ^ 59
def prefixEnd_4342048 : Nat := 4983230072969 + 3 ^ 40 * 4342048 * 2
def baseEnd_4342048 : Nat := 2229557648893532950931291

theorem tailTrace_4342048 : CollatzResearch.WordTrace tailWord_4342048 prefixEnd_4342048 2229557648893532950931291 := by
  unfold tailWord_4342048
  simp only [CollatzResearch.WordTrace]
  refine ⟨79183750486754566802341399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105578333982339422403121865 79183750486754566802341399)
  ·
    refine ⟨118775625730131850203512099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79183750486754566802341399 118775625730131850203512099)
    ·
      refine ⟨178163438595197775305268149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118775625730131850203512099 178163438595197775305268149)
      ·
        refine ⟨16702822368299791434868889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 178163438595197775305268149 16702822368299791434868889)
        ·
          refine ⟨12527116776224843576151667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16702822368299791434868889 12527116776224843576151667)
          ·
            refine ⟨18790675164337265364227501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12527116776224843576151667 18790675164337265364227501)
            ·
              refine ⟨7046503186626474511585313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18790675164337265364227501 7046503186626474511585313)
              ·
                refine ⟨5284877389969855883688985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7046503186626474511585313 5284877389969855883688985)
                ·
                  refine ⟨3963658042477391912766739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5284877389969855883688985 3963658042477391912766739)
                  ·
                    refine ⟨5945487063716087869150109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3963658042477391912766739 5945487063716087869150109)
                    ·
                      refine ⟨2229557648893532950931291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5945487063716087869150109 2229557648893532950931291)
                      ·
                        rfl

theorem cell23_4342048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 3, 2, 2, 1, 3].length) (baseStart_4342048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4342048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4342048 prefixEnd_4342048 := by exact prefixLift 4342048
  have htrace : WordTrace (prefixWord ++ tailWord_4342048) baseStart_4342048 baseEnd_4342048 := by
    simpa [prefixWord, tailWord_4342048, baseEnd_4342048] using wordTrace_append hprefix tailTrace_4342048
  have hstable : (prefixWord ++ tailWord_4342048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4342048).length < 2 ^ (prefixWord ++ tailWord_4342048).sum := by decide
  have hdescent : baseEnd_4342048 < baseStart_4342048 := by decide
  rcases family_descends (prefixWord ++ tailWord_4342048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4342065 : List Nat := [1, 2, 2, 3, 4, 1, 3, 1, 2, 1, 3]
def baseStart_4342065 : Nat := 118140960795 + 4342065 * 2 ^ 59
def prefixEnd_4342065 : Nat := 4983230072969 + 3 ^ 40 * 4342065 * 2
def baseEnd_4342065 : Nat := 2229566378064659384418713

theorem tailTrace_4342065 : CollatzResearch.WordTrace tailWord_4342065 prefixEnd_4342065 2229566378064659384418713 := by
  unfold tailWord_4342065
  simp only [CollatzResearch.WordTrace]
  refine ⟨158368121014447545508051649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105578747342965030338701099 158368121014447545508051649)
  ·
    refine ⟨118776090760835659131038737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 158368121014447545508051649 118776090760835659131038737)
    ·
      refine ⟨89082068070626744348279053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 118776090760835659131038737 89082068070626744348279053)
      ·
        refine ⟨33405775526485029130604645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 89082068070626744348279053 33405775526485029130604645)
        ·
          refine ⟨6263582911215942961988371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 33405775526485029130604645 6263582911215942961988371)
          ·
            refine ⟨9395374366823914442982557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6263582911215942961988371 9395374366823914442982557)
            ·
              refine ⟨3523265387558967916118459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9395374366823914442982557 3523265387558967916118459)
              ·
                refine ⟨5284898081338451874177689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3523265387558967916118459 5284898081338451874177689)
                ·
                  refine ⟨3963673561003838905633267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5284898081338451874177689 3963673561003838905633267)
                  ·
                    refine ⟨5945510341505758358449901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3963673561003838905633267 5945510341505758358449901)
                    ·
                      refine ⟨2229566378064659384418713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5945510341505758358449901 2229566378064659384418713)
                      ·
                        rfl

theorem cell23_4342065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 3, 1, 2, 1, 3].length) (baseStart_4342065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4342065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4342065 prefixEnd_4342065 := by exact prefixLift 4342065
  have htrace : WordTrace (prefixWord ++ tailWord_4342065) baseStart_4342065 baseEnd_4342065 := by
    simpa [prefixWord, tailWord_4342065, baseEnd_4342065] using wordTrace_append hprefix tailTrace_4342065
  have hstable : (prefixWord ++ tailWord_4342065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4342065).length < 2 ^ (prefixWord ++ tailWord_4342065).sum := by decide
  have hdescent : baseEnd_4342065 < baseStart_4342065 := by decide
  rcases family_descends (prefixWord ++ tailWord_4342065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4342104 : List Nat := [2, 1, 2, 2, 1, 1, 2, 4, 2, 3, 3]
def baseStart_4342104 : Nat := 118140960795 + 4342104 * 2 ^ 59
def prefixEnd_4342104 : Nat := 4983230072969 + 3 ^ 40 * 4342104 * 2
def baseEnd_4342104 : Nat := 2229586403810184731831033

theorem tailTrace_4342104 : CollatzResearch.WordTrace tailWord_4342104 prefixEnd_4342104 2229586403810184731831033 := by
  unfold tailWord_4342104
  simp only [CollatzResearch.WordTrace]
  refine ⟨79184771730653127584360683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105579695640870836779147577 79184771730653127584360683)
  ·
    refine ⟨118777157595979691376541025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79184771730653127584360683 118777157595979691376541025)
    ·
      refine ⟨89082868196984768532405769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 118777157595979691376541025 89082868196984768532405769)
      ·
        refine ⟨66812151147738576399304327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89082868196984768532405769 66812151147738576399304327)
        ·
          refine ⟨100218226721607864598956491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66812151147738576399304327 100218226721607864598956491)
          ·
            refine ⟨150327340082411796898434737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 100218226721607864598956491 150327340082411796898434737)
            ·
              refine ⟨112745505061808847673826053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 150327340082411796898434737 112745505061808847673826053)
              ·
                refine ⟨21139782199089158938842385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 112745505061808847673826053 21139782199089158938842385)
                ·
                  refine ⟨15854836649316869204131789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21139782199089158938842385 15854836649316869204131789)
                  ·
                    refine ⟨5945563743493825951549421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15854836649316869204131789 5945563743493825951549421)
                    ·
                      refine ⟨2229586403810184731831033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5945563743493825951549421 2229586403810184731831033)
                      ·
                        rfl

theorem cell23_4342104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 4, 2, 3, 3].length) (baseStart_4342104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4342104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4342104 prefixEnd_4342104 := by exact prefixLift 4342104
  have htrace : WordTrace (prefixWord ++ tailWord_4342104) baseStart_4342104 baseEnd_4342104 := by
    simpa [prefixWord, tailWord_4342104, baseEnd_4342104] using wordTrace_append hprefix tailTrace_4342104
  have hstable : (prefixWord ++ tailWord_4342104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4342104).length < 2 ^ (prefixWord ++ tailWord_4342104).sum := by decide
  have hdescent : baseEnd_4342104 < baseStart_4342104 := by decide
  rcases family_descends (prefixWord ++ tailWord_4342104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4342122 : List Nat := [3, 1, 3, 3, 1, 1, 4, 1, 2, 2, 2]
def baseStart_4342122 : Nat := 118140960795 + 4342122 * 2 ^ 59
def prefixEnd_4342122 : Nat := 4983230072969 + 3 ^ 40 * 4342122 * 2
def baseEnd_4342122 : Nat := 2229595646461965661405951

theorem tailTrace_4342122 : CollatzResearch.WordTrace tailWord_4342122 prefixEnd_4342122 2229595646461965661405951 := by
  unfold tailWord_4342122
  simp only [CollatzResearch.WordTrace]
  refine ⟨39592549993810261060719155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105580133316827362828584413 39592549993810261060719155)
  ·
    refine ⟨59388824990715391591078733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39592549993810261060719155 59388824990715391591078733)
    ·
      refine ⟨22270809371518271846654525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59388824990715391591078733 22270809371518271846654525)
      ·
        refine ⟨8351553514319351942495447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22270809371518271846654525 8351553514319351942495447)
        ·
          refine ⟨12527330271479027913743171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8351553514319351942495447 12527330271479027913743171)
          ·
            refine ⟨18790995407218541870614757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12527330271479027913743171 18790995407218541870614757)
            ·
              refine ⟨3523311638853476600740267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18790995407218541870614757 3523311638853476600740267)
              ·
                refine ⟨5284967458280214901110401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3523311638853476600740267 5284967458280214901110401)
                ·
                  refine ⟨3963725593710161175832801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5284967458280214901110401 3963725593710161175832801)
                  ·
                    refine ⟨2972794195282620881874601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3963725593710161175832801 2972794195282620881874601)
                    ·
                      refine ⟨2229595646461965661405951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2972794195282620881874601 2229595646461965661405951)
                      ·
                        rfl

theorem cell23_4342122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 4, 1, 2, 2, 2].length) (baseStart_4342122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4342122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4342122 prefixEnd_4342122 := by exact prefixLift 4342122
  have htrace : WordTrace (prefixWord ++ tailWord_4342122) baseStart_4342122 baseEnd_4342122 := by
    simpa [prefixWord, tailWord_4342122, baseEnd_4342122] using wordTrace_append hprefix tailTrace_4342122
  have hstable : (prefixWord ++ tailWord_4342122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4342122).length < 2 ^ (prefixWord ++ tailWord_4342122).sum := by decide
  have hdescent : baseEnd_4342122 < baseStart_4342122 := by decide
  rcases family_descends (prefixWord ++ tailWord_4342122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4342141 : List Nat := [1, 4, 1, 1, 2, 4, 2, 1, 2, 5]
def baseStart_4342141 : Nat := 118140960795 + 4342141 * 2 ^ 59
def prefixEnd_4342141 : Nat := 4983230072969 + 3 ^ 40 * 4342141 * 2
def baseEnd_4342141 : Nat := 743201800864800362356121

theorem tailTrace_4342141 : CollatzResearch.WordTrace tailWord_4342141 prefixEnd_4342141 743201800864800362356121 := by
  unfold tailWord_4342141
  simp only [CollatzResearch.WordTrace]
  refine ⟨158370892962172210487818277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105580595308114806991878851 158370892962172210487818277)
  ·
    refine ⟨29694542430407289466465927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 158370892962172210487818277 29694542430407289466465927)
    ·
      refine ⟨44541813645610934199698891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29694542430407289466465927 44541813645610934199698891)
      ·
        refine ⟨66812720468416401299548337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44541813645610934199698891 66812720468416401299548337)
        ·
          refine ⟨50109540351312300974661253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66812720468416401299548337 50109540351312300974661253)
          ·
            refine ⟨9395538815871056432748985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 50109540351312300974661253 9395538815871056432748985)
            ·
              refine ⟨7046654111903292324561739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9395538815871056432748985 7046654111903292324561739)
              ·
                refine ⟨10569981167854938486842609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7046654111903292324561739 10569981167854938486842609)
                ·
                  refine ⟨7927485875891203865131957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10569981167854938486842609 7927485875891203865131957)
                  ·
                    refine ⟨743201800864800362356121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7927485875891203865131957 743201800864800362356121)
                    ·
                      rfl

theorem cell23_4342141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 2, 1, 2, 5].length) (baseStart_4342141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4342141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4342141 prefixEnd_4342141 := by exact prefixLift 4342141
  have htrace : WordTrace (prefixWord ++ tailWord_4342141) baseStart_4342141 baseEnd_4342141 := by
    simpa [prefixWord, tailWord_4342141, baseEnd_4342141] using wordTrace_append hprefix tailTrace_4342141
  have hstable : (prefixWord ++ tailWord_4342141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4342141).length < 2 ^ (prefixWord ++ tailWord_4342141).sum := by decide
  have hdescent : baseEnd_4342141 < baseStart_4342141 := by decide
  rcases family_descends (prefixWord ++ tailWord_4342141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4342178 : List Nat := [3, 3, 1, 2, 1, 1, 3, 1, 2, 4, 2]
def baseStart_4342178 : Nat := 118140960795 + 4342178 * 2 ^ 59
def prefixEnd_4342178 : Nat := 4983230072969 + 3 ^ 40 * 4342178 * 2
def baseEnd_4342178 : Nat := 2229624401378617442305693

theorem tailTrace_4342178 : CollatzResearch.WordTrace tailWord_4342178 prefixEnd_4342178 2229624401378617442305693 := by
  unfold tailWord_4342178
  simp only [CollatzResearch.WordTrace]
  refine ⟨39593060615759541451728797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105581494975358777204610125 39593060615759541451728797)
  ·
    refine ⟨14847397730909828044398299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39593060615759541451728797 14847397730909828044398299)
    ·
      refine ⟨22271096596364742066597449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14847397730909828044398299 22271096596364742066597449)
      ·
        refine ⟨16703322447273556549948087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22271096596364742066597449 16703322447273556549948087)
        ·
          refine ⟨25054983670910334824922131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16703322447273556549948087 25054983670910334824922131)
          ·
            refine ⟨37582475506365502237383197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25054983670910334824922131 37582475506365502237383197)
            ·
              refine ⟨14093428314887063339018699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37582475506365502237383197 14093428314887063339018699)
              ·
                refine ⟨21140142472330595008528049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14093428314887063339018699 21140142472330595008528049)
                ·
                  refine ⟨15855106854247946256396037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21140142472330595008528049 15855106854247946256396037)
                  ·
                    refine ⟨2972832535171489923074257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15855106854247946256396037 2972832535171489923074257)
                    ·
                      refine ⟨2229624401378617442305693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2972832535171489923074257 2229624401378617442305693)
                      ·
                        rfl

theorem cell23_4342178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 3, 1, 2, 4, 2].length) (baseStart_4342178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4342178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4342178 prefixEnd_4342178 := by exact prefixLift 4342178
  have htrace : WordTrace (prefixWord ++ tailWord_4342178) baseStart_4342178 baseEnd_4342178 := by
    simpa [prefixWord, tailWord_4342178, baseEnd_4342178] using wordTrace_append hprefix tailTrace_4342178
  have hstable : (prefixWord ++ tailWord_4342178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4342178).length < 2 ^ (prefixWord ++ tailWord_4342178).sum := by decide
  have hdescent : baseEnd_4342178 < baseStart_4342178 := by decide
  rcases family_descends (prefixWord ++ tailWord_4342178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4342205 : List Nat := [1, 4, 1, 2, 2, 3, 2, 3, 1, 4]
def baseStart_4342205 : Nat := 118140960795 + 4342205 * 2 ^ 59
def prefixEnd_4342205 : Nat := 4983230072969 + 3 ^ 40 * 4342205 * 2
def baseEnd_4342205 : Nat := 743212755118762945556023

theorem tailTrace_4342205 : CollatzResearch.WordTrace tailWord_4342205 prefixEnd_4342205 743212755118762945556023 := by
  unfold tailWord_4342205
  simp only [CollatzResearch.WordTrace]
  refine ⟨158373227233940349418148069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105582151489293566278765379 158373227233940349418148069)
  ·
    refine ⟨29694980106363815515902763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 158373227233940349418148069 29694980106363815515902763)
    ·
      refine ⟨44542470159545723273854145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29694980106363815515902763 44542470159545723273854145)
      ·
        refine ⟨33406852619659292455390609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44542470159545723273854145 33406852619659292455390609)
        ·
          refine ⟨25055139464744469341542957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33406852619659292455390609 25055139464744469341542957)
          ·
            refine ⟨9395677299279176003078609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25055139464744469341542957 9395677299279176003078609)
            ·
              refine ⟨7046757974459382002308957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9395677299279176003078609 7046757974459382002308957)
              ·
                refine ⟨2642534240422268250865859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7046757974459382002308957 2642534240422268250865859)
                ·
                  refine ⟨3963801360633402376298789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2642534240422268250865859 3963801360633402376298789)
                  ·
                    refine ⟨743212755118762945556023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3963801360633402376298789 743212755118762945556023)
                    ·
                      rfl

theorem cell23_4342205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 2, 3, 1, 4].length) (baseStart_4342205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4342205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4342205 prefixEnd_4342205 := by exact prefixLift 4342205
  have htrace : WordTrace (prefixWord ++ tailWord_4342205) baseStart_4342205 baseEnd_4342205 := by
    simpa [prefixWord, tailWord_4342205, baseEnd_4342205] using wordTrace_append hprefix tailTrace_4342205
  have hstable : (prefixWord ++ tailWord_4342205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4342205).length < 2 ^ (prefixWord ++ tailWord_4342205).sum := by decide
  have hdescent : baseEnd_4342205 < baseStart_4342205 := by decide
  rcases family_descends (prefixWord ++ tailWord_4342205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4342211 : List Nat := [1, 1, 1, 3, 1, 1, 3, 1, 7, 1, 3]
def baseStart_4342211 : Nat := 118140960795 + 4342211 * 2 ^ 59
def prefixEnd_4342211 : Nat := 4983230072969 + 3 ^ 40 * 4342211 * 2
def baseEnd_4342211 : Nat := 2229641346240215813193041

theorem tailTrace_4342211 : CollatzResearch.WordTrace tailWord_4342211 prefixEnd_4342211 2229641346240215813193041 := by
  unfold tailWord_4342211
  simp only [CollatzResearch.WordTrace]
  refine ⟨158373446071918612442866487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105582297381279074961910991 158373446071918612442866487)
  ·
    refine ⟨237560169107877918664299731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158373446071918612442866487 237560169107877918664299731)
    ·
      refine ⟨356340253661816877996449597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 237560169107877918664299731 356340253661816877996449597)
      ·
        refine ⟨133627595123181329248668599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 356340253661816877996449597 133627595123181329248668599)
        ·
          refine ⟨200441392684771993873002899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 133627595123181329248668599 200441392684771993873002899)
          ·
            refine ⟨300662089027157990809504349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 200441392684771993873002899 300662089027157990809504349)
            ·
              refine ⟨112748283385184246553564131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 300662089027157990809504349 112748283385184246553564131)
              ·
                refine ⟨169122425077776369830346197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 112748283385184246553564131 169122425077776369830346197)
                ·
                  refine ⟨3963806837760383667898739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 169122425077776369830346197 3963806837760383667898739)
                  ·
                    refine ⟨5945710256640575501848109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3963806837760383667898739 5945710256640575501848109)
                    ·
                      refine ⟨2229641346240215813193041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5945710256640575501848109 2229641346240215813193041)
                      ·
                        rfl

theorem cell23_4342211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 1, 7, 1, 3].length) (baseStart_4342211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4342211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4342211 prefixEnd_4342211 := by exact prefixLift 4342211
  have htrace : WordTrace (prefixWord ++ tailWord_4342211) baseStart_4342211 baseEnd_4342211 := by
    simpa [prefixWord, tailWord_4342211, baseEnd_4342211] using wordTrace_append hprefix tailTrace_4342211
  have hstable : (prefixWord ++ tailWord_4342211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4342211).length < 2 ^ (prefixWord ++ tailWord_4342211).sum := by decide
  have hdescent : baseEnd_4342211 < baseStart_4342211 := by decide
  rcases family_descends (prefixWord ++ tailWord_4342211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4342248 : List Nat := [2, 1, 4, 1, 1, 4, 2, 2, 1, 5]
def baseStart_4342248 : Nat := 118140960795 + 4342248 * 2 ^ 59
def prefixEnd_4342248 : Nat := 4983230072969 + 3 ^ 40 * 4342248 * 2
def baseEnd_4342248 : Nat := 743220115008144056143457

theorem tailTrace_4342248 : CollatzResearch.WordTrace tailWord_4342248 prefixEnd_4342248 743220115008144056143457 := by
  unfold tailWord_4342248
  simp only [CollatzResearch.WordTrace]
  refine ⟨79187397786392283880981699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105583197048523045174642265 79187397786392283880981699)
  ·
    refine ⟨118781096679588425821472549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79187397786392283880981699 118781096679588425821472549)
    ·
      refine ⟨22271455627422829841526103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 118781096679588425821472549 22271455627422829841526103)
      ·
        refine ⟨33407183441134244762289155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22271455627422829841526103 33407183441134244762289155)
        ·
          refine ⟨50110775161701367143433733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33407183441134244762289155 50110775161701367143433733)
          ·
            refine ⟨9395770342819006339393825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 50110775161701367143433733 9395770342819006339393825)
            ·
              refine ⟨7046827757114254754545369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9395770342819006339393825 7046827757114254754545369)
              ·
                refine ⟨5285120817835691065909027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7046827757114254754545369 5285120817835691065909027)
                ·
                  refine ⟨7927681226753536598863541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5285120817835691065909027 7927681226753536598863541)
                  ·
                    refine ⟨743220115008144056143457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7927681226753536598863541 743220115008144056143457)
                    ·
                      rfl

theorem cell23_4342248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 2, 2, 1, 5].length) (baseStart_4342248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4342248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4342248 prefixEnd_4342248 := by exact prefixLift 4342248
  have htrace : WordTrace (prefixWord ++ tailWord_4342248) baseStart_4342248 baseEnd_4342248 := by
    simpa [prefixWord, tailWord_4342248, baseEnd_4342248] using wordTrace_append hprefix tailTrace_4342248
  have hstable : (prefixWord ++ tailWord_4342248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4342248).length < 2 ^ (prefixWord ++ tailWord_4342248).sum := by decide
  have hdescent : baseEnd_4342248 < baseStart_4342248 := by decide
  rcases family_descends (prefixWord ++ tailWord_4342248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4342251 : List Nat := [1, 1, 1, 1, 2, 3, 3, 1, 2, 6, 2]
def baseStart_4342251 : Nat := 118140960795 + 4342251 * 2 ^ 59
def prefixEnd_4342251 : Nat := 4983230072969 + 3 ^ 40 * 4342251 * 2
def baseEnd_4342251 : Nat := 2229661885466395656692857

theorem tailTrace_4342251 : CollatzResearch.WordTrace tailWord_4342251 prefixEnd_4342251 2229661885466395656692857 := by
  unfold tailWord_4342251
  simp only [CollatzResearch.WordTrace]
  refine ⟨158374904991773699274322607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105583269994515799516215071 158374904991773699274322607)
  ·
    refine ⟨237562357487660548911483911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158374904991773699274322607 237562357487660548911483911)
    ·
      refine ⟨356343536231490823367225867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 237562357487660548911483911 356343536231490823367225867)
      ·
        refine ⟨534515304347236235050838801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 356343536231490823367225867 534515304347236235050838801)
        ·
          refine ⟨400886478260427176288129101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 534515304347236235050838801 400886478260427176288129101)
          ·
            refine ⟨150332429347660191108048413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 400886478260427176288129101 150332429347660191108048413)
            ·
              refine ⟨56374661005372571665518155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 150332429347660191108048413 56374661005372571665518155)
              ·
                refine ⟨84561991508058857498277233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56374661005372571665518155 84561991508058857498277233)
                ·
                  refine ⟨63421493631044143123707925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 84561991508058857498277233 63421493631044143123707925)
                  ·
                    refine ⟨2972882513955194208923809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 63421493631044143123707925 2972882513955194208923809)
                    ·
                      refine ⟨2229661885466395656692857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2972882513955194208923809 2229661885466395656692857)
                      ·
                        rfl

theorem cell23_4342251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 1, 2, 6, 2].length) (baseStart_4342251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4342251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4342251 prefixEnd_4342251 := by exact prefixLift 4342251
  have htrace : WordTrace (prefixWord ++ tailWord_4342251) baseStart_4342251 baseEnd_4342251 := by
    simpa [prefixWord, tailWord_4342251, baseEnd_4342251] using wordTrace_append hprefix tailTrace_4342251
  have hstable : (prefixWord ++ tailWord_4342251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4342251).length < 2 ^ (prefixWord ++ tailWord_4342251).sum := by decide
  have hdescent : baseEnd_4342251 < baseStart_4342251 := by decide
  rcases family_descends (prefixWord ++ tailWord_4342251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4342271 : List Nat := [1, 1, 2, 2, 1, 2, 6, 1, 1, 1, 5]
def baseStart_4342271 : Nat := 118140960795 + 4342271 * 2 ^ 59
def prefixEnd_4342271 : Nat := 4983230072969 + 3 ^ 40 * 4342271 * 2
def baseEnd_4342271 : Nat := 2229672155079485578442765

theorem tailTrace_4342271 : CollatzResearch.WordTrace tailWord_4342271 prefixEnd_4342271 2229672155079485578442765 := by
  unfold tailWord_4342271
  simp only [CollatzResearch.WordTrace]
  refine ⟨158375634451701242690050667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105583756301134161793367111 158375634451701242690050667)
  ·
    refine ⟨237563451677551864035076001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158375634451701242690050667 237563451677551864035076001)
    ·
      refine ⟨178172588758163898026307001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 237563451677551864035076001 178172588758163898026307001)
      ·
        refine ⟨133629441568622923519730251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 178172588758163898026307001 133629441568622923519730251)
        ·
          refine ⟨200444162352934385279595377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 133629441568622923519730251 200444162352934385279595377)
          ·
            refine ⟨150333121764700788959696533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 200444162352934385279595377 150333121764700788959696533)
            ·
              refine ⟨7046865082720349482485775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 150333121764700788959696533 7046865082720349482485775)
              ·
                refine ⟨10570297624080524223728663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7046865082720349482485775 10570297624080524223728663)
                ·
                  refine ⟨15855446436120786335592995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10570297624080524223728663 15855446436120786335592995)
                  ·
                    refine ⟨23783169654181179503389493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15855446436120786335592995 23783169654181179503389493)
                    ·
                      refine ⟨2229672155079485578442765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23783169654181179503389493 2229672155079485578442765)
                      ·
                        rfl

theorem cell23_4342271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 6, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 6, 1, 1, 1, 5].length) (baseStart_4342271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4342271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4342271 prefixEnd_4342271 := by exact prefixLift 4342271
  have htrace : WordTrace (prefixWord ++ tailWord_4342271) baseStart_4342271 baseEnd_4342271 := by
    simpa [prefixWord, tailWord_4342271, baseEnd_4342271] using wordTrace_append hprefix tailTrace_4342271
  have hstable : (prefixWord ++ tailWord_4342271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4342271).length < 2 ^ (prefixWord ++ tailWord_4342271).sum := by decide
  have hdescent : baseEnd_4342271 < baseStart_4342271 := by decide
  rcases family_descends (prefixWord ++ tailWord_4342271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4342279 : List Nat := [1, 1, 4, 3, 3, 1, 3, 2, 1, 1, 3]
def baseStart_4342279 : Nat := 118140960795 + 4342279 * 2 ^ 59
def prefixEnd_4342279 : Nat := 4983230072969 + 3 ^ 40 * 4342279 * 2
def baseEnd_4342279 : Nat := 2229676262924721547142729

theorem tailTrace_4342279 : CollatzResearch.WordTrace tailWord_4342279 prefixEnd_4342279 2229676262924721547142729 := by
  unfold tailWord_4342279
  simp only [CollatzResearch.WordTrace]
  refine ⟨158375926235672260056341891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105583950823781506704227927 158375926235672260056341891)
  ·
    refine ⟨237563889353508390084512837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158375926235672260056341891 237563889353508390084512837)
    ·
      refine ⟨44543229253782823140846157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 237563889353508390084512837 44543229253782823140846157)
      ·
        refine ⟨16703710970168558677817309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44543229253782823140846157 16703710970168558677817309)
        ·
          refine ⟨6263891613813209504181491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16703710970168558677817309 6263891613813209504181491)
          ·
            refine ⟨9395837420719814256272237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6263891613813209504181491 9395837420719814256272237)
            ·
              refine ⟨3523439032769930346102089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9395837420719814256272237 3523439032769930346102089)
              ·
                refine ⟨2642579274577447759576567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3523439032769930346102089 2642579274577447759576567)
                ·
                  refine ⟨3963868911866171639364851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2642579274577447759576567 3963868911866171639364851)
                  ·
                    refine ⟨5945803367799257459047277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3963868911866171639364851 5945803367799257459047277)
                    ·
                      refine ⟨2229676262924721547142729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5945803367799257459047277 2229676262924721547142729)
                      ·
                        rfl

theorem cell23_4342279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 3, 2, 1, 1, 3].length) (baseStart_4342279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4342279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4342279 prefixEnd_4342279 := by exact prefixLift 4342279
  have htrace : WordTrace (prefixWord ++ tailWord_4342279) baseStart_4342279 baseEnd_4342279 := by
    simpa [prefixWord, tailWord_4342279, baseEnd_4342279] using wordTrace_append hprefix tailTrace_4342279
  have hstable : (prefixWord ++ tailWord_4342279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4342279).length < 2 ^ (prefixWord ++ tailWord_4342279).sum := by decide
  have hdescent : baseEnd_4342279 < baseStart_4342279 := by decide
  rcases family_descends (prefixWord ++ tailWord_4342279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4342335 : List Nat := [1, 1, 2, 2, 3, 2, 4, 2, 2, 1, 3]
def baseStart_4342335 : Nat := 118140960795 + 4342335 * 2 ^ 59
def prefixEnd_4342335 : Nat := 4983230072969 + 3 ^ 40 * 4342335 * 2
def baseEnd_4342335 : Nat := 2229705017841373328042471

theorem tailTrace_4342335 : CollatzResearch.WordTrace tailWord_4342335 prefixEnd_4342335 2229705017841373328042471 := by
  unfold tailWord_4342335
  simp only [CollatzResearch.WordTrace]
  refine ⟨158377968723469381620380459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105585312482312921080253639 158377968723469381620380459)
  ·
    refine ⟨237566953085204072430570689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158377968723469381620380459 237566953085204072430570689)
    ·
      refine ⟨178175214813903054322928017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 237566953085204072430570689 178175214813903054322928017)
      ·
        refine ⟨133631411110427290742196013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 178175214813903054322928017 133631411110427290742196013)
        ·
          refine ⟨50111779166410234028323505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 133631411110427290742196013 50111779166410234028323505)
          ·
            refine ⟨37583834374807675521242629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50111779166410234028323505 37583834374807675521242629)
            ·
              refine ⟨7046968945276439160232993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 37583834374807675521242629 7046968945276439160232993)
              ·
                refine ⟨5285226708957329370174745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7046968945276439160232993 5285226708957329370174745)
                ·
                  refine ⟨3963920031717997027631059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5285226708957329370174745 3963920031717997027631059)
                  ·
                    refine ⟨5945880047576995541446589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3963920031717997027631059 5945880047576995541446589)
                    ·
                      refine ⟨2229705017841373328042471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5945880047576995541446589 2229705017841373328042471)
                      ·
                        rfl

theorem cell23_4342335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 4, 2, 2, 1, 3].length) (baseStart_4342335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4342335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4342335 prefixEnd_4342335 := by exact prefixLift 4342335
  have htrace : WordTrace (prefixWord ++ tailWord_4342335) baseStart_4342335 baseEnd_4342335 := by
    simpa [prefixWord, tailWord_4342335, baseEnd_4342335] using wordTrace_append hprefix tailTrace_4342335
  have hstable : (prefixWord ++ tailWord_4342335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4342335).length < 2 ^ (prefixWord ++ tailWord_4342335).sum := by decide
  have hdescent : baseEnd_4342335 < baseStart_4342335 := by decide
  rcases family_descends (prefixWord ++ tailWord_4342335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4342341 : List Nat := [1, 3, 1, 1, 1, 5, 1, 1, 2, 3, 4]
def baseStart_4342341 : Nat := 118140960795 + 4342341 * 2 ^ 59
def prefixEnd_4342341 : Nat := 4983230072969 + 3 ^ 40 * 4342341 * 2
def baseEnd_4342341 : Nat := 2229708098725300304567443

theorem tailTrace_4342341 : CollatzResearch.WordTrace tailWord_4342341 prefixEnd_4342341 2229708098725300304567443 := by
  unfold tailWord_4342341
  simp only [CollatzResearch.WordTrace]
  refine ⟨158378187561447644645098877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105585458374298429763399251 158378187561447644645098877)
  ·
    refine ⟨59391820335542866741912079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 158378187561447644645098877 59391820335542866741912079)
    ·
      refine ⟨89087730503314300112868119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59391820335542866741912079 89087730503314300112868119)
      ·
        refine ⟨133631595754971450169302179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89087730503314300112868119 133631595754971450169302179)
        ·
          refine ⟨200447393632457175253953269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 133631595754971450169302179 200447393632457175253953269)
          ·
            refine ⟨18791943153042860180058119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 200447393632457175253953269 18791943153042860180058119)
            ·
              refine ⟨28187914729564290270087179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18791943153042860180058119 28187914729564290270087179)
              ·
                refine ⟨42281872094346435405130769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28187914729564290270087179 42281872094346435405130769)
                ·
                  refine ⟨31711404070759826553848077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 42281872094346435405130769 31711404070759826553848077)
                  ·
                    refine ⟨11891776526534934957693029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 31711404070759826553848077 11891776526534934957693029)
                    ·
                      refine ⟨2229708098725300304567443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11891776526534934957693029 2229708098725300304567443)
                      ·
                        rfl

theorem cell23_4342341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 1, 1, 2, 3, 4].length) (baseStart_4342341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4342341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4342341 prefixEnd_4342341 := by exact prefixLift 4342341
  have htrace : WordTrace (prefixWord ++ tailWord_4342341) baseStart_4342341 baseEnd_4342341 := by
    simpa [prefixWord, tailWord_4342341, baseEnd_4342341] using wordTrace_append hprefix tailTrace_4342341
  have hstable : (prefixWord ++ tailWord_4342341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4342341).length < 2 ^ (prefixWord ++ tailWord_4342341).sum := by decide
  have hdescent : baseEnd_4342341 < baseStart_4342341 := by decide
  rcases family_descends (prefixWord ++ tailWord_4342341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4342371 : List Nat := [1, 1, 1, 5, 1, 2, 1, 2, 1, 4, 4]
def baseStart_4342371 : Nat := 118140960795 + 4342371 * 2 ^ 59
def prefixEnd_4342371 : Nat := 4983230072969 + 3 ^ 40 * 4342371 * 2
def baseEnd_4342371 : Nat := 2229723503144935187192305

theorem tailTrace_4342371 : CollatzResearch.WordTrace tailWord_4342371 prefixEnd_4342371 2229723503144935187192305 := by
  unfold tailWord_4342371
  simp only [CollatzResearch.WordTrace]
  refine ⟨158379281751338959768690967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105586187834225973179127311 158379281751338959768690967)
  ·
    refine ⟨237568922627008439653036451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158379281751338959768690967 237568922627008439653036451)
    ·
      refine ⟨356353383940512659479554677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 237568922627008439653036451 356353383940512659479554677)
      ·
        refine ⟨33408129744423061826208251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 356353383940512659479554677 33408129744423061826208251)
        ·
          refine ⟨50112194616634592739312377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33408129744423061826208251 50112194616634592739312377)
          ·
            refine ⟨37584145962475944554484283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50112194616634592739312377 37584145962475944554484283)
            ·
              refine ⟨56376218943713916831726425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37584145962475944554484283 56376218943713916831726425)
              ·
                refine ⟨42282164207785437623794819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 56376218943713916831726425 42282164207785437623794819)
                ·
                  refine ⟨63423246311678156435692229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 42282164207785437623794819 63423246311678156435692229)
                  ·
                    refine ⟨11891858683439654331692293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 63423246311678156435692229 11891858683439654331692293)
                    ·
                      refine ⟨2229723503144935187192305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11891858683439654331692293 2229723503144935187192305)
                      ·
                        rfl

theorem cell23_4342371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 2, 1, 4, 4].length) (baseStart_4342371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4342371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4342371 prefixEnd_4342371 := by exact prefixLift 4342371
  have htrace : WordTrace (prefixWord ++ tailWord_4342371) baseStart_4342371 baseEnd_4342371 := by
    simpa [prefixWord, tailWord_4342371, baseEnd_4342371] using wordTrace_append hprefix tailTrace_4342371
  have hstable : (prefixWord ++ tailWord_4342371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4342371).length < 2 ^ (prefixWord ++ tailWord_4342371).sum := by decide
  have hdescent : baseEnd_4342371 < baseStart_4342371 := by decide
  rcases family_descends (prefixWord ++ tailWord_4342371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4342375 : List Nat := [1, 1, 5, 1, 1, 1, 1, 4, 4, 2, 2]
def baseStart_4342375 : Nat := 118140960795 + 4342375 * 2 ^ 59
def prefixEnd_4342375 : Nat := 4983230072969 + 3 ^ 40 * 4342375 * 2
def baseEnd_4342375 : Nat := 2229725557067553171542287

theorem tailTrace_4342375 : CollatzResearch.WordTrace tailWord_4342375 prefixEnd_4342375 2229725557067553171542287 := by
  unfold tailWord_4342375
  simp only [CollatzResearch.WordTrace]
  refine ⟨158379427643324468451836579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105586285095549645634557719 158379427643324468451836579)
  ·
    refine ⟨237569141464986702677754869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158379427643324468451836579 237569141464986702677754869)
    ·
      refine ⟨22272107012342503376039519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 237569141464986702677754869 22272107012342503376039519)
      ·
        refine ⟨33408160518513755064059279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22272107012342503376039519 33408160518513755064059279)
        ·
          refine ⟨50112240777770632596088919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33408160518513755064059279 50112240777770632596088919)
          ·
            refine ⟨75168361166655948894133379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50112240777770632596088919 75168361166655948894133379)
            ·
              refine ⟨112752541749983923341200069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75168361166655948894133379 112752541749983923341200069)
              ·
                refine ⟨21141101578121985626475013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 112752541749983923341200069 21141101578121985626475013)
                ·
                  refine ⟨3963956545897872304964065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21141101578121985626475013 3963956545897872304964065)
                  ·
                    refine ⟨2972967409423404228723049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3963956545897872304964065 2972967409423404228723049)
                    ·
                      refine ⟨2229725557067553171542287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2972967409423404228723049 2229725557067553171542287)
                      ·
                        rfl

theorem cell23_4342375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 4, 4, 2, 2].length) (baseStart_4342375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4342375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4342375 prefixEnd_4342375 := by exact prefixLift 4342375
  have htrace : WordTrace (prefixWord ++ tailWord_4342375) baseStart_4342375 baseEnd_4342375 := by
    simpa [prefixWord, tailWord_4342375, baseEnd_4342375] using wordTrace_append hprefix tailTrace_4342375
  have hstable : (prefixWord ++ tailWord_4342375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4342375).length < 2 ^ (prefixWord ++ tailWord_4342375).sum := by decide
  have hdescent : baseEnd_4342375 < baseStart_4342375 := by decide
  rcases family_descends (prefixWord ++ tailWord_4342375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4342411 : List Nat := [1, 1, 1, 1, 4, 1, 2, 1, 6, 5]
def baseStart_4342411 : Nat := 118140960795 + 4342411 * 2 ^ 59
def prefixEnd_4342411 : Nat := 4983230072969 + 3 ^ 40 * 4342411 * 2
def baseEnd_4342411 : Nat := 743248014123705010230707

theorem tailTrace_4342411 : CollatzResearch.WordTrace tailWord_4342411 prefixEnd_4342411 743248014123705010230707 := by
  unfold tailWord_4342411
  simp only [CollatzResearch.WordTrace]
  refine ⟨158380740671194046600147087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105587160447462697733431391 158380740671194046600147087)
  ·
    refine ⟨237571111006791069900220631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158380740671194046600147087 237571111006791069900220631)
    ·
      refine ⟨356356666510186604850330947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 237571111006791069900220631 356356666510186604850330947)
      ·
        refine ⟨534534999765279907275496421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 356356666510186604850330947 534534999765279907275496421)
        ·
          refine ⟨100225312455989982614155579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 534534999765279907275496421 100225312455989982614155579)
          ·
            refine ⟨150337968683984973921233369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 100225312455989982614155579 150337968683984973921233369)
            ·
              refine ⟨112753476512988730440925027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 150337968683984973921233369 112753476512988730440925027)
              ·
                refine ⟨169130214769483095661387541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 112753476512988730440925027 169130214769483095661387541)
                ·
                  refine ⟨7927978817319520109127541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 169130214769483095661387541 7927978817319520109127541)
                  ·
                    refine ⟨743248014123705010230707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7927978817319520109127541 743248014123705010230707)
                    ·
                      rfl

theorem cell23_4342411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 1, 6, 5].length) (baseStart_4342411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4342411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4342411 prefixEnd_4342411 := by exact prefixLift 4342411
  have htrace : WordTrace (prefixWord ++ tailWord_4342411) baseStart_4342411 baseEnd_4342411 := by
    simpa [prefixWord, tailWord_4342411, baseEnd_4342411] using wordTrace_append hprefix tailTrace_4342411
  have hstable : (prefixWord ++ tailWord_4342411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4342411).length < 2 ^ (prefixWord ++ tailWord_4342411).sum := by decide
  have hdescent : baseEnd_4342411 < baseStart_4342411 := by decide
  rcases family_descends (prefixWord ++ tailWord_4342411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4342421 : List Nat := [1, 3, 2, 1, 1, 1, 1, 1, 5, 2, 5]
def baseStart_4342421 : Nat := 118140960795 + 4342421 * 2 ^ 59
def prefixEnd_4342421 : Nat := 4983230072969 + 3 ^ 40 * 4342421 * 2
def baseEnd_4342421 : Nat := 2229749177177659991567075

theorem tailTrace_4342421 : CollatzResearch.WordTrace tailWord_4342421 prefixEnd_4342421 2229749177177659991567075 := by
  unfold tailWord_4342421
  simp only [CollatzResearch.WordTrace]
  refine ⟨158381105401157818308011117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105587403600771878872007411 158381105401157818308011117)
  ·
    refine ⟨59392914525434181865504169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 158381105401157818308011117 59392914525434181865504169)
    ·
      refine ⟨44544685894075636399128127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59392914525434181865504169 44544685894075636399128127)
      ·
        refine ⟨66817028841113454598692191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44544685894075636399128127 66817028841113454598692191)
        ·
          refine ⟨100225543261670181898038287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66817028841113454598692191 100225543261670181898038287)
          ·
            refine ⟨150338314892505272847057431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 100225543261670181898038287 150338314892505272847057431)
            ·
              refine ⟨225507472338757909270586147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 150338314892505272847057431 225507472338757909270586147)
              ·
                refine ⟨338261208508136863905879221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 225507472338757909270586147 338261208508136863905879221)
                ·
                  refine ⟨31711988297637830991176177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 338261208508136863905879221 31711988297637830991176177)
                  ·
                    refine ⟨23783991223228373243382133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 31711988297637830991176177 23783991223228373243382133)
                    ·
                      refine ⟨2229749177177659991567075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23783991223228373243382133 2229749177177659991567075)
                      ·
                        rfl

theorem cell23_4342421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 1, 5, 2, 5].length) (baseStart_4342421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4342421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4342421 prefixEnd_4342421 := by exact prefixLift 4342421
  have htrace : WordTrace (prefixWord ++ tailWord_4342421) baseStart_4342421 baseEnd_4342421 := by
    simpa [prefixWord, tailWord_4342421, baseEnd_4342421] using wordTrace_append hprefix tailTrace_4342421
  have hstable : (prefixWord ++ tailWord_4342421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4342421).length < 2 ^ (prefixWord ++ tailWord_4342421).sum := by decide
  have hdescent : baseEnd_4342421 < baseStart_4342421 := by decide
  rcases family_descends (prefixWord ++ tailWord_4342421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4342428 : List Nat := [2, 2, 3, 2, 2, 1, 2, 1, 1, 7]
def baseStart_4342428 : Nat := 118140960795 + 4342428 * 2 ^ 59
def prefixEnd_4342428 : Nat := 4983230072969 + 3 ^ 40 * 4342428 * 2
def baseEnd_4342428 : Nat := 743250923847413821393181

theorem tailTrace_4342428 : CollatzResearch.WordTrace tailWord_4342428 prefixEnd_4342428 743250923847413821393181 := by
  unfold tailWord_4342428
  simp only [CollatzResearch.WordTrace]
  refine ⟨79190680356066229251757969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105587573808088305669010625 79190680356066229251757969)
  ·
    refine ⟨59393010267049671938818477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79190680356066229251757969 59393010267049671938818477)
    ·
      refine ⟨22272378850143626977056929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59393010267049671938818477 22272378850143626977056929)
      ·
        refine ⟨16704284137607720232792697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22272378850143626977056929 16704284137607720232792697)
        ·
          refine ⟨12528213103205790174594523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16704284137607720232792697 12528213103205790174594523)
          ·
            refine ⟨18792319654808685261891785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12528213103205790174594523 18792319654808685261891785)
            ·
              refine ⟨14094239741106513946418839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18792319654808685261891785 14094239741106513946418839)
              ·
                refine ⟨21141359611659770919628259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14094239741106513946418839 21141359611659770919628259)
                ·
                  refine ⟨31712039417489656379442389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21141359611659770919628259 31712039417489656379442389)
                  ·
                    refine ⟨743250923847413821393181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 31712039417489656379442389 743250923847413821393181)
                    ·
                      rfl

theorem cell23_4342428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 2, 1, 1, 7].length) (baseStart_4342428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4342428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4342428 prefixEnd_4342428 := by exact prefixLift 4342428
  have htrace : WordTrace (prefixWord ++ tailWord_4342428) baseStart_4342428 baseEnd_4342428 := by
    simpa [prefixWord, tailWord_4342428, baseEnd_4342428] using wordTrace_append hprefix tailTrace_4342428
  have hstable : (prefixWord ++ tailWord_4342428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4342428).length < 2 ^ (prefixWord ++ tailWord_4342428).sum := by decide
  have hdescent : baseEnd_4342428 < baseStart_4342428 := by decide
  rcases family_descends (prefixWord ++ tailWord_4342428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4342432 : List Nat := [2, 1, 1, 4, 4, 2, 1, 3, 5]
def baseStart_4342432 : Nat := 118140960795 + 4342432 * 2 ^ 59
def prefixEnd_4342432 : Nat := 4983230072969 + 3 ^ 40 * 4342432 * 2
def baseEnd_4342432 : Nat := 247750536162762160947725

theorem tailTrace_4342432 : CollatzResearch.WordTrace tailWord_4342432 prefixEnd_4342432 247750536162762160947725 := by
  unfold tailWord_4342432
  simp only [CollatzResearch.WordTrace]
  refine ⟨79190753302058983593330775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105587671069411978124441033 79190753302058983593330775)
  ·
    refine ⟨118786129953088475389996163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79190753302058983593330775 118786129953088475389996163)
    ·
      refine ⟨178179194929632713084994245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118786129953088475389996163 178179194929632713084994245)
      ·
        refine ⟨33408599049306133703436421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 178179194929632713084994245 33408599049306133703436421)
        ·
          refine ⟨6264112321744900069394329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 33408599049306133703436421 6264112321744900069394329)
          ·
            refine ⟨4698084241308675052045747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6264112321744900069394329 4698084241308675052045747)
            ·
              refine ⟨7047126361963012578068621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4698084241308675052045747 7047126361963012578068621)
              ·
                refine ⟨2642672385736129716775733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7047126361963012578068621 2642672385736129716775733)
                ·
                  refine ⟨247750536162762160947725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2642672385736129716775733 247750536162762160947725)
                  ·
                    rfl

theorem cell23_4342432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 2, 1, 3, 5].length) (baseStart_4342432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4342432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4342432 prefixEnd_4342432 := by exact prefixLift 4342432
  have htrace : WordTrace (prefixWord ++ tailWord_4342432) baseStart_4342432 baseEnd_4342432 := by
    simpa [prefixWord, tailWord_4342432, baseEnd_4342432] using wordTrace_append hprefix tailTrace_4342432
  have hstable : (prefixWord ++ tailWord_4342432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4342432).length < 2 ^ (prefixWord ++ tailWord_4342432).sum := by decide
  have hdescent : baseEnd_4342432 < baseStart_4342432 := by decide
  rcases family_descends (prefixWord ++ tailWord_4342432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4342445 : List Nat := [1, 5, 2, 1, 1, 3, 1, 2, 2, 5]
def baseStart_4342445 : Nat := 118140960795 + 4342445 * 2 ^ 59
def prefixEnd_4342445 : Nat := 4983230072969 + 3 ^ 40 * 4342445 * 2
def baseEnd_4342445 : Nat := 743253833571122632555655

theorem tailTrace_4342445 : CollatzResearch.WordTrace tailWord_4342445 prefixEnd_4342445 743253833571122632555655 := by
  unfold tailWord_4342445
  simp only [CollatzResearch.WordTrace]
  refine ⟨158381980753070870406884789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105587987168713913604589859 158381980753070870406884789)
  ·
    refine ⟨14848310695600394100645449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 158381980753070870406884789 14848310695600394100645449)
    ·
      refine ⟨11136233021700295575484087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14848310695600394100645449 11136233021700295575484087)
      ·
        refine ⟨16704349532550443363226131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11136233021700295575484087 16704349532550443363226131)
        ·
          refine ⟨25056524298825665044839197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16704349532550443363226131 25056524298825665044839197)
          ·
            refine ⟨9396196612059624391814699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25056524298825665044839197 9396196612059624391814699)
            ·
              refine ⟨14094294918089436587722049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9396196612059624391814699 14094294918089436587722049)
              ·
                refine ⟨10570721188567077440791537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14094294918089436587722049 10570721188567077440791537)
                ·
                  refine ⟨7928040891425308080593653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10570721188567077440791537 7928040891425308080593653)
                  ·
                    refine ⟨743253833571122632555655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7928040891425308080593653 743253833571122632555655)
                    ·
                      rfl

theorem cell23_4342445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 1, 2, 2, 5].length) (baseStart_4342445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4342445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4342445 prefixEnd_4342445 := by exact prefixLift 4342445
  have htrace : WordTrace (prefixWord ++ tailWord_4342445) baseStart_4342445 baseEnd_4342445 := by
    simpa [prefixWord, tailWord_4342445, baseEnd_4342445] using wordTrace_append hprefix tailTrace_4342445
  have hstable : (prefixWord ++ tailWord_4342445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4342445).length < 2 ^ (prefixWord ++ tailWord_4342445).sum := by decide
  have hdescent : baseEnd_4342445 < baseStart_4342445 := by decide
  rcases family_descends (prefixWord ++ tailWord_4342445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4342449 : List Nat := [1, 2, 2, 6, 1, 1, 3, 2, 5]
def baseStart_4342449 : Nat := 118140960795 + 4342449 * 2 ^ 59
def prefixEnd_4342449 : Nat := 4983230072969 + 3 ^ 40 * 4342449 * 2
def baseEnd_4342449 : Nat := 247751506070665098001883

theorem tailTrace_4342449 : CollatzResearch.WordTrace tailWord_4342449 prefixEnd_4342449 247751506070665098001883 := by
  unfold tailWord_4342449
  simp only [CollatzResearch.WordTrace]
  refine ⟨158382126645056379090030401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105588084430037586060020267 158382126645056379090030401)
  ·
    refine ⟨118786594983792284317522801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 158382126645056379090030401 118786594983792284317522801)
    ·
      refine ⟨89089946237844213238142101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 118786594983792284317522801 89089946237844213238142101)
      ·
        refine ⟨4176091229898947495537911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 89089946237844213238142101 4176091229898947495537911)
        ·
          refine ⟨6264136844848421243306867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4176091229898947495537911 6264136844848421243306867)
          ·
            refine ⟨9396205267272631864960301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6264136844848421243306867 9396205267272631864960301)
            ·
              refine ⟨3523576975227236949360113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9396205267272631864960301 3523576975227236949360113)
              ·
                refine ⟨2642682731420427712020085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3523576975227236949360113 2642682731420427712020085)
                ·
                  refine ⟨247751506070665098001883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2642682731420427712020085 247751506070665098001883)
                  ·
                    rfl

theorem cell23_4342449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 3, 2, 5].length) (baseStart_4342449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4342449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4342449 prefixEnd_4342449 := by exact prefixLift 4342449
  have htrace : WordTrace (prefixWord ++ tailWord_4342449) baseStart_4342449 baseEnd_4342449 := by
    simpa [prefixWord, tailWord_4342449, baseEnd_4342449] using wordTrace_append hprefix tailTrace_4342449
  have hstable : (prefixWord ++ tailWord_4342449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4342449).length < 2 ^ (prefixWord ++ tailWord_4342449).sum := by decide
  have hdescent : baseEnd_4342449 < baseStart_4342449 := by decide
  rcases family_descends (prefixWord ++ tailWord_4342449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4342471 : List Nat := [1, 1, 4, 1, 1, 1, 2, 2, 10]
def baseStart_4342471 : Nat := 118140960795 + 4342471 * 2 ^ 59
def prefixEnd_4342471 : Nat := 4983230072969 + 3 ^ 40 * 4342471 * 2
def baseEnd_4342471 : Nat := 247752761245598310660205

theorem tailTrace_4342471 : CollatzResearch.WordTrace tailWord_4342471 prefixEnd_4342471 247752761245598310660205 := by
  unfold tailWord_4342471
  simp only [CollatzResearch.WordTrace]
  refine ⟨158382929050976676847331267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105588619367317784564887511 158382929050976676847331267)
  ·
    refine ⟨237574393576465015270996901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158382929050976676847331267 237574393576465015270996901)
    ·
      refine ⟨44545198795587190363311919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 237574393576465015270996901 44545198795587190363311919)
      ·
        refine ⟨66817798193380785544967879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44545198795587190363311919 66817798193380785544967879)
        ·
          refine ⟨100226697290071178317451819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66817798193380785544967879 100226697290071178317451819)
          ·
            refine ⟨150340045935106767476177729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 100226697290071178317451819 150340045935106767476177729)
            ·
              refine ⟨112755034451330075607133297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 150340045935106767476177729 112755034451330075607133297)
              ·
                refine ⟨84566275838497556705349973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 112755034451330075607133297 84566275838497556705349973)
                ·
                  refine ⟨247752761245598310660205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 84566275838497556705349973 247752761245598310660205)
                  ·
                    rfl

theorem cell23_4342471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 2, 10].length) (baseStart_4342471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4342471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4342471 prefixEnd_4342471 := by exact prefixLift 4342471
  have htrace : WordTrace (prefixWord ++ tailWord_4342471) baseStart_4342471 baseEnd_4342471 := by
    simpa [prefixWord, tailWord_4342471, baseEnd_4342471] using wordTrace_append hprefix tailTrace_4342471
  have hstable : (prefixWord ++ tailWord_4342471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4342471).length < 2 ^ (prefixWord ++ tailWord_4342471).sum := by decide
  have hdescent : baseEnd_4342471 < baseStart_4342471 := by decide
  rcases family_descends (prefixWord ++ tailWord_4342471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4342482 : List Nat := [3, 2, 2, 2, 3, 1, 2, 1, 2, 1, 4]
def baseStart_4342482 : Nat := 118140960795 + 4342482 * 2 ^ 59
def prefixEnd_4342482 : Nat := 4983230072969 + 3 ^ 40 * 4342482 * 2
def baseEnd_4342482 : Nat := 2229780499497584252904295

theorem tailTrace_4342482 : CollatzResearch.WordTrace tailWord_4342482 prefixEnd_4342482 2229780499497584252904295 := by
  unfold tailWord_4342482
  simp only [CollatzResearch.WordTrace]
  refine ⟨39595832563484206431495425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105588886835957883817321133 39595832563484206431495425)
  ·
    refine ⟨29696874422613154823621569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39595832563484206431495425 29696874422613154823621569)
    ·
      refine ⟨22272655816959866117716177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29696874422613154823621569 22272655816959866117716177)
      ·
        refine ⟨16704491862719899588287133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22272655816959866117716177 16704491862719899588287133)
        ·
          refine ⟨6264184448519962345607675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16704491862719899588287133 6264184448519962345607675)
          ·
            refine ⟨9396276672779943518411513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6264184448519962345607675 9396276672779943518411513)
            ·
              refine ⟨7047207504584957638808635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9396276672779943518411513 7047207504584957638808635)
              ·
                refine ⟨10570811256877436458212953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7047207504584957638808635 10570811256877436458212953)
                ·
                  refine ⟨7928108442658077343659715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10570811256877436458212953 7928108442658077343659715)
                  ·
                    refine ⟨11892162663987116015489573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7928108442658077343659715 11892162663987116015489573)
                    ·
                      refine ⟨2229780499497584252904295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11892162663987116015489573 2229780499497584252904295)
                      ·
                        rfl

theorem cell23_4342482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 2, 1, 2, 1, 4].length) (baseStart_4342482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4342482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4342482 prefixEnd_4342482 := by exact prefixLift 4342482
  have htrace : WordTrace (prefixWord ++ tailWord_4342482) baseStart_4342482 baseEnd_4342482 := by
    simpa [prefixWord, tailWord_4342482, baseEnd_4342482] using wordTrace_append hprefix tailTrace_4342482
  have hstable : (prefixWord ++ tailWord_4342482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4342482).length < 2 ^ (prefixWord ++ tailWord_4342482).sum := by decide
  have hdescent : baseEnd_4342482 < baseStart_4342482 := by decide
  rcases family_descends (prefixWord ++ tailWord_4342482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4342491 : List Nat := [1, 1, 1, 1, 1, 1, 1, 3, 5, 2, 6]
def baseStart_4342491 : Nat := 118140960795 + 4342491 * 2 ^ 59
def prefixEnd_4342491 : Nat := 4983230072969 + 3 ^ 40 * 4342491 * 2
def baseEnd_4342491 : Nat := 2229785120823474717691753

theorem tailTrace_4342491 : CollatzResearch.WordTrace tailWord_4342491 prefixEnd_4342491 2229785120823474717691753 := by
  unfold tailWord_4342491
  simp only [CollatzResearch.WordTrace]
  refine ⟨158383658510904220263059327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105589105673936146842039551 158383658510904220263059327)
  ·
    refine ⟨237575487766356330394588991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158383658510904220263059327 237575487766356330394588991)
    ·
      refine ⟨356363231649534495591883487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 237575487766356330394588991 356363231649534495591883487)
      ·
        refine ⟨534544847474301743387825231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 356363231649534495591883487 534544847474301743387825231)
        ·
          refine ⟨801817271211452615081737847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 534544847474301743387825231 801817271211452615081737847)
          ·
            refine ⟨1202725906817178922622606771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 801817271211452615081737847 1202725906817178922622606771)
            ·
              refine ⟨1804088860225768383933910157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1202725906817178922622606771 1804088860225768383933910157)
              ·
                refine ⟨676533322584663143975216309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1804088860225768383933910157 676533322584663143975216309)
                ·
                  refine ⟨63424998992312169747676529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 676533322584663143975216309 63424998992312169747676529)
                  ·
                    refine ⟨47568749244234127310757397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 63424998992312169747676529 47568749244234127310757397)
                    ·
                      refine ⟨2229785120823474717691753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 47568749244234127310757397 2229785120823474717691753)
                      ·
                        rfl

theorem cell23_4342491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 5, 2, 6].length) (baseStart_4342491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4342491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4342491 prefixEnd_4342491 := by exact prefixLift 4342491
  have htrace : WordTrace (prefixWord ++ tailWord_4342491) baseStart_4342491 baseEnd_4342491 := by
    simpa [prefixWord, tailWord_4342491, baseEnd_4342491] using wordTrace_append hprefix tailTrace_4342491
  have hstable : (prefixWord ++ tailWord_4342491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4342491).length < 2 ^ (prefixWord ++ tailWord_4342491).sum := by decide
  have hdescent : baseEnd_4342491 < baseStart_4342491 := by decide
  rcases family_descends (prefixWord ++ tailWord_4342491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4342515 : List Nat := [1, 1, 1, 2, 2, 3, 1, 5, 3, 1, 3]
def baseStart_4342515 : Nat := 118140960795 + 4342515 * 2 ^ 59
def prefixEnd_4342515 : Nat := 4983230072969 + 3 ^ 40 * 4342515 * 2
def baseEnd_4342515 : Nat := 2229797444359182623791643

theorem tailTrace_4342515 : CollatzResearch.WordTrace tailWord_4342515 prefixEnd_4342515 2229797444359182623791643 := by
  unfold tailWord_4342515
  simp only [CollatzResearch.WordTrace]
  refine ⟨158384533862817272361932999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105589689241878181574621999 158384533862817272361932999)
  ·
    refine ⟨237576800794225908542899499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158384533862817272361932999 237576800794225908542899499)
    ·
      refine ⟨356365201191338862814349249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 237576800794225908542899499 356365201191338862814349249)
      ·
        refine ⟨267273900893504147110761937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 356365201191338862814349249 267273900893504147110761937)
        ·
          refine ⟨200455425670128110333071453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 267273900893504147110761937 200455425670128110333071453)
          ·
            refine ⟨75170784626298041374901795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 200455425670128110333071453 75170784626298041374901795)
            ·
              refine ⟨112756176939447062062352693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75170784626298041374901795 112756176939447062062352693)
              ·
                refine ⟨10570891588073162068345565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 112756176939447062062352693 10570891588073162068345565)
                ·
                  refine ⟨3964084345527435775629587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10570891588073162068345565 3964084345527435775629587)
                  ·
                    refine ⟨5946126518291153663444381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3964084345527435775629587 5946126518291153663444381)
                    ·
                      refine ⟨2229797444359182623791643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5946126518291153663444381 2229797444359182623791643)
                      ·
                        rfl

theorem cell23_4342515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 5, 3, 1, 3].length) (baseStart_4342515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4342515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4342515 prefixEnd_4342515 := by exact prefixLift 4342515
  have htrace : WordTrace (prefixWord ++ tailWord_4342515) baseStart_4342515 baseEnd_4342515 := by
    simpa [prefixWord, tailWord_4342515, baseEnd_4342515] using wordTrace_append hprefix tailTrace_4342515
  have hstable : (prefixWord ++ tailWord_4342515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4342515).length < 2 ^ (prefixWord ++ tailWord_4342515).sum := by decide
  have hdescent : baseEnd_4342515 < baseStart_4342515 := by decide
  rcases family_descends (prefixWord ++ tailWord_4342515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4342516 : List Nat := [2, 6, 1, 1, 2, 1, 1, 1, 2, 4, 2]
def baseStart_4342516 : Nat := 118140960795 + 4342516 * 2 ^ 59
def prefixEnd_4342516 : Nat := 4983230072969 + 3 ^ 40 * 4342516 * 2
def baseEnd_4342516 : Nat := 2229797957839837119879139

theorem tailTrace_4342516 : CollatzResearch.WordTrace tailWord_4342516 prefixEnd_4342516 2229797957839837119879139 := by
  unfold tailWord_4342516
  simp only [CollatzResearch.WordTrace]
  refine ⟨79192285167906824766359701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105589713557209099688479601 79192285167906824766359701)
  ·
    refine ⟨3712138367245632410923111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 79192285167906824766359701 3712138367245632410923111)
    ·
      refine ⟨5568207550868448616384667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3712138367245632410923111 5568207550868448616384667)
      ·
        refine ⟨8352311326302672924577001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5568207550868448616384667 8352311326302672924577001)
        ·
          refine ⟨6264233494727004693432751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8352311326302672924577001 6264233494727004693432751)
          ·
            refine ⟨9396350242090507040149127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6264233494727004693432751 9396350242090507040149127)
            ·
              refine ⟨14094525363135760560223691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9396350242090507040149127 14094525363135760560223691)
              ·
                refine ⟨21141788044703640840335537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14094525363135760560223691 21141788044703640840335537)
                ·
                  refine ⟨15856341033527730630251653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21141788044703640840335537 15856341033527730630251653)
                  ·
                    refine ⟨2973063943786449493172185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15856341033527730630251653 2973063943786449493172185)
                    ·
                      refine ⟨2229797957839837119879139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2973063943786449493172185 2229797957839837119879139)
                      ·
                        rfl

theorem cell23_4342516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 1, 1, 2, 4, 2].length) (baseStart_4342516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4342516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4342516 prefixEnd_4342516 := by exact prefixLift 4342516
  have htrace : WordTrace (prefixWord ++ tailWord_4342516) baseStart_4342516 baseEnd_4342516 := by
    simpa [prefixWord, tailWord_4342516, baseEnd_4342516] using wordTrace_append hprefix tailTrace_4342516
  have hstable : (prefixWord ++ tailWord_4342516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4342516).length < 2 ^ (prefixWord ++ tailWord_4342516).sum := by decide
  have hdescent : baseEnd_4342516 < baseStart_4342516 := by decide
  rcases family_descends (prefixWord ++ tailWord_4342516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4342525 : List Nat := [1, 4, 1, 1, 1, 1, 4, 2, 1, 5, 2]
def baseStart_4342525 : Nat := 118140960795 + 4342525 * 2 ^ 59
def prefixEnd_4342525 : Nat := 4983230072969 + 3 ^ 40 * 4342525 * 2
def baseEnd_4342525 : Nat := 2229802579165727584666597

theorem tailTrace_4342525 : CollatzResearch.WordTrace tailWord_4342525 prefixEnd_4342525 2229802579165727584666597 := by
  unfold tailWord_4342525
  simp only [CollatzResearch.WordTrace]
  refine ⟨158384898592781044069797029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105589932395187362713198019 158384898592781044069797029)
  ·
    refine ⟨29697168486146445763086943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 158384898592781044069797029 29697168486146445763086943)
    ·
      refine ⟨44545752729219668644630415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29697168486146445763086943 44545752729219668644630415)
      ·
        refine ⟨66818629093829502966945623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44545752729219668644630415 66818629093829502966945623)
        ·
          refine ⟨100227943640744254450418435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66818629093829502966945623 100227943640744254450418435)
          ·
            refine ⟨150341915461116381675627653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 100227943640744254450418435 150341915461116381675627653)
            ·
              refine ⟨28189109148959321564180185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 150341915461116381675627653 28189109148959321564180185)
              ·
                refine ⟨21141831861719491173135139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28189109148959321564180185 21141831861719491173135139)
                ·
                  refine ⟨31712747792579236759702709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21141831861719491173135139 31712747792579236759702709)
                  ·
                    refine ⟨2973070105554303446222129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 31712747792579236759702709 2973070105554303446222129)
                    ·
                      refine ⟨2229802579165727584666597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2973070105554303446222129 2229802579165727584666597)
                      ·
                        rfl

theorem cell23_4342525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 4, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 4, 2, 1, 5, 2].length) (baseStart_4342525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4342525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4342525 prefixEnd_4342525 := by exact prefixLift 4342525
  have htrace : WordTrace (prefixWord ++ tailWord_4342525) baseStart_4342525 baseEnd_4342525 := by
    simpa [prefixWord, tailWord_4342525, baseEnd_4342525] using wordTrace_append hprefix tailTrace_4342525
  have hstable : (prefixWord ++ tailWord_4342525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4342525).length < 2 ^ (prefixWord ++ tailWord_4342525).sum := by decide
  have hdescent : baseEnd_4342525 < baseStart_4342525 := by decide
  rcases family_descends (prefixWord ++ tailWord_4342525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4342532 : List Nat := [2, 3, 2, 2, 1, 1, 3, 2, 3, 1, 3]
def baseStart_4342532 : Nat := 118140960795 + 4342532 * 2 ^ 59
def prefixEnd_4342532 : Nat := 4983230072969 + 3 ^ 40 * 4342532 * 2
def baseEnd_4342532 : Nat := 2229806173530309057279065

theorem tailTrace_4342532 : CollatzResearch.WordTrace tailWord_4342532 prefixEnd_4342532 2229806173530309057279065 := by
  unfold tailWord_4342532
  simp only [CollatzResearch.WordTrace]
  refine ⟨79192576951877842132650925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105590102602503789510201233 79192576951877842132650925)
  ·
    refine ⟨29697216356954190799744097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79192576951877842132650925 29697216356954190799744097)
    ·
      refine ⟨22272912267715643099808073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29697216356954190799744097 22272912267715643099808073)
      ·
        refine ⟨16704684200786732324856055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22272912267715643099808073 16704684200786732324856055)
        ·
          refine ⟨25057026301180098487284083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16704684200786732324856055 25057026301180098487284083)
          ·
            refine ⟨37585539451770147730926125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25057026301180098487284083 37585539451770147730926125)
            ·
              refine ⟨14094577294413805399097297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37585539451770147730926125 14094577294413805399097297)
              ·
                refine ⟨10570932970810354049322973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14094577294413805399097297 10570932970810354049322973)
                ·
                  refine ⟨3964099864053882768496115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10570932970810354049322973 3964099864053882768496115)
                  ·
                    refine ⟨5946149796080824152744173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3964099864053882768496115 5946149796080824152744173)
                    ·
                      refine ⟨2229806173530309057279065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5946149796080824152744173 2229806173530309057279065)
                      ·
                        rfl

theorem cell23_4342532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 3, 2, 3, 1, 3].length) (baseStart_4342532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4342532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4342532 prefixEnd_4342532 := by exact prefixLift 4342532
  have htrace : WordTrace (prefixWord ++ tailWord_4342532) baseStart_4342532 baseEnd_4342532 := by
    simpa [prefixWord, tailWord_4342532, baseEnd_4342532] using wordTrace_append hprefix tailTrace_4342532
  have hstable : (prefixWord ++ tailWord_4342532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4342532).length < 2 ^ (prefixWord ++ tailWord_4342532).sum := by decide
  have hdescent : baseEnd_4342532 < baseStart_4342532 := by decide
  rcases family_descends (prefixWord ++ tailWord_4342532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4342535 : List Nat := [1, 1, 4, 4, 1, 1, 2, 1, 3, 5]
def baseStart_4342535 : Nat := 118140960795 + 4342535 * 2 ^ 59
def prefixEnd_4342535 : Nat := 4983230072969 + 3 ^ 40 * 4342535 * 2
def baseEnd_4342535 : Nat := 743269237990757515180517

theorem tailTrace_4342535 : CollatzResearch.WordTrace tailWord_4342535 prefixEnd_4342535 743269237990757515180517 := by
  unfold tailWord_4342535
  simp only [CollatzResearch.WordTrace]
  refine ⟨158385263322744815777661059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105590175548496543851774039 158385263322744815777661059)
  ·
    refine ⟨237577894984117223666491589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158385263322744815777661059 237577894984117223666491589)
    ·
      refine ⟨44545855309521979437467173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 237577894984117223666491589 44545855309521979437467173)
      ·
        refine ⟨8352347870535371144525095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 44545855309521979437467173 8352347870535371144525095)
        ·
          refine ⟨12528521805803056716787643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8352347870535371144525095 12528521805803056716787643)
          ·
            refine ⟨18792782708704585075181465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12528521805803056716787643 18792782708704585075181465)
            ·
              refine ⟨14094587031528438806386099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18792782708704585075181465 14094587031528438806386099)
              ·
                refine ⟨21141880547292658209579149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14094587031528438806386099 21141880547292658209579149)
                ·
                  refine ⟨7928205205234746828592181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21141880547292658209579149 7928205205234746828592181)
                  ·
                    refine ⟨743269237990757515180517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7928205205234746828592181 743269237990757515180517)
                    ·
                      rfl

theorem cell23_4342535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 2, 1, 3, 5].length) (baseStart_4342535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4342535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4342535 prefixEnd_4342535 := by exact prefixLift 4342535
  have htrace : WordTrace (prefixWord ++ tailWord_4342535) baseStart_4342535 baseEnd_4342535 := by
    simpa [prefixWord, tailWord_4342535, baseEnd_4342535] using wordTrace_append hprefix tailTrace_4342535
  have hstable : (prefixWord ++ tailWord_4342535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4342535).length < 2 ^ (prefixWord ++ tailWord_4342535).sum := by decide
  have hdescent : baseEnd_4342535 < baseStart_4342535 := by decide
  rcases family_descends (prefixWord ++ tailWord_4342535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4342549 : List Nat := [1, 3, 2, 1, 2, 2, 4, 3, 1, 1, 3]
def baseStart_4342549 : Nat := 118140960795 + 4342549 * 2 ^ 59
def prefixEnd_4342549 : Nat := 4983230072969 + 3 ^ 40 * 4342549 * 2
def baseEnd_4342549 : Nat := 2229814902701435490766487

theorem tailTrace_4342549 : CollatzResearch.WordTrace tailWord_4342549 prefixEnd_4342549 2229814902701435490766487 := by
  unfold tailWord_4342549
  simp only [CollatzResearch.WordTrace]
  refine ⟨158385773944694096168670701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105590515963129397445780467 158385773944694096168670701)
  ·
    refine ⟨59394665229260286063251513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 158385773944694096168670701 59394665229260286063251513)
    ·
      refine ⟨44545998921945214547438635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59394665229260286063251513 44545998921945214547438635)
      ·
        refine ⟨66818998382917821821157953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44545998921945214547438635 66818998382917821821157953)
        ·
          refine ⟨50114248787188366365868465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66818998382917821821157953 50114248787188366365868465)
          ·
            refine ⟨37585686590391274774401349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50114248787188366365868465 37585686590391274774401349)
            ·
              refine ⟨7047316235698364020200253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 37585686590391274774401349 7047316235698364020200253)
              ·
                refine ⟨2642743588386886507575095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7047316235698364020200253 2642743588386886507575095)
                ·
                  refine ⟨3964115382580329761362643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2642743588386886507575095 3964115382580329761362643)
                  ·
                    refine ⟨5946173073870494642043965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3964115382580329761362643 5946173073870494642043965)
                    ·
                      refine ⟨2229814902701435490766487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5946173073870494642043965 2229814902701435490766487)
                      ·
                        rfl

theorem cell23_4342549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 4, 3, 1, 1, 3].length) (baseStart_4342549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4342549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4342549 prefixEnd_4342549 := by exact prefixLift 4342549
  have htrace : WordTrace (prefixWord ++ tailWord_4342549) baseStart_4342549 baseEnd_4342549 := by
    simpa [prefixWord, tailWord_4342549, baseEnd_4342549] using wordTrace_append hprefix tailTrace_4342549
  have hstable : (prefixWord ++ tailWord_4342549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4342549).length < 2 ^ (prefixWord ++ tailWord_4342549).sum := by decide
  have hdescent : baseEnd_4342549 < baseStart_4342549 := by decide
  rcases family_descends (prefixWord ++ tailWord_4342549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4342565 : List Nat := [1, 3, 1, 2, 3, 1, 3, 1, 4, 4]
def baseStart_4342565 : Nat := 118140960795 + 4342565 * 2 ^ 59
def prefixEnd_4342565 : Nat := 4983230072969 + 3 ^ 40 * 4342565 * 2
def baseEnd_4342565 : Nat := 743274372797302476055471

theorem tailTrace_4342565 : CollatzResearch.WordTrace tailWord_4342565 prefixEnd_4342565 743274372797302476055471 := by
  unfold tailWord_4342565
  simp only [CollatzResearch.WordTrace]
  refine ⟨158386357512636130901253149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105590905008424087267502099 158386357512636130901253149)
  ·
    refine ⟨59394884067238549087969931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 158386357512636130901253149 59394884067238549087969931)
    ·
      refine ⟨89092326100857823631954897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59394884067238549087969931 89092326100857823631954897)
      ·
        refine ⟨66819244575643367723966173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89092326100857823631954897 66819244575643367723966173)
        ·
          refine ⟨25057216715866262896487315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 66819244575643367723966173 25057216715866262896487315)
          ·
            refine ⟨37585825073799394344730973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25057216715866262896487315 37585825073799394344730973)
            ·
              refine ⟨14094684402674772879274115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37585825073799394344730973 14094684402674772879274115)
              ·
                refine ⟨21142026604012159318911173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14094684402674772879274115 21142026604012159318911173)
                ·
                  refine ⟨3964129988252279872295845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21142026604012159318911173 3964129988252279872295845)
                  ·
                    refine ⟨743274372797302476055471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3964129988252279872295845 743274372797302476055471)
                    ·
                      rfl

theorem cell23_4342565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 3, 1, 4, 4].length) (baseStart_4342565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4342565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4342565 prefixEnd_4342565 := by exact prefixLift 4342565
  have htrace : WordTrace (prefixWord ++ tailWord_4342565) baseStart_4342565 baseEnd_4342565 := by
    simpa [prefixWord, tailWord_4342565, baseEnd_4342565] using wordTrace_append hprefix tailTrace_4342565
  have hstable : (prefixWord ++ tailWord_4342565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4342565).length < 2 ^ (prefixWord ++ tailWord_4342565).sum := by decide
  have hdescent : baseEnd_4342565 < baseStart_4342565 := by decide
  rcases family_descends (prefixWord ++ tailWord_4342565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4342578 : List Nat := [3, 2, 1, 1, 3, 1, 2, 10]
def baseStart_4342578 : Nat := 118140960795 + 4342578 * 2 ^ 59
def prefixEnd_4342578 : Nat := 4983230072969 + 3 ^ 40 * 4342578 * 2
def baseEnd_4342578 : Nat := 82586288653348736196439

theorem tailTrace_4342578 : CollatzResearch.WordTrace tailWord_4342578 prefixEnd_4342578 82586288653348736196439 := by
  unfold tailWord_4342578
  simp only [CollatzResearch.WordTrace]
  refine ⟨39596707915397258530369097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105591221107726022747650925 39596707915397258530369097)
  ·
    refine ⟨29697530936547943897776823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39596707915397258530369097 29697530936547943897776823)
    ·
      refine ⟨44546296404821915846665235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29697530936547943897776823 44546296404821915846665235)
      ·
        refine ⟨66819444607232873769997853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44546296404821915846665235 66819444607232873769997853)
        ·
          refine ⟨25057291727712327663749195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 66819444607232873769997853 25057291727712327663749195)
          ·
            refine ⟨37585937591568491495623793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25057291727712327663749195 37585937591568491495623793)
            ·
              refine ⟨28189453193676368621717845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37585937591568491495623793 28189453193676368621717845)
              ·
                refine ⟨82586288653348736196439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 28189453193676368621717845 82586288653348736196439)
                ·
                  rfl

theorem cell23_4342578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 2, 10].length) (baseStart_4342578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4342578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4342578 prefixEnd_4342578 := by exact prefixLift 4342578
  have htrace : WordTrace (prefixWord ++ tailWord_4342578) baseStart_4342578 baseEnd_4342578 := by
    simpa [prefixWord, tailWord_4342578, baseEnd_4342578] using wordTrace_append hprefix tailTrace_4342578
  have hstable : (prefixWord ++ tailWord_4342578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4342578).length < 2 ^ (prefixWord ++ tailWord_4342578).sum := by decide
  have hdescent : baseEnd_4342578 < baseStart_4342578 := by decide
  rcases family_descends (prefixWord ++ tailWord_4342578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4342589 : List Nat := [1, 4, 1, 4, 2, 1, 2, 2, 1, 1, 4]
def baseStart_4342589 : Nat := 118140960795 + 4342589 * 2 ^ 59
def prefixEnd_4342589 : Nat := 4983230072969 + 3 ^ 40 * 4342589 * 2
def baseEnd_4342589 : Nat := 2229835441927615334266303

theorem tailTrace_4342589 : CollatzResearch.WordTrace tailWord_4342589 prefixEnd_4342589 2229835441927615334266303 := by
  unfold tailWord_4342589
  simp only [CollatzResearch.WordTrace]
  refine ⟨158387232864549183000126821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105591488576366122000084547 158387232864549183000126821)
  ·
    refine ⟨29697606162102971812523779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 158387232864549183000126821 29697606162102971812523779)
    ·
      refine ⟨44546409243154457718785669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29697606162102971812523779 44546409243154457718785669)
      ·
        refine ⟨8352451733091460822272313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 44546409243154457718785669 8352451733091460822272313)
        ·
          refine ⟨6264338799818595616704235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8352451733091460822272313 6264338799818595616704235)
          ·
            refine ⟨9396508199727893425056353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6264338799818595616704235 9396508199727893425056353)
            ·
              refine ⟨7047381149795920068792265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9396508199727893425056353 7047381149795920068792265)
              ·
                refine ⟨5285535862346940051594199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7047381149795920068792265 5285535862346940051594199)
                ·
                  refine ⟨7928303793520410077391299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5285535862346940051594199 7928303793520410077391299)
                  ·
                    refine ⟨11892455690280615116086949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7928303793520410077391299 11892455690280615116086949)
                    ·
                      refine ⟨2229835441927615334266303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11892455690280615116086949 2229835441927615334266303)
                      ·
                        rfl

theorem cell23_4342589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 2, 2, 1, 1, 4].length) (baseStart_4342589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4342589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4342589 prefixEnd_4342589 := by exact prefixLift 4342589
  have htrace : WordTrace (prefixWord ++ tailWord_4342589) baseStart_4342589 baseEnd_4342589 := by
    simpa [prefixWord, tailWord_4342589, baseEnd_4342589] using wordTrace_append hprefix tailTrace_4342589
  have hstable : (prefixWord ++ tailWord_4342589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4342589).length < 2 ^ (prefixWord ++ tailWord_4342589).sum := by decide
  have hdescent : baseEnd_4342589 < baseStart_4342589 := by decide
  rcases family_descends (prefixWord ++ tailWord_4342589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4342612 : List Nat := [2, 4, 1, 1, 5, 1, 9]
def baseStart_4342612 : Nat := 118140960795 + 4342612 * 2 ^ 59
def prefixEnd_4342612 : Nat := 4983230072969 + 3 ^ 40 * 4342612 * 2
def baseEnd_4342612 : Nat := 27528978419539120299737

theorem tailTrace_4342612 : CollatzResearch.WordTrace tailWord_4342612 prefixEnd_4342612 27528978419539120299737 := by
  unfold tailWord_4342612
  simp only [CollatzResearch.WordTrace]
  refine ⟨79194035871732928964107045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105592047828977238618809393 79194035871732928964107045)
  ·
    refine ⟨14848881725949924180770071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 79194035871732928964107045 14848881725949924180770071)
    ·
      refine ⟨22273322588924886271155107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14848881725949924180770071 22273322588924886271155107)
      ·
        refine ⟨33409983883387329406732661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22273322588924886271155107 33409983883387329406732661)
        ·
          refine ⟨3132185989067562131881187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 33409983883387329406732661 3132185989067562131881187)
          ·
            refine ⟨4698278983601343197821781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3132185989067562131881187 4698278983601343197821781)
            ·
              refine ⟨27528978419539120299737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4698278983601343197821781 27528978419539120299737)
              ·
                rfl

theorem cell23_4342612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 5, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 5, 1, 9].length) (baseStart_4342612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4342612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4342612 prefixEnd_4342612 := by exact prefixLift 4342612
  have htrace : WordTrace (prefixWord ++ tailWord_4342612) baseStart_4342612 baseEnd_4342612 := by
    simpa [prefixWord, tailWord_4342612, baseEnd_4342612] using wordTrace_append hprefix tailTrace_4342612
  have hstable : (prefixWord ++ tailWord_4342612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4342612).length < 2 ^ (prefixWord ++ tailWord_4342612).sum := by decide
  have hdescent : baseEnd_4342612 < baseStart_4342612 := by decide
  rcases family_descends (prefixWord ++ tailWord_4342612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4342649 : List Nat := [1, 2, 1, 3, 2, 3, 3, 2, 1, 3, 2]
def baseStart_4342649 : Nat := 118140960795 + 4342649 * 2 ^ 59
def prefixEnd_4342649 : Nat := 4983230072969 + 3 ^ 40 * 4342649 * 2
def baseEnd_4342649 : Nat := 2229866250766885099516027

theorem tailTrace_4342649 : CollatzResearch.WordTrace tailWord_4342649 prefixEnd_4342649 2229866250766885099516027 := by
  unfold tailWord_4342649
  simp only [CollatzResearch.WordTrace]
  refine ⟨158389421244331813247311001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105592947496221208831540667 158389421244331813247311001)
  ·
    refine ⟨118792065933248859935483251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 158389421244331813247311001 118792065933248859935483251)
    ·
      refine ⟨178188098899873289903224877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118792065933248859935483251 178188098899873289903224877)
      ·
        refine ⟨66820537087452483713709329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 178188098899873289903224877 66820537087452483713709329)
        ·
          refine ⟨50115402815589362785281997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66820537087452483713709329 50115402815589362785281997)
          ·
            refine ⟨18793276055846011044480749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50115402815589362785281997 18793276055846011044480749)
            ·
              refine ⟨7047478520942254141680281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18793276055846011044480749 7047478520942254141680281)
              ·
                refine ⟨5285608890706690606260211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7047478520942254141680281 5285608890706690606260211)
                ·
                  refine ⟨7928413336060035909390317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5285608890706690606260211 7928413336060035909390317)
                  ·
                    refine ⟨2973155001022513466021369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7928413336060035909390317 2973155001022513466021369)
                    ·
                      refine ⟨2229866250766885099516027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2973155001022513466021369 2229866250766885099516027)
                      ·
                        rfl

theorem cell23_4342649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 3, 2, 1, 3, 2].length) (baseStart_4342649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4342649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4342649 prefixEnd_4342649 := by exact prefixLift 4342649
  have htrace : WordTrace (prefixWord ++ tailWord_4342649) baseStart_4342649 baseEnd_4342649 := by
    simpa [prefixWord, tailWord_4342649, baseEnd_4342649] using wordTrace_append hprefix tailTrace_4342649
  have hstable : (prefixWord ++ tailWord_4342649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4342649).length < 2 ^ (prefixWord ++ tailWord_4342649).sum := by decide
  have hdescent : baseEnd_4342649 < baseStart_4342649 := by decide
  rcases family_descends (prefixWord ++ tailWord_4342649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4342665 : List Nat := [1, 2, 1, 1, 5, 2, 2, 1, 2, 1, 5]
def baseStart_4342665 : Nat := 118140960795 + 4342665 * 2 ^ 59
def prefixEnd_4342665 : Nat := 4983230072969 + 3 ^ 40 * 4342665 * 2
def baseEnd_4342665 : Nat := 2229874466457357036915953

theorem tailTrace_4342665 : CollatzResearch.WordTrace tailWord_4342665 prefixEnd_4342665 2229874466457357036915953 := by
  unfold tailWord_4342665
  simp only [CollatzResearch.WordTrace]
  refine ⟨158390004812273847979893449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105593336541515898653262299 158390004812273847979893449)
  ·
    refine ⟨118792503609205385984920087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 158390004812273847979893449 118792503609205385984920087)
    ·
      refine ⟨178188755413808078977380131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118792503609205385984920087 178188755413808078977380131)
      ·
        refine ⟨267283133120712118466070197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 178188755413808078977380131 267283133120712118466070197)
        ·
          refine ⟨25057793730066761106194081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 267283133120712118466070197 25057793730066761106194081)
          ·
            refine ⟨18793345297550070829645561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25057793730066761106194081 18793345297550070829645561)
            ·
              refine ⟨14095008973162553122234171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18793345297550070829645561 14095008973162553122234171)
              ·
                refine ⟨21142513459743829683351257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14095008973162553122234171 21142513459743829683351257)
                ·
                  refine ⟨15856885094807872262513443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21142513459743829683351257 15856885094807872262513443)
                  ·
                    refine ⟨23785327642211808393770165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15856885094807872262513443 23785327642211808393770165)
                    ·
                      refine ⟨2229874466457357036915953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23785327642211808393770165 2229874466457357036915953)
                      ·
                        rfl

theorem cell23_4342665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 2, 1, 2, 1, 5].length) (baseStart_4342665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4342665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4342665 prefixEnd_4342665 := by exact prefixLift 4342665
  have htrace : WordTrace (prefixWord ++ tailWord_4342665) baseStart_4342665 baseEnd_4342665 := by
    simpa [prefixWord, tailWord_4342665, baseEnd_4342665] using wordTrace_append hprefix tailTrace_4342665
  have hstable : (prefixWord ++ tailWord_4342665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4342665).length < 2 ^ (prefixWord ++ tailWord_4342665).sum := by decide
  have hdescent : baseEnd_4342665 < baseStart_4342665 := by decide
  rcases family_descends (prefixWord ++ tailWord_4342665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4342685 : List Nat := [1, 4, 2, 1, 2, 1, 2, 3, 7]
def baseStart_4342685 : Nat := 118140960795 + 4342685 * 2 ^ 59
def prefixEnd_4342685 : Nat := 4983230072969 + 3 ^ 40 * 4342685 * 2
def baseEnd_4342685 : Nat := 247764970674494106518429

theorem tailTrace_4342685 : CollatzResearch.WordTrace tailWord_4342685 prefixEnd_4342685 247764970674494106518429 := by
  unfold tailWord_4342685
  simp only [CollatzResearch.WordTrace]
  refine ⟨158390734272201391395621509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105593822848134260930414339 158390734272201391395621509)
  ·
    refine ⟨29698262676037760886679033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 158390734272201391395621509 29698262676037760886679033)
    ·
      refine ⟨22273697007028320665009275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29698262676037760886679033 22273697007028320665009275)
      ·
        refine ⟨33410545510542480997513913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22273697007028320665009275 33410545510542480997513913)
        ·
          refine ⟨25057909132906860748135435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33410545510542480997513913 25057909132906860748135435)
          ·
            refine ⟨37586863699360291122203153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25057909132906860748135435 37586863699360291122203153)
            ·
              refine ⟨28190147774520218341652365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37586863699360291122203153 28190147774520218341652365)
              ·
                refine ⟨10571305415445081878119637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28190147774520218341652365 10571305415445081878119637)
                ·
                  refine ⟨247764970674494106518429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10571305415445081878119637 247764970674494106518429)
                  ·
                    rfl

theorem cell23_4342685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 2, 3, 7].length) (baseStart_4342685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4342685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4342685 prefixEnd_4342685 := by exact prefixLift 4342685
  have htrace : WordTrace (prefixWord ++ tailWord_4342685) baseStart_4342685 baseEnd_4342685 := by
    simpa [prefixWord, tailWord_4342685, baseEnd_4342685] using wordTrace_append hprefix tailTrace_4342685
  have hstable : (prefixWord ++ tailWord_4342685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4342685).length < 2 ^ (prefixWord ++ tailWord_4342685).sum := by decide
  have hdescent : baseEnd_4342685 < baseStart_4342685 := by decide
  rcases family_descends (prefixWord ++ tailWord_4342685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4342853 : List Nat := [1, 3, 1, 1, 1, 3, 6, 2, 1, 1, 3]
def baseStart_4342853 : Nat := 118140960795 + 4342853 * 2 ^ 59
def prefixEnd_4342853 : Nat := 4983230072969 + 3 ^ 40 * 4342853 * 2
def baseEnd_4342853 : Nat := 2229971000820402301365089

theorem tailTrace_4342853 : CollatzResearch.WordTrace tailWord_4342853 prefixEnd_4342853 2229971000820402301365089 := by
  unfold tailWord_4342853
  simp only [CollatzResearch.WordTrace]
  refine ⟨158396861735592756087737213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105597907823728504058491475 158396861735592756087737213)
  ·
    refine ⟨59398823150847283532901455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 158396861735592756087737213 59398823150847283532901455)
    ·
      refine ⟨89098234726270925299352183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59398823150847283532901455 89098234726270925299352183)
      ·
        refine ⟨133647352089406387949028275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89098234726270925299352183 133647352089406387949028275)
        ·
          refine ⟨200471028134109581923542413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 133647352089406387949028275 200471028134109581923542413)
          ·
            refine ⟨75176635550291093221328405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 200471028134109581923542413 75176635550291093221328405)
            ·
              refine ⟨3523904791419894994749769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 75176635550291093221328405 3523904791419894994749769)
              ·
                refine ⟨2642928593564921246062327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3523904791419894994749769 2642928593564921246062327)
                ·
                  refine ⟨3964392890347381869093491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2642928593564921246062327 3964392890347381869093491)
                  ·
                    refine ⟨5946589335521072803640237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3964392890347381869093491 5946589335521072803640237)
                    ·
                      refine ⟨2229971000820402301365089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5946589335521072803640237 2229971000820402301365089)
                      ·
                        rfl

theorem cell23_4342853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 6, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 6, 2, 1, 1, 3].length) (baseStart_4342853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4342853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4342853 prefixEnd_4342853 := by exact prefixLift 4342853
  have htrace : WordTrace (prefixWord ++ tailWord_4342853) baseStart_4342853 baseEnd_4342853 := by
    simpa [prefixWord, tailWord_4342853, baseEnd_4342853] using wordTrace_append hprefix tailTrace_4342853
  have hstable : (prefixWord ++ tailWord_4342853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4342853).length < 2 ^ (prefixWord ++ tailWord_4342853).sum := by decide
  have hdescent : baseEnd_4342853 < baseStart_4342853 := by decide
  rcases family_descends (prefixWord ++ tailWord_4342853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4342862 : List Nat := [4, 1, 1, 1, 1, 3, 2, 1, 3, 1, 5]
def baseStart_4342862 : Nat := 118140960795 + 4342862 * 2 ^ 59
def prefixEnd_4342862 : Nat := 4983230072969 + 3 ^ 40 * 4342862 * 2
def baseEnd_4342862 : Nat := 2229975622146292766152547

theorem tailTrace_4342862 : CollatzResearch.WordTrace tailWord_4342862 prefixEnd_4342862 2229975622146292766152547 := by
  unfold tailWord_4342862
  simp only [CollatzResearch.WordTrace]
  refine ⟨19799648749070018828101855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 105598126661706767083209893 19799648749070018828101855)
  ·
    refine ⟨29699473123605028242152783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19799648749070018828101855 29699473123605028242152783)
    ·
      refine ⟨44549209685407542363229175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29699473123605028242152783 44549209685407542363229175)
      ·
        refine ⟨66823814528111313544843763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44549209685407542363229175 66823814528111313544843763)
        ·
          refine ⟨100235721792166970317265645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66823814528111313544843763 100235721792166970317265645)
          ·
            refine ⟨37588395672062613868974617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 100235721792166970317265645 37588395672062613868974617)
            ·
              refine ⟨28191296754046960401730963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37588395672062613868974617 28191296754046960401730963)
              ·
                refine ⟨42286945131070440602596445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28191296754046960401730963 42286945131070440602596445)
                ·
                  refine ⟨15857604424151415225973667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 42286945131070440602596445 15857604424151415225973667)
                  ·
                    refine ⟨23786406636227122838960501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15857604424151415225973667 23786406636227122838960501)
                    ·
                      refine ⟨2229975622146292766152547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23786406636227122838960501 2229975622146292766152547)
                      ·
                        rfl

theorem cell23_4342862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 2, 1, 3, 1, 5].length) (baseStart_4342862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4342862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4342862 prefixEnd_4342862 := by exact prefixLift 4342862
  have htrace : WordTrace (prefixWord ++ tailWord_4342862) baseStart_4342862 baseEnd_4342862 := by
    simpa [prefixWord, tailWord_4342862, baseEnd_4342862] using wordTrace_append hprefix tailTrace_4342862
  have hstable : (prefixWord ++ tailWord_4342862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4342862).length < 2 ^ (prefixWord ++ tailWord_4342862).sum := by decide
  have hdescent : baseEnd_4342862 < baseStart_4342862 := by decide
  rcases family_descends (prefixWord ++ tailWord_4342862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4342869 : List Nat := [1, 3, 2, 2, 1, 2, 1, 5, 2, 4]
def baseStart_4342869 : Nat := 118140960795 + 4342869 * 2 ^ 59
def prefixEnd_4342869 : Nat := 4983230072969 + 3 ^ 40 * 4342869 * 2
def baseEnd_4342869 : Nat := 743326405503624746255005

theorem tailTrace_4342869 : CollatzResearch.WordTrace tailWord_4342869 prefixEnd_4342869 743326405503624746255005 := by
  unfold tailWord_4342869
  simp only [CollatzResearch.WordTrace]
  refine ⟨158397445303534790820319661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105598296869023193880213107 158397445303534790820319661)
  ·
    refine ⟨59399041988825546557619873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 158397445303534790820319661 59399041988825546557619873)
    ·
      refine ⟨44549281491619159918214905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59399041988825546557619873 44549281491619159918214905)
      ·
        refine ⟨33411961118714369938661179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44549281491619159918214905 33411961118714369938661179)
        ·
          refine ⟨50117941678071554907991769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33411961118714369938661179 50117941678071554907991769)
          ·
            refine ⟨37588456258553666180993827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50117941678071554907991769 37588456258553666180993827)
            ·
              refine ⟨56382684387830499271490741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37588456258553666180993827 56382684387830499271490741)
              ·
                refine ⟨5285876661359109306702257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 56382684387830499271490741 5285876661359109306702257)
                ·
                  refine ⟨3964407496019331980026693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5285876661359109306702257 3964407496019331980026693)
                  ·
                    refine ⟨743326405503624746255005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3964407496019331980026693 743326405503624746255005)
                    ·
                      rfl

theorem cell23_4342869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 5, 2, 4].length) (baseStart_4342869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4342869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4342869 prefixEnd_4342869 := by exact prefixLift 4342869
  have htrace : WordTrace (prefixWord ++ tailWord_4342869) baseStart_4342869 baseEnd_4342869 := by
    simpa [prefixWord, tailWord_4342869, baseEnd_4342869] using wordTrace_append hprefix tailTrace_4342869
  have hstable : (prefixWord ++ tailWord_4342869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4342869).length < 2 ^ (prefixWord ++ tailWord_4342869).sum := by decide
  have hdescent : baseEnd_4342869 < baseStart_4342869 := by decide
  rcases family_descends (prefixWord ++ tailWord_4342869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4342870 : List Nat := [5, 2, 2, 1, 2, 1, 1, 2, 3, 1, 3]
def baseStart_4342870 : Nat := 118140960795 + 4342870 * 2 ^ 59
def prefixEnd_4342870 : Nat := 4983230072969 + 3 ^ 40 * 4342870 * 2
def baseEnd_4342870 : Nat := 2229979729991528734852511

theorem tailTrace_4342870 : CollatzResearch.WordTrace tailWord_4342870 prefixEnd_4342870 2229979729991528734852511 := by
  unfold tailWord_4342870
  simp only [CollatzResearch.WordTrace]
  refine ⟨9899842611033197999444129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 105598321184354111994070709 9899842611033197999444129)
  ·
    refine ⟨7424881958274898499583097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9899842611033197999444129 7424881958274898499583097)
    ·
      refine ⟨5568661468706173874687323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7424881958274898499583097 5568661468706173874687323)
      ·
        refine ⟨8352992203059260812030985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5568661468706173874687323 8352992203059260812030985)
        ·
          refine ⟨6264744152294445609023239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8352992203059260812030985 6264744152294445609023239)
          ·
            refine ⟨9397116228441668413534859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6264744152294445609023239 9397116228441668413534859)
            ·
              refine ⟨14095674342662502620302289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9397116228441668413534859 14095674342662502620302289)
              ·
                refine ⟨10571755756996876965226717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14095674342662502620302289 10571755756996876965226717)
                ·
                  refine ⟨3964408408873828861960019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10571755756996876965226717 3964408408873828861960019)
                  ·
                    refine ⟨5946612613310743292940029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3964408408873828861960019 5946612613310743292940029)
                    ·
                      refine ⟨2229979729991528734852511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5946612613310743292940029 2229979729991528734852511)
                      ·
                        rfl

theorem cell23_4342870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 1, 2, 3, 1, 3].length) (baseStart_4342870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4342870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4342870 prefixEnd_4342870 := by exact prefixLift 4342870
  have htrace : WordTrace (prefixWord ++ tailWord_4342870) baseStart_4342870 baseEnd_4342870 := by
    simpa [prefixWord, tailWord_4342870, baseEnd_4342870] using wordTrace_append hprefix tailTrace_4342870
  have hstable : (prefixWord ++ tailWord_4342870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4342870).length < 2 ^ (prefixWord ++ tailWord_4342870).sum := by decide
  have hdescent : baseEnd_4342870 < baseStart_4342870 := by decide
  rcases family_descends (prefixWord ++ tailWord_4342870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4342879 : List Nat := [1, 1, 2, 3, 1, 1, 4, 4, 1, 2, 3]
def baseStart_4342879 : Nat := 118140960795 + 4342879 * 2 ^ 59
def prefixEnd_4342879 : Nat := 4983230072969 + 3 ^ 40 * 4342879 * 2
def baseEnd_4342879 : Nat := 2229984351317419199639969

theorem tailTrace_4342879 : CollatzResearch.WordTrace tailWord_4342879 prefixEnd_4342879 2229984351317419199639969 := by
  unfold tailWord_4342879
  simp only [CollatzResearch.WordTrace]
  refine ⟨158397810033498562528183691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105598540022332375018789127 158397810033498562528183691)
  ·
    refine ⟨237596715050247843792275537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158397810033498562528183691 237596715050247843792275537)
    ·
      refine ⟨178197536287685882844206653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 237596715050247843792275537 178197536287685882844206653)
      ·
        refine ⟨66824076107882206066577495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 178197536287685882844206653 66824076107882206066577495)
        ·
          refine ⟨100236114161823309099866243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66824076107882206066577495 100236114161823309099866243)
          ·
            refine ⟨150354171242734963649799365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 100236114161823309099866243 150354171242734963649799365)
            ·
              refine ⟨28191407108012805684337381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 150354171242734963649799365 28191407108012805684337381)
              ·
                refine ⟨5285888832752401065813259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28191407108012805684337381 5285888832752401065813259)
                ·
                  refine ⟨7928833249128601598719889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5285888832752401065813259 7928833249128601598719889)
                  ·
                    refine ⟨5946624936846451199039917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7928833249128601598719889 5946624936846451199039917)
                    ·
                      refine ⟨2229984351317419199639969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5946624936846451199039917 2229984351317419199639969)
                      ·
                        rfl

theorem cell23_4342879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 4, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 4, 4, 1, 2, 3].length) (baseStart_4342879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4342879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4342879 prefixEnd_4342879 := by exact prefixLift 4342879
  have htrace : WordTrace (prefixWord ++ tailWord_4342879) baseStart_4342879 baseEnd_4342879 := by
    simpa [prefixWord, tailWord_4342879, baseEnd_4342879] using wordTrace_append hprefix tailTrace_4342879
  have hstable : (prefixWord ++ tailWord_4342879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4342879).length < 2 ^ (prefixWord ++ tailWord_4342879).sum := by decide
  have hdescent : baseEnd_4342879 < baseStart_4342879 := by decide
  rcases family_descends (prefixWord ++ tailWord_4342879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4342893 : List Nat := [1, 5, 1, 1, 2, 4, 2, 1, 1, 1, 4]
def baseStart_4342893 : Nat := 118140960795 + 4342893 * 2 ^ 59
def prefixEnd_4342893 : Nat := 4983230072969 + 3 ^ 40 * 4342893 * 2
def baseEnd_4342893 : Nat := 2229991540046582144864905

theorem tailTrace_4342893 : CollatzResearch.WordTrace tailWord_4342893 prefixEnd_4342893 2229991540046582144864905 := by
  unfold tailWord_4342893
  simp only [CollatzResearch.WordTrace]
  refine ⟨158398320655447842919193333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105598880436965228612795555 158398320655447842919193333)
  ·
    refine ⟨14849842561448235273674375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 158398320655447842919193333 14849842561448235273674375)
    ·
      refine ⟨22274763842172352910511563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14849842561448235273674375 22274763842172352910511563)
      ·
        refine ⟨33412145763258529365767345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22274763842172352910511563 33412145763258529365767345)
        ·
          refine ⟨25059109322443897024325509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33412145763258529365767345 25059109322443897024325509)
          ·
            refine ⟨4698582997958230692061033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25059109322443897024325509 4698582997958230692061033)
            ·
              refine ⟨3523937248468673019045775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4698582997958230692061033 3523937248468673019045775)
              ·
                refine ⟨5285905872703009528568663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3523937248468673019045775 5285905872703009528568663)
                ·
                  refine ⟨7928858809054514292852995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5285905872703009528568663 7928858809054514292852995)
                  ·
                    refine ⟨11893288213581771439279493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7928858809054514292852995 11893288213581771439279493)
                    ·
                      refine ⟨2229991540046582144864905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11893288213581771439279493 2229991540046582144864905)
                      ·
                        rfl

theorem cell23_4342893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 4, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 4, 2, 1, 1, 1, 4].length) (baseStart_4342893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4342893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4342893 prefixEnd_4342893 := by exact prefixLift 4342893
  have htrace : WordTrace (prefixWord ++ tailWord_4342893) baseStart_4342893 baseEnd_4342893 := by
    simpa [prefixWord, tailWord_4342893, baseEnd_4342893] using wordTrace_append hprefix tailTrace_4342893
  have hstable : (prefixWord ++ tailWord_4342893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4342893).length < 2 ^ (prefixWord ++ tailWord_4342893).sum := by decide
  have hdescent : baseEnd_4342893 < baseStart_4342893 := by decide
  rcases family_descends (prefixWord ++ tailWord_4342893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4342926 : List Nat := [4, 1, 1, 3, 2, 1, 3, 1, 1, 3, 3]
def baseStart_4342926 : Nat := 118140960795 + 4342926 * 2 ^ 59
def prefixEnd_4342926 : Nat := 4983230072969 + 3 ^ 40 * 4342926 * 2
def baseEnd_4342926 : Nat := 2230008484908180515752253

theorem tailTrace_4342926 : CollatzResearch.WordTrace tailWord_4342926 prefixEnd_4342926 2230008484908180515752253 := by
  unfold tailWord_4342926
  simp only [CollatzResearch.WordTrace]
  refine ⟨19799940533041036194393079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 105599682842885526370096421 19799940533041036194393079)
  ·
    refine ⟨29699910799561554291589619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19799940533041036194393079 29699910799561554291589619)
    ·
      refine ⟨44549866199342331437384429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29699910799561554291589619 44549866199342331437384429)
      ·
        refine ⟨16706199824753374289019161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44549866199342331437384429 16706199824753374289019161)
        ·
          refine ⟨12529649868565030716764371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16706199824753374289019161 12529649868565030716764371)
          ·
            refine ⟨18794474802847546075146557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12529649868565030716764371 18794474802847546075146557)
            ·
              refine ⟨7047928051067829778179959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18794474802847546075146557 7047928051067829778179959)
              ·
                refine ⟨10571892076601744667269939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7047928051067829778179959 10571892076601744667269939)
                ·
                  refine ⟨15857838114902617000904909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10571892076601744667269939 15857838114902617000904909)
                  ·
                    refine ⟨5946689293088481375339341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15857838114902617000904909 5946689293088481375339341)
                    ·
                      refine ⟨2230008484908180515752253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5946689293088481375339341 2230008484908180515752253)
                      ·
                        rfl

theorem cell23_4342926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 3, 1, 1, 3, 3].length) (baseStart_4342926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4342926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4342926 prefixEnd_4342926 := by exact prefixLift 4342926
  have htrace : WordTrace (prefixWord ++ tailWord_4342926) baseStart_4342926 baseEnd_4342926 := by
    simpa [prefixWord, tailWord_4342926, baseEnd_4342926] using wordTrace_append hprefix tailTrace_4342926
  have hstable : (prefixWord ++ tailWord_4342926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4342926).length < 2 ^ (prefixWord ++ tailWord_4342926).sum := by decide
  have hdescent : baseEnd_4342926 < baseStart_4342926 := by decide
  rcases family_descends (prefixWord ++ tailWord_4342926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4342977 : List Nat := [1, 2, 6, 1, 1, 3, 2, 1, 2, 1, 3]
def baseStart_4342977 : Nat := 118140960795 + 4342977 * 2 ^ 59
def prefixEnd_4342977 : Nat := 4983230072969 + 3 ^ 40 * 4342977 * 2
def baseEnd_4342977 : Nat := 2230034672421559816214519

theorem tailTrace_4342977 : CollatzResearch.WordTrace tailWord_4342977 prefixEnd_4342977 2230034672421559816214519 := by
  unfold tailWord_4342977
  simp only [CollatzResearch.WordTrace]
  refine ⟨158401384387143525265251185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105600922924762350176834123 158401384387143525265251185)
  ·
    refine ⟨118801038290357643948938389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 158401384387143525265251185 118801038290357643948938389)
    ·
      refine ⟨5568798669860514560106487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 118801038290357643948938389 5568798669860514560106487)
      ·
        refine ⟨8353198004790771840159731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5568798669860514560106487 8353198004790771840159731)
        ·
          refine ⟨12529797007186157760239597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8353198004790771840159731 12529797007186157760239597)
          ·
            refine ⟨4698673877694809160089849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12529797007186157760239597 4698673877694809160089849)
            ·
              refine ⟨3524005408271106870067387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4698673877694809160089849 3524005408271106870067387)
              ·
                refine ⟨5286008112406660305101081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3524005408271106870067387 5286008112406660305101081)
                ·
                  refine ⟨3964506084304995228825811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5286008112406660305101081 3964506084304995228825811)
                  ·
                    refine ⟨5946759126457492843238717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3964506084304995228825811 5946759126457492843238717)
                    ·
                      refine ⟨2230034672421559816214519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5946759126457492843238717 2230034672421559816214519)
                      ·
                        rfl

theorem cell23_4342977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 3, 2, 1, 2, 1, 3].length) (baseStart_4342977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4342977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4342977 prefixEnd_4342977 := by exact prefixLift 4342977
  have htrace : WordTrace (prefixWord ++ tailWord_4342977) baseStart_4342977 baseEnd_4342977 := by
    simpa [prefixWord, tailWord_4342977, baseEnd_4342977] using wordTrace_append hprefix tailTrace_4342977
  have hstable : (prefixWord ++ tailWord_4342977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4342977).length < 2 ^ (prefixWord ++ tailWord_4342977).sum := by decide
  have hdescent : baseEnd_4342977 < baseStart_4342977 := by decide
  rcases family_descends (prefixWord ++ tailWord_4342977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4343019 : List Nat := [1, 1, 1, 1, 2, 6, 2, 2, 2, 5]
def baseStart_4343019 : Nat := 118140960795 + 4343019 * 2 ^ 59
def prefixEnd_4343019 : Nat := 4983230072969 + 3 ^ 40 * 4343019 * 2
def baseEnd_4343019 : Nat := 743352079536349550629775

theorem tailTrace_4343019 : CollatzResearch.WordTrace tailWord_4343019 prefixEnd_4343019 743352079536349550629775 := by
  unfold tailWord_4343019
  simp only [CollatzResearch.WordTrace]
  refine ⟨158402916252991366438280111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105601944168660910958853407 158402916252991366438280111)
  ·
    refine ⟨237604374379487049657420167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158402916252991366438280111 237604374379487049657420167)
    ·
      refine ⟨356406561569230574486130251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 237604374379487049657420167 356406561569230574486130251)
      ·
        refine ⟨534609842353845861729195377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 356406561569230574486130251 534609842353845861729195377)
        ·
          refine ⟨400957381765384396296896533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 534609842353845861729195377 400957381765384396296896533)
          ·
            refine ⟨18794877270252393576417025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 400957381765384396296896533 18794877270252393576417025)
            ·
              refine ⟨14096157952689295182312769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18794877270252393576417025 14096157952689295182312769)
              ·
                refine ⟨10572118464516971386734577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14096157952689295182312769 10572118464516971386734577)
                ·
                  refine ⟨7929088848387728540050933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10572118464516971386734577 7929088848387728540050933)
                  ·
                    refine ⟨743352079536349550629775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7929088848387728540050933 743352079536349550629775)
                    ·
                      rfl

theorem cell23_4343019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 2, 2, 2, 5].length) (baseStart_4343019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4343019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4343019 prefixEnd_4343019 := by exact prefixLift 4343019
  have htrace : WordTrace (prefixWord ++ tailWord_4343019) baseStart_4343019 baseEnd_4343019 := by
    simpa [prefixWord, tailWord_4343019, baseEnd_4343019] using wordTrace_append hprefix tailTrace_4343019
  have hstable : (prefixWord ++ tailWord_4343019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4343019).length < 2 ^ (prefixWord ++ tailWord_4343019).sum := by decide
  have hdescent : baseEnd_4343019 < baseStart_4343019 := by decide
  rcases family_descends (prefixWord ++ tailWord_4343019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4343032 : List Nat := [2, 1, 2, 1, 1, 2, 1, 1, 4, 8]
def baseStart_4343032 : Nat := 118140960795 + 4343032 * 2 ^ 59
def prefixEnd_4343032 : Nat := 4983230072969 + 3 ^ 40 * 4343032 * 2
def baseEnd_4343032 : Nat := 743354304619185700342255

theorem tailTrace_4343032 : CollatzResearch.WordTrace tailWord_4343032 prefixEnd_4343032 743354304619185700342255 := by
  unfold tailWord_4343032
  simp only [CollatzResearch.WordTrace]
  refine ⟨79201695200972134829251675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105602260267962846439002233 79201695200972134829251675)
  ·
    refine ⟨118802542801458202243877513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79201695200972134829251675 118802542801458202243877513)
    ·
      refine ⟨89101907101093651682908135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 118802542801458202243877513 89101907101093651682908135)
      ·
        refine ⟨133652860651640477524362203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89101907101093651682908135 133652860651640477524362203)
        ·
          refine ⟨200479290977460716286543305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 133652860651640477524362203 200479290977460716286543305)
          ·
            refine ⟨150359468233095537214907479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 200479290977460716286543305 150359468233095537214907479)
            ·
              refine ⟨225539202349643305822361219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 150359468233095537214907479 225539202349643305822361219)
              ·
                refine ⟨338308803524464958733541829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 225539202349643305822361219 338308803524464958733541829)
                ·
                  refine ⟨63432900660837179762539093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 338308803524464958733541829 63432900660837179762539093)
                  ·
                    refine ⟨743354304619185700342255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 63432900660837179762539093 743354304619185700342255)
                    ·
                      rfl

theorem cell23_4343032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 1, 4, 8].length) (baseStart_4343032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4343032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4343032 prefixEnd_4343032 := by exact prefixLift 4343032
  have htrace : WordTrace (prefixWord ++ tailWord_4343032) baseStart_4343032 baseEnd_4343032 := by
    simpa [prefixWord, tailWord_4343032, baseEnd_4343032] using wordTrace_append hprefix tailTrace_4343032
  have hstable : (prefixWord ++ tailWord_4343032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4343032).length < 2 ^ (prefixWord ++ tailWord_4343032).sum := by decide
  have hdescent : baseEnd_4343032 < baseStart_4343032 := by decide
  rcases family_descends (prefixWord ++ tailWord_4343032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4343076 : List Nat := [2, 3, 1, 3, 1, 1, 2, 1, 4, 2, 3]
def baseStart_4343076 : Nat := 118140960795 + 4343076 * 2 ^ 59
def prefixEnd_4343076 : Nat := 4983230072969 + 3 ^ 40 * 4343076 * 2
def baseEnd_4343076 : Nat := 2230085507006354928876563

theorem tailTrace_4343076 : CollatzResearch.WordTrace tailWord_4343076 prefixEnd_4343076 2230085507006354928876563 := by
  unfold tailWord_4343076
  simp only [CollatzResearch.WordTrace]
  refine ⟨79202497606892432586552541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105603330142523243448736721 79202497606892432586552541)
  ·
    refine ⟨29700936602584662219957203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79202497606892432586552541 29700936602584662219957203)
    ·
      refine ⟨44551404903876993329935805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29700936602584662219957203 44551404903876993329935805)
      ·
        refine ⟨16706776838953872498725927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44551404903876993329935805 16706776838953872498725927)
        ·
          refine ⟨25060165258430808748088891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16706776838953872498725927 25060165258430808748088891)
          ·
            refine ⟨37590247887646213122133337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25060165258430808748088891 37590247887646213122133337)
            ·
              refine ⟨28192685915734659841600003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37590247887646213122133337 28192685915734659841600003)
              ·
                refine ⟨42289028873601989762400005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28192685915734659841600003 42289028873601989762400005)
                ·
                  refine ⟨7929192913800373080450001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 42289028873601989762400005 7929192913800373080450001)
                  ·
                    refine ⟨5946894685350279810337501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7929192913800373080450001 5946894685350279810337501)
                    ·
                      refine ⟨2230085507006354928876563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5946894685350279810337501 2230085507006354928876563)
                      ·
                        rfl

theorem cell23_4343076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 2, 1, 4, 2, 3].length) (baseStart_4343076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4343076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4343076 prefixEnd_4343076 := by exact prefixLift 4343076
  have htrace : WordTrace (prefixWord ++ tailWord_4343076) baseStart_4343076 baseEnd_4343076 := by
    simpa [prefixWord, tailWord_4343076, baseEnd_4343076] using wordTrace_append hprefix tailTrace_4343076
  have hstable : (prefixWord ++ tailWord_4343076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4343076).length < 2 ^ (prefixWord ++ tailWord_4343076).sum := by decide
  have hdescent : baseEnd_4343076 < baseStart_4343076 := by decide
  rcases family_descends (prefixWord ++ tailWord_4343076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4343109 : List Nat := [1, 3, 1, 1, 1, 2, 1, 5, 3, 5]
def baseStart_4343109 : Nat := 118140960795 + 4343109 * 2 ^ 59
def prefixEnd_4343109 : Nat := 4983230072969 + 3 ^ 40 * 4343109 * 2
def baseEnd_4343109 : Nat := 743367483955984433254637

theorem tailTrace_4343109 : CollatzResearch.WordTrace tailWord_4343109 prefixEnd_4343109 743367483955984433254637 := by
  unfold tailWord_4343109
  simp only [CollatzResearch.WordTrace]
  refine ⟨158406198822665311809056381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105604132548443541206037587 158406198822665311809056381)
  ·
    refine ⟨59402324558499491928396143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 158406198822665311809056381 59402324558499491928396143)
    ·
      refine ⟨89103486837749237892594215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59402324558499491928396143 89103486837749237892594215)
      ·
        refine ⟨133655230256623856838891323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89103486837749237892594215 133655230256623856838891323)
        ·
          refine ⟨200482845384935785258336985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 133655230256623856838891323 200482845384935785258336985)
          ·
            refine ⟨150362134038701838943752739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 200482845384935785258336985 150362134038701838943752739)
            ·
              refine ⟨225543201058052758415629109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 150362134038701838943752739 225543201058052758415629109)
              ·
                refine ⟨21144675099192446101465229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 225543201058052758415629109 21144675099192446101465229)
                ·
                  refine ⟨7929253162197167288049461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21144675099192446101465229 7929253162197167288049461)
                  ·
                    refine ⟨743367483955984433254637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7929253162197167288049461 743367483955984433254637)
                    ·
                      rfl

theorem cell23_4343109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 5, 3, 5].length) (baseStart_4343109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4343109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4343109 prefixEnd_4343109 := by exact prefixLift 4343109
  have htrace : WordTrace (prefixWord ++ tailWord_4343109) baseStart_4343109 baseEnd_4343109 := by
    simpa [prefixWord, tailWord_4343109, baseEnd_4343109] using wordTrace_append hprefix tailTrace_4343109
  have hstable : (prefixWord ++ tailWord_4343109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4343109).length < 2 ^ (prefixWord ++ tailWord_4343109).sum := by decide
  have hdescent : baseEnd_4343109 < baseStart_4343109 := by decide
  rcases family_descends (prefixWord ++ tailWord_4343109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4343140 : List Nat := [2, 3, 1, 1, 3, 4, 1, 1, 3, 1, 3]
def baseStart_4343140 : Nat := 118140960795 + 4343140 * 2 ^ 59
def prefixEnd_4343140 : Nat := 4983230072969 + 3 ^ 40 * 4343140 * 2
def baseEnd_4343140 : Nat := 2230118369768242678476269

theorem tailTrace_4343140 : CollatzResearch.WordTrace tailWord_4343140 prefixEnd_4343140 2230118369768242678476269 := by
  unfold tailWord_4343140
  simp only [CollatzResearch.WordTrace]
  refine ⟨79203664742776502051717437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105604886323702002735623249 79203664742776502051717437)
  ·
    refine ⟨29701374278541188269394039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79203664742776502051717437 29701374278541188269394039)
    ·
      refine ⟨44552061417811782404091059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29701374278541188269394039 44552061417811782404091059)
      ·
        refine ⟨66828092126717673606136589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44552061417811782404091059 66828092126717673606136589)
        ·
          refine ⟨25060534547519127602301221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 66828092126717673606136589 25060534547519127602301221)
          ·
            refine ⟨4698850227659836425431479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25060534547519127602301221 4698850227659836425431479)
            ·
              refine ⟨7048275341489754638147219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4698850227659836425431479 7048275341489754638147219)
              ·
                refine ⟨10572413012234631957220829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7048275341489754638147219 10572413012234631957220829)
                ·
                  refine ⟨3964654879587986983957811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10572413012234631957220829 3964654879587986983957811)
                  ·
                    refine ⟨5946982319381980475936717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3964654879587986983957811 5946982319381980475936717)
                    ·
                      refine ⟨2230118369768242678476269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5946982319381980475936717 2230118369768242678476269)
                      ·
                        rfl

theorem cell23_4343140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 4, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 4, 1, 1, 3, 1, 3].length) (baseStart_4343140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4343140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4343140 prefixEnd_4343140 := by exact prefixLift 4343140
  have htrace : WordTrace (prefixWord ++ tailWord_4343140) baseStart_4343140 baseEnd_4343140 := by
    simpa [prefixWord, tailWord_4343140, baseEnd_4343140] using wordTrace_append hprefix tailTrace_4343140
  have hstable : (prefixWord ++ tailWord_4343140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4343140).length < 2 ^ (prefixWord ++ tailWord_4343140).sum := by decide
  have hdescent : baseEnd_4343140 < baseStart_4343140 := by decide
  rcases family_descends (prefixWord ++ tailWord_4343140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4343159 : List Nat := [1, 1, 3, 1, 1, 2, 3, 3, 1, 1, 6]
def baseStart_4343159 : Nat := 118140960795 + 4343159 * 2 ^ 59
def prefixEnd_4343159 : Nat := 4983230072969 + 3 ^ 40 * 4343159 * 2
def baseEnd_4343159 : Nat := 2230128125900678104138681

theorem tailTrace_4343159 : CollatzResearch.WordTrace tailWord_4343159 prefixEnd_4343159 2230128125900678104138681 := by
  unfold tailWord_4343159
  simp only [CollatzResearch.WordTrace]
  refine ⟨158408022472484170348376531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105605348314989446898917687 158408022472484170348376531)
  ·
    refine ⟨237612033708726255522564797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158408022472484170348376531 237612033708726255522564797)
    ·
      refine ⟨89104512640772345820961799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 237612033708726255522564797 89104512640772345820961799)
      ·
        refine ⟨133656768961158518731442699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89104512640772345820961799 133656768961158518731442699)
        ·
          refine ⟨200485153441737778097164049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 133656768961158518731442699 200485153441737778097164049)
          ·
            refine ⟨150363865081303333572873037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 200485153441737778097164049 150363865081303333572873037)
            ·
              refine ⟨56386449405488750089827389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 150363865081303333572873037 56386449405488750089827389)
              ·
                refine ⟨21144918527058281283685271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 56386449405488750089827389 21144918527058281283685271)
                ·
                  refine ⟨31717377790587421925527907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21144918527058281283685271 31717377790587421925527907)
                  ·
                    refine ⟨47576066685881132888291861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 31717377790587421925527907 47576066685881132888291861)
                    ·
                      refine ⟨2230128125900678104138681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 47576066685881132888291861 2230128125900678104138681)
                      ·
                        rfl

theorem cell23_4343159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 3, 1, 1, 6].length) (baseStart_4343159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4343159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4343159 prefixEnd_4343159 := by exact prefixLift 4343159
  have htrace : WordTrace (prefixWord ++ tailWord_4343159) baseStart_4343159 baseEnd_4343159 := by
    simpa [prefixWord, tailWord_4343159, baseEnd_4343159] using wordTrace_append hprefix tailTrace_4343159
  have hstable : (prefixWord ++ tailWord_4343159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4343159).length < 2 ^ (prefixWord ++ tailWord_4343159).sum := by decide
  have hdescent : baseEnd_4343159 < baseStart_4343159 := by decide
  rcases family_descends (prefixWord ++ tailWord_4343159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4343163 : List Nat := [1, 1, 1, 1, 1, 6, 2, 1, 5, 2, 2]
def baseStart_4343163 : Nat := 118140960795 + 4343163 * 2 ^ 59
def prefixEnd_4343163 : Nat := 4983230072969 + 3 ^ 40 * 4343163 * 2
def baseEnd_4343163 : Nat := 2230130179823296088488663

theorem tailTrace_4343163 : CollatzResearch.WordTrace tailWord_4343163 prefixEnd_4343163 2230130179823296088488663 := by
  unfold tailWord_4343163
  simp only [CollatzResearch.WordTrace]
  refine ⟨158408168364469679031522143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105605445576313119354348095 158408168364469679031522143)
  ·
    refine ⟨237612252546704518547283215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158408168364469679031522143 237612252546704518547283215)
    ·
      refine ⟨356418378820056777820924823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 237612252546704518547283215 356418378820056777820924823)
      ·
        refine ⟨534627568230085166731387235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 356418378820056777820924823 534627568230085166731387235)
        ·
          refine ⟨801941352345127750097080853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 534627568230085166731387235 801941352345127750097080853)
          ·
            refine ⟨37591000891177863285800665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 801941352345127750097080853 37591000891177863285800665)
            ·
              refine ⟨28193250668383397464350499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37591000891177863285800665 28193250668383397464350499)
              ·
                refine ⟨42289876002575096196525749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28193250668383397464350499 42289876002575096196525749)
                ·
                  refine ⟨3964675875241415268424289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 42289876002575096196525749 3964675875241415268424289)
                  ·
                    refine ⟨2973506906431061451318217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3964675875241415268424289 2973506906431061451318217)
                    ·
                      refine ⟨2230130179823296088488663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2973506906431061451318217 2230130179823296088488663)
                      ·
                        rfl

theorem cell23_4343163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 2, 1, 5, 2, 2].length) (baseStart_4343163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4343163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4343163 prefixEnd_4343163 := by exact prefixLift 4343163
  have htrace : WordTrace (prefixWord ++ tailWord_4343163) baseStart_4343163 baseEnd_4343163 := by
    simpa [prefixWord, tailWord_4343163, baseEnd_4343163] using wordTrace_append hprefix tailTrace_4343163
  have hstable : (prefixWord ++ tailWord_4343163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4343163).length < 2 ^ (prefixWord ++ tailWord_4343163).sum := by decide
  have hdescent : baseEnd_4343163 < baseStart_4343163 := by decide
  rcases family_descends (prefixWord ++ tailWord_4343163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4343176 : List Nat := [2, 1, 3, 3, 1, 2, 1, 1, 3, 2, 4]
def baseStart_4343176 : Nat := 118140960795 + 4343176 * 2 ^ 59
def prefixEnd_4343176 : Nat := 4983230072969 + 3 ^ 40 * 4343176 * 2
def baseEnd_4343176 : Nat := 2230136855071804537626103

theorem tailTrace_4343176 : CollatzResearch.WordTrace tailWord_4343176 prefixEnd_4343176 2230136855071804537626103 := by
  unfold tailWord_4343176
  simp only [CollatzResearch.WordTrace]
  refine ⟨79204321256711291125872691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105605761675615054834496921 79204321256711291125872691)
  ·
    refine ⟨118806481885066936688809037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79204321256711291125872691 118806481885066936688809037)
    ·
      refine ⟨44552430706900101258303389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 118806481885066936688809037 44552430706900101258303389)
      ·
        refine ⟨16707161515087537971863771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44552430706900101258303389 16707161515087537971863771)
        ·
          refine ⟨25060742272631306957795657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16707161515087537971863771 25060742272631306957795657)
          ·
            refine ⟨18795556704473480218346743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25060742272631306957795657 18795556704473480218346743)
            ·
              refine ⟨28193335056710220327520115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18795556704473480218346743 28193335056710220327520115)
              ·
                refine ⟨42290002585065330491280173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28193335056710220327520115 42290002585065330491280173)
                ·
                  refine ⟨15858750969399498934230065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 42290002585065330491280173 15858750969399498934230065)
                  ·
                    refine ⟨11894063227049624200672549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15858750969399498934230065 11894063227049624200672549)
                    ·
                      refine ⟨2230136855071804537626103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11894063227049624200672549 2230136855071804537626103)
                      ·
                        rfl

theorem cell23_4343176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 1, 1, 3, 2, 4].length) (baseStart_4343176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4343176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4343176 prefixEnd_4343176 := by exact prefixLift 4343176
  have htrace : WordTrace (prefixWord ++ tailWord_4343176) baseStart_4343176 baseEnd_4343176 := by
    simpa [prefixWord, tailWord_4343176, baseEnd_4343176] using wordTrace_append hprefix tailTrace_4343176
  have hstable : (prefixWord ++ tailWord_4343176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4343176).length < 2 ^ (prefixWord ++ tailWord_4343176).sum := by decide
  have hdescent : baseEnd_4343176 < baseStart_4343176 := by decide
  rcases family_descends (prefixWord ++ tailWord_4343176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4343186 : List Nat := [3, 2, 3, 3, 12]
def baseStart_4343186 : Nat := 118140960795 + 4343186 * 2 ^ 59
def prefixEnd_4343186 : Nat := 4983230072969 + 3 ^ 40 * 4343186 * 2
def baseEnd_4343186 : Nat := 3059179684332441013033

theorem tailTrace_4343186 : CollatzResearch.WordTrace tailWord_4343186 prefixEnd_4343186 3059179684332441013033 := by
  unfold tailWord_4343186
  simp only [CollatzResearch.WordTrace]
  refine ⟨39602251810846588489902353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105606004828924235973072941 39602251810846588489902353)
  ·
    refine ⟨29701688858134941367426765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39602251810846588489902353 29701688858134941367426765)
    ·
      refine ⟨11138133321800603012785037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29701688858134941367426765 11138133321800603012785037)
      ·
        refine ⟨4176799995675226129794389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11138133321800603012785037 4176799995675226129794389)
        ·
          refine ⟨3059179684332441013033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 4176799995675226129794389 3059179684332441013033)
          ·
            rfl

theorem cell23_4343186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 12].length) (baseStart_4343186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4343186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4343186 prefixEnd_4343186 := by exact prefixLift 4343186
  have htrace : WordTrace (prefixWord ++ tailWord_4343186) baseStart_4343186 baseEnd_4343186 := by
    simpa [prefixWord, tailWord_4343186, baseEnd_4343186] using wordTrace_append hprefix tailTrace_4343186
  have hstable : (prefixWord ++ tailWord_4343186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4343186).length < 2 ^ (prefixWord ++ tailWord_4343186).sum := by decide
  have hdescent : baseEnd_4343186 < baseStart_4343186 := by decide
  rcases family_descends (prefixWord ++ tailWord_4343186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4343209 : List Nat := [1, 2, 1, 1, 1, 1, 3, 1, 3, 4, 5]
def baseStart_4343209 : Nat := 118140960795 + 4343209 * 2 ^ 59
def prefixEnd_4343209 : Nat := 4983230072969 + 3 ^ 40 * 4343209 * 2
def baseEnd_4343209 : Nat := 2230153799933402908513451

theorem tailTrace_4343209 : CollatzResearch.WordTrace tailWord_4343209 prefixEnd_4343209 2230153799933402908513451 := by
  unfold tailWord_4343209
  simp only [CollatzResearch.WordTrace]
  refine ⟨158409846122303028887696681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105606564081535352591797787 158409846122303028887696681)
  ·
    refine ⟨118807384591727271665772511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 158409846122303028887696681 118807384591727271665772511)
    ·
      refine ⟨178211076887590907498658767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118807384591727271665772511 178211076887590907498658767)
      ·
        refine ⟨267316615331386361247988151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 178211076887590907498658767 267316615331386361247988151)
        ·
          refine ⟨400974922997079541871982227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 267316615331386361247988151 400974922997079541871982227)
          ·
            refine ⟨601462384495619312807973341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 400974922997079541871982227 601462384495619312807973341)
            ·
              refine ⟨225548394185857242302990003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 601462384495619312807973341 225548394185857242302990003)
              ·
                refine ⟨338322591278785863454485005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 225548394185857242302990003 338322591278785863454485005)
                ·
                  refine ⟨126870971729544698795431877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 338322591278785863454485005 126870971729544698795431877)
                  ·
                    refine ⟨23788307199289631024143477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 126870971729544698795431877 23788307199289631024143477)
                    ·
                      refine ⟨2230153799933402908513451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23788307199289631024143477 2230153799933402908513451)
                      ·
                        rfl

theorem cell23_4343209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 1, 3, 4, 5].length) (baseStart_4343209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4343209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4343209 prefixEnd_4343209 := by exact prefixLift 4343209
  have htrace : WordTrace (prefixWord ++ tailWord_4343209) baseStart_4343209 baseEnd_4343209 := by
    simpa [prefixWord, tailWord_4343209, baseEnd_4343209] using wordTrace_append hprefix tailTrace_4343209
  have hstable : (prefixWord ++ tailWord_4343209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4343209).length < 2 ^ (prefixWord ++ tailWord_4343209).sum := by decide
  have hdescent : baseEnd_4343209 < baseStart_4343209 := by decide
  rcases family_descends (prefixWord ++ tailWord_4343209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4343223 : List Nat := [1, 1, 3, 1, 3, 2, 1, 3, 3, 3, 2]
def baseStart_4343223 : Nat := 118140960795 + 4343223 * 2 ^ 59
def prefixEnd_4343223 : Nat := 4983230072969 + 3 ^ 40 * 4343223 * 2
def baseEnd_4343223 : Nat := 2230160988662565853738387

theorem tailTrace_4343223 : CollatzResearch.WordTrace tailWord_4343223 prefixEnd_4343223 2230160988662565853738387 := by
  unfold tailWord_4343223
  simp only [CollatzResearch.WordTrace]
  refine ⟨158410356744252309278706323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105606904496168206185804215 158410356744252309278706323)
  ·
    refine ⟨237615535116378463918059485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158410356744252309278706323 237615535116378463918059485)
    ·
      refine ⟨89105825668641923969272307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 237615535116378463918059485 89105825668641923969272307)
      ·
        refine ⟨133658738502962885953908461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89105825668641923969272307 133658738502962885953908461)
        ·
          refine ⟨50122026938611082232715673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 133658738502962885953908461 50122026938611082232715673)
          ·
            refine ⟨37591520203958311674536755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50122026938611082232715673 37591520203958311674536755)
            ·
              refine ⟨56387280305937467511805133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37591520203958311674536755 56387280305937467511805133)
              ·
                refine ⟨21145230114726550316926925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 56387280305937467511805133 21145230114726550316926925)
                ·
                  refine ⟨7929461293022456368847597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21145230114726550316926925 7929461293022456368847597)
                  ·
                    refine ⟨2973547984883421138317849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7929461293022456368847597 2973547984883421138317849)
                    ·
                      refine ⟨2230160988662565853738387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2973547984883421138317849 2230160988662565853738387)
                      ·
                        rfl

theorem cell23_4343223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 3, 3, 3, 2].length) (baseStart_4343223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4343223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4343223 prefixEnd_4343223 := by exact prefixLift 4343223
  have htrace : WordTrace (prefixWord ++ tailWord_4343223) baseStart_4343223 baseEnd_4343223 := by
    simpa [prefixWord, tailWord_4343223, baseEnd_4343223] using wordTrace_append hprefix tailTrace_4343223
  have hstable : (prefixWord ++ tailWord_4343223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4343223).length < 2 ^ (prefixWord ++ tailWord_4343223).sum := by decide
  have hdescent : baseEnd_4343223 < baseStart_4343223 := by decide
  rcases family_descends (prefixWord ++ tailWord_4343223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4343240 : List Nat := [2, 1, 3, 1, 3, 1, 3, 3, 1, 3, 2]
def baseStart_4343240 : Nat := 118140960795 + 4343240 * 2 ^ 59
def prefixEnd_4343240 : Nat := 4983230072969 + 3 ^ 40 * 4343240 * 2
def baseEnd_4343240 : Nat := 2230169717833692287225809

theorem tailTrace_4343240 : CollatzResearch.WordTrace tailWord_4343240 prefixEnd_4343240 2230169717833692287225809 := by
  unfold tailWord_4343240
  simp only [CollatzResearch.WordTrace]
  refine ⟨79205488392595360591037587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105607317856793814121383449 79205488392595360591037587)
  ·
    refine ⟨118808232588893040886556381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79205488392595360591037587 118808232588893040886556381)
    ·
      refine ⟨44553087220834890332458643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 118808232588893040886556381 44553087220834890332458643)
      ·
        refine ⟨66829630831252335498687965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44553087220834890332458643 66829630831252335498687965)
        ·
          refine ⟨25061111561719625812007987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 66829630831252335498687965 25061111561719625812007987)
          ·
            refine ⟨37591667342579438718011981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25061111561719625812007987 37591667342579438718011981)
            ·
              refine ⟨14096875253467289519254493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37591667342579438718011981 14096875253467289519254493)
              ·
                refine ⟨5286328220050233569720435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14096875253467289519254493 5286328220050233569720435)
                ·
                  refine ⟨7929492330075350354580653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5286328220050233569720435 7929492330075350354580653)
                  ·
                    refine ⟨2973559623778256382967745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7929492330075350354580653 2973559623778256382967745)
                    ·
                      refine ⟨2230169717833692287225809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2973559623778256382967745 2230169717833692287225809)
                      ·
                        rfl

theorem cell23_4343240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 3, 3, 1, 3, 2].length) (baseStart_4343240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4343240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4343240 prefixEnd_4343240 := by exact prefixLift 4343240
  have htrace : WordTrace (prefixWord ++ tailWord_4343240) baseStart_4343240 baseEnd_4343240 := by
    simpa [prefixWord, tailWord_4343240, baseEnd_4343240] using wordTrace_append hprefix tailTrace_4343240
  have hstable : (prefixWord ++ tailWord_4343240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4343240).length < 2 ^ (prefixWord ++ tailWord_4343240).sum := by decide
  have hdescent : baseEnd_4343240 < baseStart_4343240 := by decide
  rcases family_descends (prefixWord ++ tailWord_4343240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4343246 : List Nat := [4, 1, 1, 1, 2, 1, 3, 2, 2, 6]
def baseStart_4343246 : Nat := 118140960795 + 4343246 * 2 ^ 59
def prefixEnd_4343246 : Nat := 4983230072969 + 3 ^ 40 * 4343246 * 2
def baseEnd_4343246 : Nat := 743390932905873087916927

theorem tailTrace_4343246 : CollatzResearch.WordTrace tailWord_4343246 prefixEnd_4343246 743390932905873087916927 := by
  unfold tailWord_4343246
  simp only [CollatzResearch.WordTrace]
  refine ⟨19801399452896123025849199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 105607463748779322804529061 19801399452896123025849199)
  ·
    refine ⟨29702099179344184538773799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19801399452896123025849199 29702099179344184538773799)
    ·
      refine ⟨44553148769016276808160699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29702099179344184538773799 44553148769016276808160699)
      ·
        refine ⟨66829723153524415212241049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44553148769016276808160699 66829723153524415212241049)
        ·
          refine ⟨50122292365143311409180787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66829723153524415212241049 50122292365143311409180787)
          ·
            refine ⟨75183438547714967113771181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50122292365143311409180787 75183438547714967113771181)
            ·
              refine ⟨28193789455393112667664193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 75183438547714967113771181 28193789455393112667664193)
              ·
                refine ⟨21145342091544834500748145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28193789455393112667664193 21145342091544834500748145)
                ·
                  refine ⟨15859006568658625875561109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21145342091544834500748145 15859006568658625875561109)
                  ·
                    refine ⟨743390932905873087916927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15859006568658625875561109 743390932905873087916927)
                    ·
                      rfl

theorem cell23_4343246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 3, 2, 2, 6].length) (baseStart_4343246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4343246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4343246 prefixEnd_4343246 := by exact prefixLift 4343246
  have htrace : WordTrace (prefixWord ++ tailWord_4343246) baseStart_4343246 baseEnd_4343246 := by
    simpa [prefixWord, tailWord_4343246, baseEnd_4343246] using wordTrace_append hprefix tailTrace_4343246
  have hstable : (prefixWord ++ tailWord_4343246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4343246).length < 2 ^ (prefixWord ++ tailWord_4343246).sum := by decide
  have hdescent : baseEnd_4343246 < baseStart_4343246 := by decide
  rcases family_descends (prefixWord ++ tailWord_4343246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4343256 : List Nat := [2, 1, 2, 2, 2, 1, 2, 1, 1, 6, 3]
def baseStart_4343256 : Nat := 118140960795 + 4343256 * 2 ^ 59
def prefixEnd_4343256 : Nat := 4983230072969 + 3 ^ 40 * 4343256 * 2
def baseEnd_4343256 : Nat := 2230177933524164224625735

theorem tailTrace_4343256 : CollatzResearch.WordTrace tailWord_4343256 prefixEnd_4343256 2230177933524164224625735 := by
  unfold tailWord_4343256
  simp only [CollatzResearch.WordTrace]
  refine ⟨79205780176566377957328811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105607706902088503943105081 79205780176566377957328811)
  ·
    refine ⟨118808670264849566935993217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79205780176566377957328811 118808670264849566935993217)
    ·
      refine ⟨89106502698637175201994913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 118808670264849566935993217 89106502698637175201994913)
      ·
        refine ⟨66829877023977881401496185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89106502698637175201994913 66829877023977881401496185)
        ·
          refine ⟨50122407767983411051122139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66829877023977881401496185 50122407767983411051122139)
          ·
            refine ⟨75183611651975116576683209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50122407767983411051122139 75183611651975116576683209)
            ·
              refine ⟨56387708738981337432512407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 75183611651975116576683209 56387708738981337432512407)
              ·
                refine ⟨84581563108472006148768611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56387708738981337432512407 84581563108472006148768611)
                ·
                  refine ⟨126872344662708009223152917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 84581563108472006148768611 126872344662708009223152917)
                  ·
                    refine ⟨5947141156064437932335293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 126872344662708009223152917 5947141156064437932335293)
                    ·
                      refine ⟨2230177933524164224625735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5947141156064437932335293 2230177933524164224625735)
                      ·
                        rfl

theorem cell23_4343256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 1, 1, 6, 3].length) (baseStart_4343256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4343256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4343256 prefixEnd_4343256 := by exact prefixLift 4343256
  have htrace : WordTrace (prefixWord ++ tailWord_4343256) baseStart_4343256 baseEnd_4343256 := by
    simpa [prefixWord, tailWord_4343256, baseEnd_4343256] using wordTrace_append hprefix tailTrace_4343256
  have hstable : (prefixWord ++ tailWord_4343256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4343256).length < 2 ^ (prefixWord ++ tailWord_4343256).sum := by decide
  have hdescent : baseEnd_4343256 < baseStart_4343256 := by decide
  rcases family_descends (prefixWord ++ tailWord_4343256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4343310 : List Nat := [4, 1, 1, 2, 4, 2, 1, 1, 7]
def baseStart_4343310 : Nat := 118140960795 + 4343310 * 2 ^ 59
def prefixEnd_4343310 : Nat := 4983230072969 + 3 ^ 40 * 4343310 * 2
def baseEnd_4343310 : Nat := 247800629053278557038943

theorem tailTrace_4343310 : CollatzResearch.WordTrace tailWord_4343310 prefixEnd_4343310 247800629053278557038943 := by
  unfold tailWord_4343310
  simp only [CollatzResearch.WordTrace]
  refine ⟨19801691236867140392140423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 105609019929958082091415589 19801691236867140392140423)
  ·
    refine ⟨29702536855300710588210635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19801691236867140392140423 29702536855300710588210635)
    ·
      refine ⟨44553805282951065882315953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29702536855300710588210635 44553805282951065882315953)
      ·
        refine ⟨33415353962213299411736965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44553805282951065882315953 33415353962213299411736965)
        ·
          refine ⟨6265378867914993639700681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 33415353962213299411736965 6265378867914993639700681)
          ·
            refine ⟨4699034150936245229775511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6265378867914993639700681 4699034150936245229775511)
            ·
              refine ⟨7048551226404367844663267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4699034150936245229775511 7048551226404367844663267)
              ·
                refine ⟨10572826839606551766994901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7048551226404367844663267 10572826839606551766994901)
                ·
                  refine ⟨247800629053278557038943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10572826839606551766994901 247800629053278557038943)
                  ·
                    rfl

theorem cell23_4343310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 2, 1, 1, 7].length) (baseStart_4343310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4343310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4343310 prefixEnd_4343310 := by exact prefixLift 4343310
  have htrace : WordTrace (prefixWord ++ tailWord_4343310) baseStart_4343310 baseEnd_4343310 := by
    simpa [prefixWord, tailWord_4343310, baseEnd_4343310] using wordTrace_append hprefix tailTrace_4343310
  have hstable : (prefixWord ++ tailWord_4343310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4343310).length < 2 ^ (prefixWord ++ tailWord_4343310).sum := by decide
  have hdescent : baseEnd_4343310 < baseStart_4343310 := by decide
  rcases family_descends (prefixWord ++ tailWord_4343310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4343313 : List Nat := [1, 2, 2, 1, 1, 2, 4, 1, 2, 5, 2]
def baseStart_4343313 : Nat := 118140960795 + 4343313 * 2 ^ 59
def prefixEnd_4343313 : Nat := 4983230072969 + 3 ^ 40 * 4343313 * 2
def baseEnd_4343313 : Nat := 2230207201921470501612973

theorem tailTrace_4343313 : CollatzResearch.WordTrace tailWord_4343313 prefixEnd_4343313 2230207201921470501612973 := by
  unfold tailWord_4343313
  simp only [CollatzResearch.WordTrace]
  refine ⟨158413639313926254649482593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105609092875950836432988395 158413639313926254649482593)
  ·
    refine ⟨118810229485444690987111945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 158413639313926254649482593 118810229485444690987111945)
    ·
      refine ⟨89107672114083518240333959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 118810229485444690987111945 89107672114083518240333959)
      ·
        refine ⟨133661508171125277360500939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89107672114083518240333959 133661508171125277360500939)
        ·
          refine ⟨200492262256687916040751409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 133661508171125277360500939 200492262256687916040751409)
          ·
            refine ⟨150369196692515937030563557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 200492262256687916040751409 150369196692515937030563557)
            ·
              refine ⟨28194224379846738193230667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 150369196692515937030563557 28194224379846738193230667)
              ·
                refine ⟨42291336569770107289846001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28194224379846738193230667 42291336569770107289846001)
                ·
                  refine ⟨31718502427327580467384501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 42291336569770107289846001 31718502427327580467384501)
                  ·
                    refine ⟨2973609602561960668817297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 31718502427327580467384501 2973609602561960668817297)
                    ·
                      refine ⟨2230207201921470501612973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2973609602561960668817297 2230207201921470501612973)
                      ·
                        rfl

theorem cell23_4343313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 5, 2].length) (baseStart_4343313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4343313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4343313 prefixEnd_4343313 := by exact prefixLift 4343313
  have htrace : WordTrace (prefixWord ++ tailWord_4343313) baseStart_4343313 baseEnd_4343313 := by
    simpa [prefixWord, tailWord_4343313, baseEnd_4343313] using wordTrace_append hprefix tailTrace_4343313
  have hstable : (prefixWord ++ tailWord_4343313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4343313).length < 2 ^ (prefixWord ++ tailWord_4343313).sum := by decide
  have hdescent : baseEnd_4343313 < baseStart_4343313 := by decide
  rcases family_descends (prefixWord ++ tailWord_4343313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4343383 : List Nat := [1, 1, 3, 2, 2, 3, 2, 3, 6]
def baseStart_4343383 : Nat := 118140960795 + 4343383 * 2 ^ 59
def prefixEnd_4343383 : Nat := 4983230072969 + 3 ^ 40 * 4343383 * 2
def baseEnd_4343383 : Nat := 247804793951920580859739

theorem tailTrace_4343383 : CollatzResearch.WordTrace tailWord_4343383 prefixEnd_4343383 247804793951920580859739 := by
  unfold tailWord_4343383
  simp only [CollatzResearch.WordTrace]
  refine ⟨158416192423672656604530803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105610794949115104403020535 158416192423672656604530803)
  ·
    refine ⟨237624288635508984906796205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158416192423672656604530803 237624288635508984906796205)
    ·
      refine ⟨89109108238315869340048577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 237624288635508984906796205 89109108238315869340048577)
      ·
        refine ⟨66831831178736902005036433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89109108238315869340048577 66831831178736902005036433)
        ·
          refine ⟨50123873384052676503777325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66831831178736902005036433 50123873384052676503777325)
          ·
            refine ⟨18796452519019753688916497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50123873384052676503777325 18796452519019753688916497)
            ·
              refine ⟨14097339389264815266687373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18796452519019753688916497 14097339389264815266687373)
              ·
                refine ⟨5286502270974305725007765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14097339389264815266687373 5286502270974305725007765)
                ·
                  refine ⟨247804793951920580859739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5286502270974305725007765 247804793951920580859739)
                  ·
                    rfl

theorem cell23_4343383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 2, 3, 6].length) (baseStart_4343383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4343383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4343383 prefixEnd_4343383 := by exact prefixLift 4343383
  have htrace : WordTrace (prefixWord ++ tailWord_4343383) baseStart_4343383 baseEnd_4343383 := by
    simpa [prefixWord, tailWord_4343383, baseEnd_4343383] using wordTrace_append hprefix tailTrace_4343383
  have hstable : (prefixWord ++ tailWord_4343383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4343383).length < 2 ^ (prefixWord ++ tailWord_4343383).sum := by decide
  have hdescent : baseEnd_4343383 < baseStart_4343383 := by decide
  rcases family_descends (prefixWord ++ tailWord_4343383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4343397 : List Nat := [1, 3, 1, 3, 3, 3, 1, 1, 2, 2, 3]
def baseStart_4343397 : Nat := 118140960795 + 4343397 * 2 ^ 59
def prefixEnd_4343397 : Nat := 4983230072969 + 3 ^ 40 * 4343397 * 2
def baseEnd_4343397 : Nat := 2230250334296448172962587

theorem tailTrace_4343397 : CollatzResearch.WordTrace tailWord_4343397 prefixEnd_4343397 2230250334296448172962587 := by
  unfold tailWord_4343397
  simp only [CollatzResearch.WordTrace]
  refine ⟨158416703045621936995540445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105611135363747957997026963 158416703045621936995540445)
  ·
    refine ⟨59406263642108226373327667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 158416703045621936995540445 59406263642108226373327667)
    ·
      refine ⟨89109395463162339559991501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59406263642108226373327667 89109395463162339559991501)
      ·
        refine ⟨33416023298685877334996813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 89109395463162339559991501 33416023298685877334996813)
        ·
          refine ⟨12531008737007204000623805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33416023298685877334996813 12531008737007204000623805)
          ·
            refine ⟨4699128276377701500233927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12531008737007204000623805 4699128276377701500233927)
            ·
              refine ⟨7048692414566552250350891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4699128276377701500233927 7048692414566552250350891)
              ·
                refine ⟨10573038621849828375526337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7048692414566552250350891 10573038621849828375526337)
                ·
                  refine ⟨7929778966387371281644753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10573038621849828375526337 7929778966387371281644753)
                  ·
                    refine ⟨5947334224790528461233565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7929778966387371281644753 5947334224790528461233565)
                    ·
                      refine ⟨2230250334296448172962587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5947334224790528461233565 2230250334296448172962587)
                      ·
                        rfl

theorem cell23_4343397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 3, 1, 1, 2, 2, 3].length) (baseStart_4343397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4343397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4343397 prefixEnd_4343397 := by exact prefixLift 4343397
  have htrace : WordTrace (prefixWord ++ tailWord_4343397) baseStart_4343397 baseEnd_4343397 := by
    simpa [prefixWord, tailWord_4343397, baseEnd_4343397] using wordTrace_append hprefix tailTrace_4343397
  have hstable : (prefixWord ++ tailWord_4343397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4343397).length < 2 ^ (prefixWord ++ tailWord_4343397).sum := by decide
  have hdescent : baseEnd_4343397 < baseStart_4343397 := by decide
  rcases family_descends (prefixWord ++ tailWord_4343397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4343420 : List Nat := [2, 2, 2, 1, 1, 2, 1, 3, 4, 3, 2]
def baseStart_4343420 : Nat := 118140960795 + 4343420 * 2 ^ 59
def prefixEnd_4343420 : Nat := 4983230072969 + 3 ^ 40 * 4343420 * 2
def baseEnd_4343420 : Nat := 2230262144351501582974981

theorem tailTrace_4343420 : CollatzResearch.WordTrace tailWord_4343420 prefixEnd_4343420 2230262144351501582974981 := by
  unfold tailWord_4343420
  simp only [CollatzResearch.WordTrace]
  refine ⟨79208770962269305961813857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105611694616359074615751809 79208770962269305961813857)
  ·
    refine ⟨59406578221701979471360393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79208770962269305961813857 59406578221701979471360393)
    ·
      refine ⟨44554933666276484603520295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59406578221701979471360393 44554933666276484603520295)
      ·
        refine ⟨66832400499414726905280443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44554933666276484603520295 66832400499414726905280443)
        ·
          refine ⟨100248600749122090357920665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66832400499414726905280443 100248600749122090357920665)
          ·
            refine ⟨75186450561841567768440499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 100248600749122090357920665 75186450561841567768440499)
            ·
              refine ⟨112779675842762351652660749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75186450561841567768440499 112779675842762351652660749)
              ·
                refine ⟨42292378441035881869747781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 112779675842762351652660749 42292378441035881869747781)
                ·
                  refine ⟨7929820957694227850577709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 42292378441035881869747781 7929820957694227850577709)
                  ·
                    refine ⟨2973682859135335443966641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7929820957694227850577709 2973682859135335443966641)
                    ·
                      refine ⟨2230262144351501582974981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2973682859135335443966641 2230262144351501582974981)
                      ·
                        rfl

theorem cell23_4343420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 3, 4, 3, 2].length) (baseStart_4343420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4343420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4343420 prefixEnd_4343420 := by exact prefixLift 4343420
  have htrace : WordTrace (prefixWord ++ tailWord_4343420) baseStart_4343420 baseEnd_4343420 := by
    simpa [prefixWord, tailWord_4343420, baseEnd_4343420] using wordTrace_append hprefix tailTrace_4343420
  have hstable : (prefixWord ++ tailWord_4343420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4343420).length < 2 ^ (prefixWord ++ tailWord_4343420).sum := by decide
  have hdescent : baseEnd_4343420 < baseStart_4343420 := by decide
  rcases family_descends (prefixWord ++ tailWord_4343420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4343433 : List Nat := [1, 2, 1, 1, 4, 1, 2, 1, 5, 1, 4]
def baseStart_4343433 : Nat := 118140960795 + 4343433 * 2 ^ 59
def prefixEnd_4343433 : Nat := 4983230072969 + 3 ^ 40 * 4343433 * 2
def baseEnd_4343433 : Nat := 2230268819600010032112421

theorem tailTrace_4343433 : CollatzResearch.WordTrace tailWord_4343433 prefixEnd_4343433 2230268819600010032112421 := by
  unfold tailWord_4343433
  simp only [CollatzResearch.WordTrace]
  refine ⟨158418016073491515143850953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105612010715661010095900635 158418016073491515143850953)
  ·
    refine ⟨118813512055118636357888215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 158418016073491515143850953 118813512055118636357888215)
    ·
      refine ⟨178220268082677954536832323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118813512055118636357888215 178220268082677954536832323)
      ·
        refine ⟨267330402124016931805248485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 178220268082677954536832323 267330402124016931805248485)
        ·
          refine ⟨50124450398253174713484091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 267330402124016931805248485 50124450398253174713484091)
          ·
            refine ⟨75186675597379762070226137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50124450398253174713484091 75186675597379762070226137)
            ·
              refine ⟨56390006698034821552669603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 75186675597379762070226137 56390006698034821552669603)
              ·
                refine ⟨84585010047052232329004405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56390006698034821552669603 84585010047052232329004405)
                ·
                  refine ⟨7929844691911146780844163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 84585010047052232329004405 7929844691911146780844163)
                  ·
                    refine ⟨11894767037866720171266245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7929844691911146780844163 11894767037866720171266245)
                    ·
                      refine ⟨2230268819600010032112421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11894767037866720171266245 2230268819600010032112421)
                      ·
                        rfl

theorem cell23_4343433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 1, 5, 1, 4].length) (baseStart_4343433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4343433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4343433 prefixEnd_4343433 := by exact prefixLift 4343433
  have htrace : WordTrace (prefixWord ++ tailWord_4343433) baseStart_4343433 baseEnd_4343433 := by
    simpa [prefixWord, tailWord_4343433, baseEnd_4343433] using wordTrace_append hprefix tailTrace_4343433
  have hstable : (prefixWord ++ tailWord_4343433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4343433).length < 2 ^ (prefixWord ++ tailWord_4343433).sum := by decide
  have hdescent : baseEnd_4343433 < baseStart_4343433 := by decide
  rcases family_descends (prefixWord ++ tailWord_4343433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4343443 : List Nat := [1, 1, 1, 2, 1, 2, 2, 1, 8, 4]
def baseStart_4343443 : Nat := 118140960795 + 4343443 * 2 ^ 59
def prefixEnd_4343443 : Nat := 4983230072969 + 3 ^ 40 * 4343443 * 2
def baseEnd_4343443 : Nat := 743424651468851664329125

theorem tailTrace_4343443 : CollatzResearch.WordTrace tailWord_4343443 prefixEnd_4343443 743424651468851664329125 := by
  unfold tailWord_4343443
  simp only [CollatzResearch.WordTrace]
  refine ⟨158418380803455286851714983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105612253868970191234476655 158418380803455286851714983)
  ·
    refine ⟨237627571205182930277572475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158418380803455286851714983 237627571205182930277572475)
    ·
      refine ⟨356441356807774395416358713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 237627571205182930277572475 356441356807774395416358713)
      ·
        refine ⟨267331017605830796562269035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 356441356807774395416358713 267331017605830796562269035)
        ·
          refine ⟨400996526408746194843403553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 267331017605830796562269035 400996526408746194843403553)
          ·
            refine ⟨300747394806559646132552665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 400996526408746194843403553 300747394806559646132552665)
            ·
              refine ⟨225560546104919734599414499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 300747394806559646132552665 225560546104919734599414499)
              ·
                refine ⟨338340819157379601899121749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 225560546104919734599414499 338340819157379601899121749)
                ·
                  refine ⟨3964931474500542209755333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 338340819157379601899121749 3964931474500542209755333)
                  ·
                    refine ⟨743424651468851664329125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3964931474500542209755333 743424651468851664329125)
                    ·
                      rfl

theorem cell23_4343443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 1, 8, 4].length) (baseStart_4343443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4343443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4343443 prefixEnd_4343443 := by exact prefixLift 4343443
  have htrace : WordTrace (prefixWord ++ tailWord_4343443) baseStart_4343443 baseEnd_4343443 := by
    simpa [prefixWord, tailWord_4343443, baseEnd_4343443] using wordTrace_append hprefix tailTrace_4343443
  have hstable : (prefixWord ++ tailWord_4343443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4343443).length < 2 ^ (prefixWord ++ tailWord_4343443).sum := by decide
  have hdescent : baseEnd_4343443 < baseStart_4343443 := by decide
  rcases family_descends (prefixWord ++ tailWord_4343443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4343453 : List Nat := [1, 4, 2, 1, 1, 1, 1, 1, 5, 1, 5]
def baseStart_4343453 : Nat := 118140960795 + 4343453 * 2 ^ 59
def prefixEnd_4343453 : Nat := 4983230072969 + 3 ^ 40 * 4343453 * 2
def baseEnd_4343453 : Nat := 2230279089213099953862329

theorem tailTrace_4343453 : CollatzResearch.WordTrace tailWord_4343453 prefixEnd_4343453 2230279089213099953862329 := by
  unfold tailWord_4343453
  simp only [CollatzResearch.WordTrace]
  refine ⟨158418745533419058559579013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105612497022279372373052675 158418745533419058559579013)
  ·
    refine ⟨29703514787516073479921065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 158418745533419058559579013 29703514787516073479921065)
    ·
      refine ⟨22277636090637055109940799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29703514787516073479921065 22277636090637055109940799)
      ·
        refine ⟨33416454135955582664911199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22277636090637055109940799 33416454135955582664911199)
        ·
          refine ⟨50124681203933373997366799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33416454135955582664911199 50124681203933373997366799)
          ·
            refine ⟨75187021805900060996050199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50124681203933373997366799 75187021805900060996050199)
            ·
              refine ⟨112780532708850091494075299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75187021805900060996050199 112780532708850091494075299)
              ·
                refine ⟨169170799063275137241112949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 112780532708850091494075299 169170799063275137241112949)
                ·
                  refine ⟨15859762412182044116354339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 169170799063275137241112949 15859762412182044116354339)
                  ·
                    refine ⟨23789643618273066174531509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15859762412182044116354339 23789643618273066174531509)
                    ·
                      refine ⟨2230279089213099953862329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23789643618273066174531509 2230279089213099953862329)
                      ·
                        rfl

theorem cell23_4343453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 1, 5, 1, 5].length) (baseStart_4343453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4343453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4343453 prefixEnd_4343453 := by exact prefixLift 4343453
  have htrace : WordTrace (prefixWord ++ tailWord_4343453) baseStart_4343453 baseEnd_4343453 := by
    simpa [prefixWord, tailWord_4343453, baseEnd_4343453] using wordTrace_append hprefix tailTrace_4343453
  have hstable : (prefixWord ++ tailWord_4343453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4343453).length < 2 ^ (prefixWord ++ tailWord_4343453).sum := by decide
  have hdescent : baseEnd_4343453 < baseStart_4343453 := by decide
  rcases family_descends (prefixWord ++ tailWord_4343453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4343460 : List Nat := [2, 3, 1, 2, 2, 2, 1, 2, 4, 4]
def baseStart_4343460 : Nat := 118140960795 + 4343460 * 2 ^ 59
def prefixEnd_4343460 : Nat := 4983230072969 + 3 ^ 40 * 4343460 * 2
def baseEnd_4343460 : Nat := 743427561192560475491599

theorem tailTrace_4343460 : CollatzResearch.WordTrace tailWord_4343460 prefixEnd_4343460 743427561192560475491599 := by
  unfold tailWord_4343460
  simp only [CollatzResearch.WordTrace]
  refine ⟨79209500422196849377541917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105612667229595799170055889 79209500422196849377541917)
  ·
    refine ⟨29703562658323818516578219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79209500422196849377541917 29703562658323818516578219)
    ·
      refine ⟨44555343987485727774867329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29703562658323818516578219 44555343987485727774867329)
      ·
        refine ⟨33416507990614295831150497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44555343987485727774867329 33416507990614295831150497)
        ·
          refine ⟨25062380992960721873362873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33416507990614295831150497 25062380992960721873362873)
          ·
            refine ⟨18796785744720541405022155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25062380992960721873362873 18796785744720541405022155)
            ·
              refine ⟨28195178617080812107533233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18796785744720541405022155 28195178617080812107533233)
              ·
                refine ⟨21146383962810609080649925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28195178617080812107533233 21146383962810609080649925)
                ·
                  refine ⟨3964946993026989202621861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21146383962810609080649925 3964946993026989202621861)
                  ·
                    refine ⟨743427561192560475491599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3964946993026989202621861 743427561192560475491599)
                    ·
                      rfl

theorem cell23_4343460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 1, 2, 4, 4].length) (baseStart_4343460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4343460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4343460 prefixEnd_4343460 := by exact prefixLift 4343460
  have htrace : WordTrace (prefixWord ++ tailWord_4343460) baseStart_4343460 baseEnd_4343460 := by
    simpa [prefixWord, tailWord_4343460, baseEnd_4343460] using wordTrace_append hprefix tailTrace_4343460
  have hstable : (prefixWord ++ tailWord_4343460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4343460).length < 2 ^ (prefixWord ++ tailWord_4343460).sum := by decide
  have hdescent : baseEnd_4343460 < baseStart_4343460 := by decide
  rcases family_descends (prefixWord ++ tailWord_4343460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4343484 : List Nat := [2, 2, 2, 3, 1, 2, 3, 1, 3, 2, 2]
def baseStart_4343484 : Nat := 118140960795 + 4343484 * 2 ^ 59
def prefixEnd_4343484 : Nat := 4983230072969 + 3 ^ 40 * 4343484 * 2
def baseEnd_4343484 : Nat := 2230295007113389332574687

theorem tailTrace_4343484 : CollatzResearch.WordTrace tailWord_4343484 prefixEnd_4343484 2230295007113389332574687 := by
  unfold tailWord_4343484
  simp only [CollatzResearch.WordTrace]
  refine ⟨79209938098153375426978753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105613250797537833902638337 79209938098153375426978753)
  ·
    refine ⟨59407453573615031570234065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79209938098153375426978753 59407453573615031570234065)
    ·
      refine ⟨44555590180211273677675549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59407453573615031570234065 44555590180211273677675549)
      ·
        refine ⟨16708346317579227629128331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44555590180211273677675549 16708346317579227629128331)
        ·
          refine ⟨25062519476368841443692497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16708346317579227629128331 25062519476368841443692497)
          ·
            refine ⟨18796889607276631082769373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25062519476368841443692497 18796889607276631082769373)
            ·
              refine ⟨7048833602728736656038515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18796889607276631082769373 7048833602728736656038515)
              ·
                refine ⟨10573250404093104984057773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7048833602728736656038515 10573250404093104984057773)
                ·
                  refine ⟨3964968901534914369021665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10573250404093104984057773 3964968901534914369021665)
                  ·
                    refine ⟨2973726676151185776766249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3964968901534914369021665 2973726676151185776766249)
                    ·
                      refine ⟨2230295007113389332574687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2973726676151185776766249 2230295007113389332574687)
                      ·
                        rfl

theorem cell23_4343484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 3, 1, 3, 2, 2].length) (baseStart_4343484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4343484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4343484 prefixEnd_4343484 := by exact prefixLift 4343484
  have htrace : WordTrace (prefixWord ++ tailWord_4343484) baseStart_4343484 baseEnd_4343484 := by
    simpa [prefixWord, tailWord_4343484, baseEnd_4343484] using wordTrace_append hprefix tailTrace_4343484
  have hstable : (prefixWord ++ tailWord_4343484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4343484).length < 2 ^ (prefixWord ++ tailWord_4343484).sum := by decide
  have hdescent : baseEnd_4343484 < baseStart_4343484 := by decide
  rcases family_descends (prefixWord ++ tailWord_4343484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4343501 : List Nat := [1, 6, 2, 1, 1, 3, 1, 2, 1, 1, 4]
def baseStart_4343501 : Nat := 118140960795 + 4343501 * 2 ^ 59
def prefixEnd_4343501 : Nat := 4983230072969 + 3 ^ 40 * 4343501 * 2
def baseEnd_4343501 : Nat := 2230303736284515766062109

theorem tailTrace_4343501 : CollatzResearch.WordTrace tailWord_4343501 prefixEnd_4343501 2230303736284515766062109 := by
  unfold tailWord_4343501
  simp only [CollatzResearch.WordTrace]
  refine ⟨158420496237245162757326357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105613664158163441838217571 158420496237245162757326357)
  ·
    refine ⟨7425960761120867004249673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 158420496237245162757326357 7425960761120867004249673)
    ·
      refine ⟨5569470570840650253187255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7425960761120867004249673 5569470570840650253187255)
      ·
        refine ⟨8354205856260975379780883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5569470570840650253187255 8354205856260975379780883)
        ·
          refine ⟨12531308784391463069671325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8354205856260975379780883 12531308784391463069671325)
          ·
            refine ⟨4699240794146798651126747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12531308784391463069671325 4699240794146798651126747)
            ·
              refine ⟨7048861191220197976690121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4699240794146798651126747 7048861191220197976690121)
              ·
                refine ⟨5286645893415148482517591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7048861191220197976690121 5286645893415148482517591)
                ·
                  refine ⟨7929968840122722723776387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5286645893415148482517591 7929968840122722723776387)
                  ·
                    refine ⟨11894953260184084085664581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7929968840122722723776387 11894953260184084085664581)
                    ·
                      refine ⟨2230303736284515766062109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11894953260184084085664581 2230303736284515766062109)
                      ·
                        rfl

theorem cell23_4343501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 3, 1, 2, 1, 1, 4].length) (baseStart_4343501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4343501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4343501 prefixEnd_4343501 := by exact prefixLift 4343501
  have htrace : WordTrace (prefixWord ++ tailWord_4343501) baseStart_4343501 baseEnd_4343501 := by
    simpa [prefixWord, tailWord_4343501, baseEnd_4343501] using wordTrace_append hprefix tailTrace_4343501
  have hstable : (prefixWord ++ tailWord_4343501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4343501).length < 2 ^ (prefixWord ++ tailWord_4343501).sum := by decide
  have hdescent : baseEnd_4343501 < baseStart_4343501 := by decide
  rcases family_descends (prefixWord ++ tailWord_4343501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4343534 : List Nat := [4, 1, 2, 1, 1, 2, 4, 2, 2, 1, 3]
def baseStart_4343534 : Nat := 118140960795 + 4343534 * 2 ^ 59
def prefixEnd_4343534 : Nat := 4983230072969 + 3 ^ 40 * 4343534 * 2
def baseEnd_4343534 : Nat := 2230320681146114136949457

theorem tailTrace_4343534 : CollatzResearch.WordTrace tailWord_4343534 prefixEnd_4343534 2230320681146114136949457 := by
  unfold tailWord_4343534
  simp only [CollatzResearch.WordTrace]
  refine ⟨19802712480765701174159707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 105614466564083739595518437 19802712480765701174159707)
  ·
    refine ⟨29704068721148551761239561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19802712480765701174159707 29704068721148551761239561)
    ·
      refine ⟨22278051540861413820929671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29704068721148551761239561 22278051540861413820929671)
      ·
        refine ⟨33417077311292120731394507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22278051540861413820929671 33417077311292120731394507)
        ·
          refine ⟨50125615966938181097091761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33417077311292120731394507 50125615966938181097091761)
          ·
            refine ⟨37594211975203635822818821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50125615966938181097091761 37594211975203635822818821)
            ·
              refine ⟨7048914745350681716778529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 37594211975203635822818821 7048914745350681716778529)
              ·
                refine ⟨5286686059013011287583897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7048914745350681716778529 5286686059013011287583897)
                ·
                  refine ⟨3965014544259758465687923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5286686059013011287583897 3965014544259758465687923)
                  ·
                    refine ⟨5947521816389637698531885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3965014544259758465687923 5947521816389637698531885)
                    ·
                      refine ⟨2230320681146114136949457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5947521816389637698531885 2230320681146114136949457)
                      ·
                        rfl

theorem cell23_4343534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 4, 2, 2, 1, 3].length) (baseStart_4343534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4343534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4343534 prefixEnd_4343534 := by exact prefixLift 4343534
  have htrace : WordTrace (prefixWord ++ tailWord_4343534) baseStart_4343534 baseEnd_4343534 := by
    simpa [prefixWord, tailWord_4343534, baseEnd_4343534] using wordTrace_append hprefix tailTrace_4343534
  have hstable : (prefixWord ++ tailWord_4343534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4343534).length < 2 ^ (prefixWord ++ tailWord_4343534).sum := by decide
  have hdescent : baseEnd_4343534 < baseStart_4343534 := by decide
  rcases family_descends (prefixWord ++ tailWord_4343534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4343543 : List Nat := [1, 1, 3, 1, 1, 1, 4, 2, 1, 3, 5]
def baseStart_4343543 : Nat := 118140960795 + 4343543 * 2 ^ 59
def prefixEnd_4343543 : Nat := 4983230072969 + 3 ^ 40 * 4343543 * 2
def baseEnd_4343543 : Nat := 2230325302472004601736915

theorem tailTrace_4343543 : CollatzResearch.WordTrace tailWord_4343543 prefixEnd_4343543 2230325302472004601736915 := by
  unfold tailWord_4343543
  simp only [CollatzResearch.WordTrace]
  refine ⟨158422028103093003930355283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105614685402062002620236855 158422028103093003930355283)
  ·
    refine ⟨237633042154639505895532925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158422028103093003930355283 237633042154639505895532925)
    ·
      refine ⟨89112390807989814710824847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 237633042154639505895532925 89112390807989814710824847)
      ·
        refine ⟨133668586211984722066237271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89112390807989814710824847 133668586211984722066237271)
        ·
          refine ⟨200502879317977083099355907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 133668586211984722066237271 200502879317977083099355907)
          ·
            refine ⟨300754318976965624649033861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 200502879317977083099355907 300754318976965624649033861)
            ·
              refine ⟨56391434808181054621693849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 300754318976965624649033861 56391434808181054621693849)
              ·
                refine ⟨42293576106135790966270387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 56391434808181054621693849 42293576106135790966270387)
                ·
                  refine ⟨63440364159203686449405581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 42293576106135790966270387 63440364159203686449405581)
                  ·
                    refine ⟨23790136559701382418527093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 63440364159203686449405581 23790136559701382418527093)
                    ·
                      refine ⟨2230325302472004601736915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23790136559701382418527093 2230325302472004601736915)
                      ·
                        rfl

theorem cell23_4343543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 2, 1, 3, 5].length) (baseStart_4343543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4343543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4343543 prefixEnd_4343543 := by exact prefixLift 4343543
  have htrace : WordTrace (prefixWord ++ tailWord_4343543) baseStart_4343543 baseEnd_4343543 := by
    simpa [prefixWord, tailWord_4343543, baseEnd_4343543] using wordTrace_append hprefix tailTrace_4343543
  have hstable : (prefixWord ++ tailWord_4343543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4343543).length < 2 ^ (prefixWord ++ tailWord_4343543).sum := by decide
  have hdescent : baseEnd_4343543 < baseStart_4343543 := by decide
  rcases family_descends (prefixWord ++ tailWord_4343543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4343557 : List Nat := [1, 3, 1, 1, 2, 1, 1, 1, 8, 2, 2]
def baseStart_4343557 : Nat := 118140960795 + 4343557 * 2 ^ 59
def prefixEnd_4343557 : Nat := 4983230072969 + 3 ^ 40 * 4343557 * 2
def baseEnd_4343557 : Nat := 2230332491201167546961851

theorem tailTrace_4343557 : CollatzResearch.WordTrace tailWord_4343557 prefixEnd_4343557 2230332491201167546961851 := by
  unfold tailWord_4343557
  simp only [CollatzResearch.WordTrace]
  refine ⟨158422538725042284321364925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105615025816694856214243283 158422538725042284321364925)
  ·
    refine ⟨59408452021890856620511847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 158422538725042284321364925 59408452021890856620511847)
    ·
      refine ⟨89112678032836284930767771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59408452021890856620511847 89112678032836284930767771)
      ·
        refine ⟨133669017049254427396151657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89112678032836284930767771 133669017049254427396151657)
        ·
          refine ⟨100251762786940820547113743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 133669017049254427396151657 100251762786940820547113743)
          ·
            refine ⟨150377644180411230820670615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 100251762786940820547113743 150377644180411230820670615)
            ·
              refine ⟨225566466270616846231005923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 150377644180411230820670615 225566466270616846231005923)
              ·
                refine ⟨338349699405925269346508885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 225566466270616846231005923 338349699405925269346508885)
                ·
                  refine ⟨3965035539913186750154401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 338349699405925269346508885 3965035539913186750154401)
                  ·
                    refine ⟨2973776654934890062615801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3965035539913186750154401 2973776654934890062615801)
                    ·
                      refine ⟨2230332491201167546961851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2973776654934890062615801 2230332491201167546961851)
                      ·
                        rfl

theorem cell23_4343557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 1, 8, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 1, 8, 2, 2].length) (baseStart_4343557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4343557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4343557 prefixEnd_4343557 := by exact prefixLift 4343557
  have htrace : WordTrace (prefixWord ++ tailWord_4343557) baseStart_4343557 baseEnd_4343557 := by
    simpa [prefixWord, tailWord_4343557, baseEnd_4343557] using wordTrace_append hprefix tailTrace_4343557
  have hstable : (prefixWord ++ tailWord_4343557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4343557).length < 2 ^ (prefixWord ++ tailWord_4343557).sum := by decide
  have hdescent : baseEnd_4343557 < baseStart_4343557 := by decide
  rcases family_descends (prefixWord ++ tailWord_4343557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4343560 : List Nat := [2, 1, 3, 2, 2, 1, 1, 2, 2, 4, 3]
def baseStart_4343560 : Nat := 118140960795 + 4343560 * 2 ^ 59
def prefixEnd_4343560 : Nat := 4983230072969 + 3 ^ 40 * 4343560 * 2
def baseEnd_4343560 : Nat := 2230334031643131035224337

theorem tailTrace_4343560 : CollatzResearch.WordTrace tailWord_4343560 prefixEnd_4343560 2230334031643131035224337 := by
  unfold tailWord_4343560
  simp only [CollatzResearch.WordTrace]
  refine ⟨79211324072015707916862067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105615098762687610555816089 79211324072015707916862067)
  ·
    refine ⟨118816986108023561875293101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79211324072015707916862067 118816986108023561875293101)
    ·
      refine ⟨44556369790508835703234913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 118816986108023561875293101 44556369790508835703234913)
      ·
        refine ⟨33417277342881626777426185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44556369790508835703234913 33417277342881626777426185)
        ·
          refine ⟨25062958007161220083069639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33417277342881626777426185 25062958007161220083069639)
          ·
            refine ⟨37594437010741830124604459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25062958007161220083069639 37594437010741830124604459)
            ·
              refine ⟨56391655516112745186906689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37594437010741830124604459 56391655516112745186906689)
              ·
                refine ⟨42293741637084558890180017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 56391655516112745186906689 42293741637084558890180017)
                ·
                  refine ⟨31720306227813419167635013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 42293741637084558890180017 31720306227813419167635013)
                  ·
                    refine ⟨5947557417715016093931565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 31720306227813419167635013 5947557417715016093931565)
                    ·
                      refine ⟨2230334031643131035224337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5947557417715016093931565 2230334031643131035224337)
                      ·
                        rfl

theorem cell23_4343560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 2, 2, 4, 3].length) (baseStart_4343560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4343560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4343560 prefixEnd_4343560 := by exact prefixLift 4343560
  have htrace : WordTrace (prefixWord ++ tailWord_4343560) baseStart_4343560 baseEnd_4343560 := by
    simpa [prefixWord, tailWord_4343560, baseEnd_4343560] using wordTrace_append hprefix tailTrace_4343560
  have hstable : (prefixWord ++ tailWord_4343560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4343560).length < 2 ^ (prefixWord ++ tailWord_4343560).sum := by decide
  have hdescent : baseEnd_4343560 < baseStart_4343560 := by decide
  rcases family_descends (prefixWord ++ tailWord_4343560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4343563 : List Nat := [1, 1, 1, 1, 5, 1, 3, 1, 9]
def baseStart_4343563 : Nat := 118140960795 + 4343563 * 2 ^ 59
def prefixEnd_4343563 : Nat := 4983230072969 + 3 ^ 40 * 4343563 * 2
def baseEnd_4343563 : Nat := 247815063565010502609647

theorem tailTrace_4343563 : CollatzResearch.WordTrace tailWord_4343563 prefixEnd_4343563 247815063565010502609647 := by
  unfold tailWord_4343563
  simp only [CollatzResearch.WordTrace]
  refine ⟨158422757563020547346083343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105615171708680364897388895 158422757563020547346083343)
  ·
    refine ⟨237634136344530821019125015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158422757563020547346083343 237634136344530821019125015)
    ·
      refine ⟨356451204516796231528687523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 237634136344530821019125015 356451204516796231528687523)
      ·
        refine ⟨534676806775194347293031285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 356451204516796231528687523 534676806775194347293031285)
        ·
          refine ⟨50125950635174470058721683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 534676806775194347293031285 50125950635174470058721683)
          ·
            refine ⟨75188925952761705088082525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50125950635174470058721683 75188925952761705088082525)
            ·
              refine ⟨28195847232285639408030947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 75188925952761705088082525 28195847232285639408030947)
              ·
                refine ⟨42293770848428459112046421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28195847232285639408030947 42293770848428459112046421)
                ·
                  refine ⟨247815063565010502609647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 42293770848428459112046421 247815063565010502609647)
                  ·
                    rfl

theorem cell23_4343563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 3, 1, 9].length) (baseStart_4343563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4343563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4343563 prefixEnd_4343563 := by exact prefixLift 4343563
  have htrace : WordTrace (prefixWord ++ tailWord_4343563) baseStart_4343563 baseEnd_4343563 := by
    simpa [prefixWord, tailWord_4343563, baseEnd_4343563] using wordTrace_append hprefix tailTrace_4343563
  have hstable : (prefixWord ++ tailWord_4343563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4343563).length < 2 ^ (prefixWord ++ tailWord_4343563).sum := by decide
  have hdescent : baseEnd_4343563 < baseStart_4343563 := by decide
  rcases family_descends (prefixWord ++ tailWord_4343563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4343572 : List Nat := [2, 4, 4, 1, 2, 1, 2, 1, 1, 2, 3]
def baseStart_4343572 : Nat := 118140960795 + 4343572 * 2 ^ 59
def prefixEnd_4343572 : Nat := 4983230072969 + 3 ^ 40 * 4343572 * 2
def baseEnd_4343572 : Nat := 2230340193410984988274283

theorem tailTrace_4343572 : CollatzResearch.WordTrace tailWord_4343572 prefixEnd_4343572 2230340193410984988274283 := by
  unfold tailWord_4343572
  simp only [CollatzResearch.WordTrace]
  refine ⟨79211542909993970941580485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105615390546658627922107313 79211542909993970941580485)
  ·
    refine ⟨14852164295623869551546341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 79211542909993970941580485 14852164295623869551546341)
    ·
      refine ⟨2784780805429475540914939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14852164295623869551546341 2784780805429475540914939)
      ·
        refine ⟨4177171208144213311372409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2784780805429475540914939 4177171208144213311372409)
        ·
          refine ⟨3132878406108159983529307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4177171208144213311372409 3132878406108159983529307)
          ·
            refine ⟨4699317609162239975293961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3132878406108159983529307 4699317609162239975293961)
            ·
              refine ⟨3524488206871679981470471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4699317609162239975293961 3524488206871679981470471)
              ·
                refine ⟨5286732310307519972205707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3524488206871679981470471 5286732310307519972205707)
                ·
                  refine ⟨7930098465461279958308561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5286732310307519972205707 7930098465461279958308561)
                  ·
                    refine ⟨5947573849095959968731421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7930098465461279958308561 5947573849095959968731421)
                    ·
                      refine ⟨2230340193410984988274283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5947573849095959968731421 2230340193410984988274283)
                      ·
                        rfl

theorem cell23_4343572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 2, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 2, 1, 2, 1, 1, 2, 3].length) (baseStart_4343572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4343572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4343572 prefixEnd_4343572 := by exact prefixLift 4343572
  have htrace : WordTrace (prefixWord ++ tailWord_4343572) baseStart_4343572 baseEnd_4343572 := by
    simpa [prefixWord, tailWord_4343572, baseEnd_4343572] using wordTrace_append hprefix tailTrace_4343572
  have hstable : (prefixWord ++ tailWord_4343572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4343572).length < 2 ^ (prefixWord ++ tailWord_4343572).sum := by decide
  have hdescent : baseEnd_4343572 < baseStart_4343572 := by decide
  rcases family_descends (prefixWord ++ tailWord_4343572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4343593 : List Nat := [1, 2, 1, 1, 1, 1, 1, 3, 5, 7]
def baseStart_4343593 : Nat := 118140960795 + 4343593 * 2 ^ 59
def prefixEnd_4343593 : Nat := 4983230072969 + 3 ^ 40 * 4343593 * 2
def baseEnd_4343593 : Nat := 743450325501576468703895

theorem tailTrace_4343593 : CollatzResearch.WordTrace tailWord_4343593 prefixEnd_4343593 743450325501576468703895 := by
  unfold tailWord_4343593
  simp only [CollatzResearch.WordTrace]
  refine ⟨158423851752911862469675433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105615901168607908313116955 158423851752911862469675433)
  ·
    refine ⟨118817888814683896852256575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 158423851752911862469675433 118817888814683896852256575)
    ·
      refine ⟨178226833222025845278384863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118817888814683896852256575 178226833222025845278384863)
      ·
        refine ⟨267340249833038767917577295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 178226833222025845278384863 267340249833038767917577295)
        ·
          refine ⟨401010374749558151876365943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 267340249833038767917577295 401010374749558151876365943)
          ·
            refine ⟨601515562124337227814548915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 401010374749558151876365943 601515562124337227814548915)
            ·
              refine ⟨902273343186505841721823373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 601515562124337227814548915 902273343186505841721823373)
              ·
                refine ⟨338352503694939690645683765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 902273343186505841721823373 338352503694939690645683765)
                ·
                  refine ⟨31720547221400595998032853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 338352503694939690645683765 31720547221400595998032853)
                  ·
                    refine ⟨743450325501576468703895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 31720547221400595998032853 743450325501576468703895)
                    ·
                      rfl

theorem cell23_4343593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 3, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 3, 5, 7].length) (baseStart_4343593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4343593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4343593 prefixEnd_4343593 := by exact prefixLift 4343593
  have htrace : WordTrace (prefixWord ++ tailWord_4343593) baseStart_4343593 baseEnd_4343593 := by
    simpa [prefixWord, tailWord_4343593, baseEnd_4343593] using wordTrace_append hprefix tailTrace_4343593
  have hstable : (prefixWord ++ tailWord_4343593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4343593).length < 2 ^ (prefixWord ++ tailWord_4343593).sum := by decide
  have hdescent : baseEnd_4343593 < baseStart_4343593 := by decide
  rcases family_descends (prefixWord ++ tailWord_4343593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4343610 : List Nat := [3, 1, 1, 1, 5, 1, 1, 2, 1, 7]
def baseStart_4343610 : Nat := 118140960795 + 4343610 * 2 ^ 59
def prefixEnd_4343610 : Nat := 4983230072969 + 3 ^ 40 * 4343610 * 2
def baseEnd_4343610 : Nat := 743453235225285279866369

theorem tailTrace_4343610 : CollatzResearch.WordTrace tailWord_4343610 prefixEnd_4343610 743453235225285279866369 := by
  unfold tailWord_4343610
  simp only [CollatzResearch.WordTrace]
  refine ⟨39606117948462568593261071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105616314529233516248696189 39606117948462568593261071)
  ·
    refine ⟨59409176922693852889891607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39606117948462568593261071 59409176922693852889891607)
    ·
      refine ⟨89113765384040779334837411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59409176922693852889891607 89113765384040779334837411)
      ·
        refine ⟨133670648076061169002256117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89113765384040779334837411 133670648076061169002256117)
        ·
          refine ⟨12531623257130734593961511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 133670648076061169002256117 12531623257130734593961511)
          ·
            refine ⟨18797434885696101890942267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12531623257130734593961511 18797434885696101890942267)
            ·
              refine ⟨28196152328544152836413401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18797434885696101890942267 28196152328544152836413401)
              ·
                refine ⟨21147114246408114627310051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28196152328544152836413401 21147114246408114627310051)
                ·
                  refine ⟨31720671369612171940965077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21147114246408114627310051 31720671369612171940965077)
                  ·
                    refine ⟨743453235225285279866369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 31720671369612171940965077 743453235225285279866369)
                    ·
                      rfl

theorem cell23_4343610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 1, 2, 1, 7].length) (baseStart_4343610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4343610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4343610 prefixEnd_4343610 := by exact prefixLift 4343610
  have htrace : WordTrace (prefixWord ++ tailWord_4343610) baseStart_4343610 baseEnd_4343610 := by
    simpa [prefixWord, tailWord_4343610, baseEnd_4343610] using wordTrace_append hprefix tailTrace_4343610
  have hstable : (prefixWord ++ tailWord_4343610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4343610).length < 2 ^ (prefixWord ++ tailWord_4343610).sum := by decide
  have hdescent : baseEnd_4343610 < baseStart_4343610 := by decide
  rcases family_descends (prefixWord ++ tailWord_4343610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4343644 : List Nat := [2, 2, 4, 2, 2, 1, 1, 2, 2, 5]
def baseStart_4343644 : Nat := 118140960795 + 4343644 * 2 ^ 59
def prefixEnd_4343644 : Nat := 4983230072969 + 3 ^ 40 * 4343644 * 2
def baseEnd_4343644 : Nat := 743459054672702902191317

theorem tailTrace_4343644 : CollatzResearch.WordTrace tailWord_4343644 prefixEnd_4343644 743459054672702902191317 := by
  unfold tailWord_4343644
  simp only [CollatzResearch.WordTrace]
  refine ⟨79212855937863549089890993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105617141250484732119854657 79212855937863549089890993)
  ·
    refine ⟨59409641953397661817418245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79212855937863549089890993 59409641953397661817418245)
    ·
      refine ⟨11139307866262061590765921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 59409641953397661817418245 11139307866262061590765921)
      ·
        refine ⟨8354480899696546193074441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11139307866262061590765921 8354480899696546193074441)
        ·
          refine ⟨6265860674772409644805831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8354480899696546193074441 6265860674772409644805831)
          ·
            refine ⟨9398791012158614467208747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6265860674772409644805831 9398791012158614467208747)
            ·
              refine ⟨14098186518237921700813121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9398791012158614467208747 14098186518237921700813121)
              ·
                refine ⟨10573639888678441275609841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14098186518237921700813121 10573639888678441275609841)
                ·
                  refine ⟨7930229916508830956707381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10573639888678441275609841 7930229916508830956707381)
                  ·
                    refine ⟨743459054672702902191317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7930229916508830956707381 743459054672702902191317)
                    ·
                      rfl

theorem cell23_4343644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 1, 2, 2, 5].length) (baseStart_4343644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4343644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4343644 prefixEnd_4343644 := by exact prefixLift 4343644
  have htrace : WordTrace (prefixWord ++ tailWord_4343644) baseStart_4343644 baseEnd_4343644 := by
    simpa [prefixWord, tailWord_4343644, baseEnd_4343644] using wordTrace_append hprefix tailTrace_4343644
  have hstable : (prefixWord ++ tailWord_4343644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4343644).length < 2 ^ (prefixWord ++ tailWord_4343644).sum := by decide
  have hdescent : baseEnd_4343644 < baseStart_4343644 := by decide
  rcases family_descends (prefixWord ++ tailWord_4343644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4343647 : List Nat := [1, 1, 2, 3, 1, 5, 1, 2, 2, 1, 4]
def baseStart_4343647 : Nat := 118140960795 + 4343647 * 2 ^ 59
def prefixEnd_4343647 : Nat := 4983230072969 + 3 ^ 40 * 4343647 * 2
def baseEnd_4343647 : Nat := 2230378704460072194836437

theorem tailTrace_4343647 : CollatzResearch.WordTrace tailWord_4343647 prefixEnd_4343647 2230378704460072194836437 := by
  unfold tailWord_4343647
  simp only [CollatzResearch.WordTrace]
  refine ⟨158425821294716229692141195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105617214196477486461427463 158425821294716229692141195)
  ·
    refine ⟨237638731942074344538211793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158425821294716229692141195 237638731942074344538211793)
    ·
      refine ⟨178229048956555758403658845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 237638731942074344538211793 178229048956555758403658845)
      ·
        refine ⟨66835893358708409401372067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 178229048956555758403658845 66835893358708409401372067)
        ·
          refine ⟨100253840038062614102058101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66835893358708409401372067 100253840038062614102058101)
          ·
            refine ⟨9398797503568370072067947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 100253840038062614102058101 9398797503568370072067947)
            ·
              refine ⟨14098196255352555108101921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9398797503568370072067947 14098196255352555108101921)
              ·
                refine ⟨10573647191514416331076441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14098196255352555108101921 10573647191514416331076441)
                ·
                  refine ⟨7930235393635812248307331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10573647191514416331076441 7930235393635812248307331)
                  ·
                    refine ⟨11895353090453718372460997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7930235393635812248307331 11895353090453718372460997)
                    ·
                      refine ⟨2230378704460072194836437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11895353090453718372460997 2230378704460072194836437)
                      ·
                        rfl

theorem cell23_4343647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 1, 2, 2, 1, 4].length) (baseStart_4343647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4343647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4343647 prefixEnd_4343647 := by exact prefixLift 4343647
  have htrace : WordTrace (prefixWord ++ tailWord_4343647) baseStart_4343647 baseEnd_4343647 := by
    simpa [prefixWord, tailWord_4343647, baseEnd_4343647] using wordTrace_append hprefix tailTrace_4343647
  have hstable : (prefixWord ++ tailWord_4343647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4343647).length < 2 ^ (prefixWord ++ tailWord_4343647).sum := by decide
  have hdescent : baseEnd_4343647 < baseStart_4343647 := by decide
  rcases family_descends (prefixWord ++ tailWord_4343647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4343681 : List Nat := [1, 2, 4, 4, 1, 1, 2, 1, 2, 1, 4]
def baseStart_4343681 : Nat := 118140960795 + 4343681 * 2 ^ 59
def prefixEnd_4343681 : Nat := 4983230072969 + 3 ^ 40 * 4343681 * 2
def baseEnd_4343681 : Nat := 2230396162802325061811281

theorem tailTrace_4343681 : CollatzResearch.WordTrace tailWord_4343681 prefixEnd_4343681 2230396162802325061811281 := by
  unfold tailWord_4343681
  simp only [CollatzResearch.WordTrace]
  refine ⟨158427061376593053498878897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105618040917728702332585931 158427061376593053498878897)
  ·
    refine ⟨118820296032444790124159173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 158427061376593053498878897 118820296032444790124159173)
    ·
      refine ⟨22278805506083398148279845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 118820296032444790124159173 22278805506083398148279845)
      ·
        refine ⟨4177276032390637152802471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22278805506083398148279845 4177276032390637152802471)
        ·
          refine ⟨6265914048585955729203707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4177276032390637152802471 6265914048585955729203707)
          ·
            refine ⟨9398871072878933593805561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6265914048585955729203707 9398871072878933593805561)
            ·
              refine ⟨7049153304659200195354171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9398871072878933593805561 7049153304659200195354171)
              ·
                refine ⟨10573729956988800293031257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7049153304659200195354171 10573729956988800293031257)
                ·
                  refine ⟨7930297467741600219773443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10573729956988800293031257 7930297467741600219773443)
                  ·
                    refine ⟨11895446201612400329660165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7930297467741600219773443 11895446201612400329660165)
                    ·
                      refine ⟨2230396162802325061811281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11895446201612400329660165 2230396162802325061811281)
                      ·
                        rfl

theorem cell23_4343681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 2, 1, 2, 1, 4].length) (baseStart_4343681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4343681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4343681 prefixEnd_4343681 := by exact prefixLift 4343681
  have htrace : WordTrace (prefixWord ++ tailWord_4343681) baseStart_4343681 baseEnd_4343681 := by
    simpa [prefixWord, tailWord_4343681, baseEnd_4343681] using wordTrace_append hprefix tailTrace_4343681
  have hstable : (prefixWord ++ tailWord_4343681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4343681).length < 2 ^ (prefixWord ++ tailWord_4343681).sum := by decide
  have hdescent : baseEnd_4343681 < baseStart_4343681 := by decide
  rcases family_descends (prefixWord ++ tailWord_4343681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4343708 : List Nat := [2, 2, 3, 3, 1, 1, 4, 2, 1, 4]
def baseStart_4343708 : Nat := 118140960795 + 4343708 * 2 ^ 59
def prefixEnd_4343708 : Nat := 4983230072969 + 3 ^ 40 * 4343708 * 2
def baseEnd_4343708 : Nat := 743470008926665485391219

theorem tailTrace_4343708 : CollatzResearch.WordTrace tailWord_4343708 prefixEnd_4343708 743470008926665485391219 := by
  unfold tailWord_4343708
  simp only [CollatzResearch.WordTrace]
  refine ⟨79214023073747618555055889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105618697431663491406741185 79214023073747618555055889)
  ·
    refine ⟨59410517305310713916291917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79214023073747618555055889 59410517305310713916291917)
    ·
      refine ⟨22278943989491517718609469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59410517305310713916291917 22278943989491517718609469)
      ·
        refine ⟨8354603996059319144478551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22278943989491517718609469 8354603996059319144478551)
        ·
          refine ⟨12531905994088978716717827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8354603996059319144478551 12531905994088978716717827)
          ·
            refine ⟨18797858991133468075076741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12531905994088978716717827 18797858991133468075076741)
            ·
              refine ⟨3524598560837525264076889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18797858991133468075076741 3524598560837525264076889)
              ·
                refine ⟨2643448920628143948057667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3524598560837525264076889 2643448920628143948057667)
                ·
                  refine ⟨3965173380942215922086501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2643448920628143948057667 3965173380942215922086501)
                  ·
                    refine ⟨743470008926665485391219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3965173380942215922086501 743470008926665485391219)
                    ·
                      rfl

theorem cell23_4343708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 4, 2, 1, 4].length) (baseStart_4343708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4343708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4343708 prefixEnd_4343708 := by exact prefixLift 4343708
  have htrace : WordTrace (prefixWord ++ tailWord_4343708) baseStart_4343708 baseEnd_4343708 := by
    simpa [prefixWord, tailWord_4343708, baseEnd_4343708] using wordTrace_append hprefix tailTrace_4343708
  have hstable : (prefixWord ++ tailWord_4343708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4343708).length < 2 ^ (prefixWord ++ tailWord_4343708).sum := by decide
  have hdescent : baseEnd_4343708 < baseStart_4343708 := by decide
  rcases family_descends (prefixWord ++ tailWord_4343708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4343737 : List Nat := [1, 2, 1, 4, 2, 1, 1, 3, 3, 1, 4]
def baseStart_4343737 : Nat := 118140960795 + 4343737 * 2 ^ 59
def prefixEnd_4343737 : Nat := 4983230072969 + 3 ^ 40 * 4343737 * 2
def baseEnd_4343737 : Nat := 2230424917718976842711023

theorem tailTrace_4343737 : CollatzResearch.WordTrace tailWord_4343737 prefixEnd_4343737 2230424917718976842711023 := by
  unfold tailWord_4343737
  simp only [CollatzResearch.WordTrace]
  refine ⟨158429103864390175062917465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105619402576260116708611643 158429103864390175062917465)
  ·
    refine ⟨118821827898292631297188099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 158429103864390175062917465 118821827898292631297188099)
    ·
      refine ⟨178232741847438946945782149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118821827898292631297188099 178232741847438946945782149)
      ·
        refine ⟨33418639096394802552334153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 178232741847438946945782149 33418639096394802552334153)
        ·
          refine ⟨25063979322296101914250615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33418639096394802552334153 25063979322296101914250615)
          ·
            refine ⟨37595968983444152871375923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25063979322296101914250615 37595968983444152871375923)
            ·
              refine ⟨56393953475166229307063885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37595968983444152871375923 56393953475166229307063885)
              ·
                refine ⟨21147732553187335990148957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 56393953475166229307063885 21147732553187335990148957)
                ·
                  refine ⟨7930399707445250996305859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21147732553187335990148957 7930399707445250996305859)
                  ·
                    refine ⟨11895599561167876494458789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7930399707445250996305859 11895599561167876494458789)
                    ·
                      refine ⟨2230424917718976842711023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11895599561167876494458789 2230424917718976842711023)
                      ·
                        rfl

theorem cell23_4343737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 3, 3, 1, 4].length) (baseStart_4343737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4343737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4343737 prefixEnd_4343737 := by exact prefixLift 4343737
  have htrace : WordTrace (prefixWord ++ tailWord_4343737) baseStart_4343737 baseEnd_4343737 := by
    simpa [prefixWord, tailWord_4343737, baseEnd_4343737] using wordTrace_append hprefix tailTrace_4343737
  have hstable : (prefixWord ++ tailWord_4343737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4343737).length < 2 ^ (prefixWord ++ tailWord_4343737).sum := by decide
  have hdescent : baseEnd_4343737 < baseStart_4343737 := by decide
  rcases family_descends (prefixWord ++ tailWord_4343737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4343741 : List Nat := [1, 4, 1, 2, 3, 1, 3, 1, 2, 3, 2]
def baseStart_4343741 : Nat := 118140960795 + 4343741 * 2 ^ 59
def prefixEnd_4343741 : Nat := 4983230072969 + 3 ^ 40 * 4343741 * 2
def baseEnd_4343741 : Nat := 2230426971641594827061005

theorem tailTrace_4343741 : CollatzResearch.WordTrace tailWord_4343741 prefixEnd_4343741 2230426971641594827061005 := by
  unfold tailWord_4343741
  simp only [CollatzResearch.WordTrace]
  refine ⟨158429249756375683746063077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105619499837583789164042051 158429249756375683746063077)
  ·
    refine ⟨29705484329320440702386827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 158429249756375683746063077 29705484329320440702386827)
    ·
      refine ⟨44558226493980661053580241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29705484329320440702386827 44558226493980661053580241)
      ·
        refine ⟨33418669870485495790185181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44558226493980661053580241 33418669870485495790185181)
        ·
          refine ⟨12532001201432060921319443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33418669870485495790185181 12532001201432060921319443)
          ·
            refine ⟨18798001802148091381979165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12532001201432060921319443 18798001802148091381979165)
            ·
              refine ⟨7049250675805534268242187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18798001802148091381979165 7049250675805534268242187)
              ·
                refine ⟨10573876013708301402363281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7049250675805534268242187 10573876013708301402363281)
                ·
                  refine ⟨7930407010281226051772461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10573876013708301402363281 7930407010281226051772461)
                  ·
                    refine ⟨2973902628855459769414673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7930407010281226051772461 2973902628855459769414673)
                    ·
                      refine ⟨2230426971641594827061005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2973902628855459769414673 2230426971641594827061005)
                      ·
                        rfl

theorem cell23_4343741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 3, 1, 2, 3, 2].length) (baseStart_4343741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4343741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4343741 prefixEnd_4343741 := by exact prefixLift 4343741
  have htrace : WordTrace (prefixWord ++ tailWord_4343741) baseStart_4343741 baseEnd_4343741 := by
    simpa [prefixWord, tailWord_4343741, baseEnd_4343741] using wordTrace_append hprefix tailTrace_4343741
  have hstable : (prefixWord ++ tailWord_4343741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4343741).length < 2 ^ (prefixWord ++ tailWord_4343741).sum := by decide
  have hdescent : baseEnd_4343741 < baseStart_4343741 := by decide
  rcases family_descends (prefixWord ++ tailWord_4343741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4343764 : List Nat := [2, 4, 1, 2, 1, 1, 3, 1, 4, 4]
def baseStart_4343764 : Nat := 118140960795 + 4343764 * 2 ^ 59
def prefixEnd_4343764 : Nat := 4983230072969 + 3 ^ 40 * 4343764 * 2
def baseEnd_4343764 : Nat := 743479593898882745691133

theorem tailTrace_4343764 : CollatzResearch.WordTrace tailWord_4343764 prefixEnd_4343764 743479593898882745691133 := by
  unfold tailWord_4343764
  simp only [CollatzResearch.WordTrace]
  refine ⟨79215044317646179337075173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105620059090194905782766897 79215044317646179337075173)
  ·
    refine ⟨14852820809558658625701595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 79215044317646179337075173 14852820809558658625701595)
    ·
      refine ⟨22279231214337987938552393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14852820809558658625701595 22279231214337987938552393)
      ·
        refine ⟨16709423410753490953914295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22279231214337987938552393 16709423410753490953914295)
        ·
          refine ⟨25064135116130236430871443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16709423410753490953914295 25064135116130236430871443)
          ·
            refine ⟨37596202674195354646307165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25064135116130236430871443 37596202674195354646307165)
            ·
              refine ⟨14098576002823257992365187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37596202674195354646307165 14098576002823257992365187)
              ·
                refine ⟨21147864004234886988547781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14098576002823257992365187 21147864004234886988547781)
                ·
                  refine ⟨3965224500794041310352709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21147864004234886988547781 3965224500794041310352709)
                  ·
                    refine ⟨743479593898882745691133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3965224500794041310352709 743479593898882745691133)
                    ·
                      rfl

theorem cell23_4343764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 3, 1, 4, 4].length) (baseStart_4343764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4343764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4343764 prefixEnd_4343764 := by exact prefixLift 4343764
  have htrace : WordTrace (prefixWord ++ tailWord_4343764) baseStart_4343764 baseEnd_4343764 := by
    simpa [prefixWord, tailWord_4343764, baseEnd_4343764] using wordTrace_append hprefix tailTrace_4343764
  have hstable : (prefixWord ++ tailWord_4343764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4343764).length < 2 ^ (prefixWord ++ tailWord_4343764).sum := by decide
  have hdescent : baseEnd_4343764 < baseStart_4343764 := by decide
  rcases family_descends (prefixWord ++ tailWord_4343764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4343804 : List Nat := [2, 2, 2, 1, 2, 2, 1, 1, 6, 1, 3]
def baseStart_4343804 : Nat := 118140960795 + 4343804 * 2 ^ 59
def prefixEnd_4343804 : Nat := 4983230072969 + 3 ^ 40 * 4343804 * 2
def baseEnd_4343804 : Nat := 2230459320922828080573215

theorem tailTrace_4343804 : CollatzResearch.WordTrace tailWord_4343804 prefixEnd_4343804 2230459320922828080573215 := by
  unfold tailWord_4343804
  simp only [CollatzResearch.WordTrace]
  refine ⟨79215773777573722752803233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105621031703431630337070977 79215773777573722752803233)
  ·
    refine ⟨59411830333180292064602425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79215773777573722752803233 59411830333180292064602425)
    ·
      refine ⟨44558872749885219048451819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59411830333180292064602425 44558872749885219048451819)
      ·
        refine ⟨66838309124827828572677729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44558872749885219048451819 66838309124827828572677729)
        ·
          refine ⟨50128731843620871429508297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66838309124827828572677729 50128731843620871429508297)
          ·
            refine ⟨37596548882715653572131223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50128731843620871429508297 37596548882715653572131223)
            ·
              refine ⟨56394823324073480358196835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37596548882715653572131223 56394823324073480358196835)
              ·
                refine ⟨84592234986110220537295253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56394823324073480358196835 84592234986110220537295253)
                ·
                  refine ⟨3965261014973916587685715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 84592234986110220537295253 3965261014973916587685715)
                  ·
                    refine ⟨5947891522460874881528573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3965261014973916587685715 5947891522460874881528573)
                    ·
                      refine ⟨2230459320922828080573215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5947891522460874881528573 2230459320922828080573215)
                      ·
                        rfl

theorem cell23_4343804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 1, 6, 1, 3].length) (baseStart_4343804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4343804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4343804 prefixEnd_4343804 := by exact prefixLift 4343804
  have htrace : WordTrace (prefixWord ++ tailWord_4343804) baseStart_4343804 baseEnd_4343804 := by
    simpa [prefixWord, tailWord_4343804, baseEnd_4343804] using wordTrace_append hprefix tailTrace_4343804
  have hstable : (prefixWord ++ tailWord_4343804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4343804).length < 2 ^ (prefixWord ++ tailWord_4343804).sum := by decide
  have hdescent : baseEnd_4343804 < baseStart_4343804 := by decide
  rcases family_descends (prefixWord ++ tailWord_4343804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4343861 : List Nat := [1, 3, 3, 1, 1, 1, 2, 1, 6, 2, 2]
def baseStart_4343861 : Nat := 118140960795 + 4343861 * 2 ^ 59
def prefixEnd_4343861 : Nat := 4983230072969 + 3 ^ 40 * 4343861 * 2
def baseEnd_4343861 : Nat := 2230488589320134357560453

theorem tailTrace_4343861 : CollatzResearch.WordTrace tailWord_4343861 prefixEnd_4343861 2230488589320134357560453 := by
  unfold tailWord_4343861
  simp only [CollatzResearch.WordTrace]
  refine ⟨158433626515940944240431437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105622417677293962826954291 158433626515940944240431437)
  ·
    refine ⟨59412609943477854090161789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 158433626515940944240431437 59412609943477854090161789)
    ·
      refine ⟨22279728728804195283810671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59412609943477854090161789 22279728728804195283810671)
      ·
        refine ⟨33419593093206292925716007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22279728728804195283810671 33419593093206292925716007)
        ·
          refine ⟨50129389639809439388574011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33419593093206292925716007 50129389639809439388574011)
          ·
            refine ⟨75194084459714159082861017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50129389639809439388574011 75194084459714159082861017)
            ·
              refine ⟨56395563344785619312145763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 75194084459714159082861017 56395563344785619312145763)
              ·
                refine ⟨84593345017178428968218645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56395563344785619312145763 84593345017178428968218645)
                ·
                  refine ⟨3965313047680238857885249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 84593345017178428968218645 3965313047680238857885249)
                  ·
                    refine ⟨2973984785760179143413937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3965313047680238857885249 2973984785760179143413937)
                    ·
                      refine ⟨2230488589320134357560453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2973984785760179143413937 2230488589320134357560453)
                      ·
                        rfl

theorem cell23_4343861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 1, 6, 2, 2].length) (baseStart_4343861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4343861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4343861 prefixEnd_4343861 := by exact prefixLift 4343861
  have htrace : WordTrace (prefixWord ++ tailWord_4343861) baseStart_4343861 baseEnd_4343861 := by
    simpa [prefixWord, tailWord_4343861, baseEnd_4343861] using wordTrace_append hprefix tailTrace_4343861
  have hstable : (prefixWord ++ tailWord_4343861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4343861).length < 2 ^ (prefixWord ++ tailWord_4343861).sum := by decide
  have hdescent : baseEnd_4343861 < baseStart_4343861 := by decide
  rcases family_descends (prefixWord ++ tailWord_4343861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4343865 : List Nat := [1, 2, 1, 5, 3, 1, 3, 1, 1, 3, 2]
def baseStart_4343865 : Nat := 118140960795 + 4343865 * 2 ^ 59
def prefixEnd_4343865 : Nat := 4983230072969 + 3 ^ 40 * 4343865 * 2
def baseEnd_4343865 : Nat := 2230490643242752341910435

theorem tailTrace_4343865 : CollatzResearch.WordTrace tailWord_4343865 prefixEnd_4343865 2230490643242752341910435 := by
  unfold tailWord_4343865
  simp only [CollatzResearch.WordTrace]
  refine ⟨158433772407926452923577049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105622514938617635282384699 158433772407926452923577049)
  ·
    refine ⟨118825329305944839692682787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 158433772407926452923577049 118825329305944839692682787)
    ·
      refine ⟨178237993958917259539024181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118825329305944839692682787 178237993958917259539024181)
      ·
        refine ⟨16709811933648493081783517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 178237993958917259539024181 16709811933648493081783517)
        ·
          refine ⟨6266179475118184905668819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16709811933648493081783517 6266179475118184905668819)
          ·
            refine ⟨9399269212677277358503229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6266179475118184905668819 9399269212677277358503229)
            ·
              refine ⟨3524725954753979009438711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9399269212677277358503229 3524725954753979009438711)
              ·
                refine ⟨5287088932130968514158067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3524725954753979009438711 5287088932130968514158067)
                ·
                  refine ⟨7930633398196452771237101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5287088932130968514158067 7930633398196452771237101)
                  ·
                    refine ⟨2973987524323669789213913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7930633398196452771237101 2973987524323669789213913)
                    ·
                      refine ⟨2230490643242752341910435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2973987524323669789213913 2230490643242752341910435)
                      ·
                        rfl

theorem cell23_4343865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 3, 1, 1, 3, 2].length) (baseStart_4343865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4343865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4343865 prefixEnd_4343865 := by exact prefixLift 4343865
  have htrace : WordTrace (prefixWord ++ tailWord_4343865) baseStart_4343865 baseEnd_4343865 := by
    simpa [prefixWord, tailWord_4343865, baseEnd_4343865] using wordTrace_append hprefix tailTrace_4343865
  have hstable : (prefixWord ++ tailWord_4343865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4343865).length < 2 ^ (prefixWord ++ tailWord_4343865).sum := by decide
  have hdescent : baseEnd_4343865 < baseStart_4343865 := by decide
  rcases family_descends (prefixWord ++ tailWord_4343865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4343878 : List Nat := [6, 1, 1, 1, 1, 1, 1, 2, 3, 4, 2]
def baseStart_4343878 : Nat := 118140960795 + 4343878 * 2 ^ 59
def prefixEnd_4343878 : Nat := 4983230072969 + 3 ^ 40 * 4343878 * 2
def baseEnd_4343878 : Nat := 2230497318491260791047875

theorem tailTrace_4343878 : CollatzResearch.WordTrace tailWord_4343878 prefixEnd_4343878 2230497318491260791047875 := by
  unfold tailWord_4343878
  simp only [CollatzResearch.WordTrace]
  refine ⟨4951070204902479879493759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 105622831037919570762533525 4951070204902479879493759)
  ·
    refine ⟨7426605307353719819240639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4951070204902479879493759 7426605307353719819240639)
    ·
      refine ⟨11139907961030579728860959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7426605307353719819240639 11139907961030579728860959)
      ·
        refine ⟨16709861941545869593291439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11139907961030579728860959 16709861941545869593291439)
        ·
          refine ⟨25064792912318804389937159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16709861941545869593291439 25064792912318804389937159)
          ·
            refine ⟨37597189368478206584905739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25064792912318804389937159 37597189368478206584905739)
            ·
              refine ⟨56395784052717309877358609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37597189368478206584905739 56395784052717309877358609)
              ·
                refine ⟨42296838039537982408018957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 56395784052717309877358609 42296838039537982408018957)
                ·
                  refine ⟨15861314264826743403007109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 42296838039537982408018957 15861314264826743403007109)
                  ·
                    refine ⟨2973996424655014388063833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15861314264826743403007109 2973996424655014388063833)
                    ·
                      refine ⟨2230497318491260791047875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2973996424655014388063833 2230497318491260791047875)
                      ·
                        rfl

theorem cell23_4343878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 2, 3, 4, 2].length) (baseStart_4343878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4343878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4343878 prefixEnd_4343878 := by exact prefixLift 4343878
  have htrace : WordTrace (prefixWord ++ tailWord_4343878) baseStart_4343878 baseEnd_4343878 := by
    simpa [prefixWord, tailWord_4343878, baseEnd_4343878] using wordTrace_append hprefix tailTrace_4343878
  have hstable : (prefixWord ++ tailWord_4343878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4343878).length < 2 ^ (prefixWord ++ tailWord_4343878).sum := by decide
  have hdescent : baseEnd_4343878 < baseStart_4343878 := by decide
  rcases family_descends (prefixWord ++ tailWord_4343878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4343897 : List Nat := [1, 2, 1, 2, 2, 1, 4, 2, 1, 7]
def baseStart_4343897 : Nat := 118140960795 + 4343897 * 2 ^ 59
def prefixEnd_4343897 : Nat := 4983230072969 + 3 ^ 40 * 4343897 * 2
def baseEnd_4343897 : Nat := 743502358207898738903429

theorem tailTrace_4343897 : CollatzResearch.WordTrace tailWord_4343897 prefixEnd_4343897 743502358207898738903429 := by
  unfold tailWord_4343897
  simp only [CollatzResearch.WordTrace]
  refine ⟨158434939543810522388741945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105623293029207014925827963 158434939543810522388741945)
  ·
    refine ⟨118826204657857891791556459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 158434939543810522388741945 118826204657857891791556459)
    ·
      refine ⟨178239306986786837687334689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118826204657857891791556459 178239306986786837687334689)
      ·
        refine ⟨133679480240090128265501017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 178239306986786837687334689 133679480240090128265501017)
        ·
          refine ⟨100259610180067596199125763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 133679480240090128265501017 100259610180067596199125763)
          ·
            refine ⟨150389415270101394298688645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 100259610180067596199125763 150389415270101394298688645)
            ·
              refine ⟨28198015363144011431004121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 150389415270101394298688645 28198015363144011431004121)
              ·
                refine ⟨21148511522358008573253091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28198015363144011431004121 21148511522358008573253091)
                ·
                  refine ⟨31722767283537012859879637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21148511522358008573253091 31722767283537012859879637)
                  ·
                    refine ⟨743502358207898738903429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 31722767283537012859879637 743502358207898738903429)
                    ·
                      rfl

theorem cell23_4343897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 4, 2, 1, 7].length) (baseStart_4343897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4343897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4343897 prefixEnd_4343897 := by exact prefixLift 4343897
  have htrace : WordTrace (prefixWord ++ tailWord_4343897) baseStart_4343897 baseEnd_4343897 := by
    simpa [prefixWord, tailWord_4343897, baseEnd_4343897] using wordTrace_append hprefix tailTrace_4343897
  have hstable : (prefixWord ++ tailWord_4343897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4343897).length < 2 ^ (prefixWord ++ tailWord_4343897).sum := by decide
  have hdescent : baseEnd_4343897 < baseStart_4343897 := by decide
  rcases family_descends (prefixWord ++ tailWord_4343897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4343901 : List Nat := [1, 4, 4, 1, 1, 2, 1, 2, 7]
def baseStart_4343901 : Nat := 118140960795 + 4343901 * 2 ^ 59
def prefixEnd_4343901 : Nat := 4983230072969 + 3 ^ 40 * 4343901 * 2
def baseEnd_4343901 : Nat := 247834347616257133451141

theorem tailTrace_4343901 : CollatzResearch.WordTrace tailWord_4343901 prefixEnd_4343901 247834347616257133451141 := by
  unfold tailWord_4343901
  simp only [CollatzResearch.WordTrace]
  refine ⟨158435085435796031071887557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105623390290530687381258371 158435085435796031071887557)
  ·
    refine ⟨29706578519211755825978917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 158435085435796031071887557 29706578519211755825978917)
    ·
      refine ⟨5569983472352204217371047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29706578519211755825978917 5569983472352204217371047)
      ·
        refine ⟨8354975208528306326056571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5569983472352204217371047 8354975208528306326056571)
        ·
          refine ⟨12532462812792459489084857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8354975208528306326056571 12532462812792459489084857)
          ·
            refine ⟨9399347109594344616813643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12532462812792459489084857 9399347109594344616813643)
            ·
              refine ⟨14099020664391516925220465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9399347109594344616813643 14099020664391516925220465)
              ·
                refine ⟨10574265498293637693915349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14099020664391516925220465 10574265498293637693915349)
                ·
                  refine ⟨247834347616257133451141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10574265498293637693915349 247834347616257133451141)
                  ·
                    rfl

theorem cell23_4343901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 1, 2, 7].length) (baseStart_4343901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4343901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4343901 prefixEnd_4343901 := by exact prefixLift 4343901
  have htrace : WordTrace (prefixWord ++ tailWord_4343901) baseStart_4343901 baseEnd_4343901 := by
    simpa [prefixWord, tailWord_4343901, baseEnd_4343901] using wordTrace_append hprefix tailTrace_4343901
  have hstable : (prefixWord ++ tailWord_4343901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4343901).length < 2 ^ (prefixWord ++ tailWord_4343901).sum := by decide
  have hdescent : baseEnd_4343901 < baseStart_4343901 := by decide
  rcases family_descends (prefixWord ++ tailWord_4343901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4343907 : List Nat := [1, 1, 1, 5, 1, 1, 2, 2, 1, 1, 7]
def baseStart_4343907 : Nat := 118140960795 + 4343907 * 2 ^ 59
def prefixEnd_4343907 : Nat := 4983230072969 + 3 ^ 40 * 4343907 * 2
def baseEnd_4343907 : Nat := 2230512209430241177585241

theorem tailTrace_4343907 : CollatzResearch.WordTrace tailWord_4343907 prefixEnd_4343907 2230512209430241177585241 := by
  unfold tailWord_4343907
  simp only [CollatzResearch.WordTrace]
  refine ⟨158435304273774294096605975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105623536182516196064403983 158435304273774294096605975)
  ·
    refine ⟨237652956410661441144908963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158435304273774294096605975 237652956410661441144908963)
    ·
      refine ⟨356479434615992161717363445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 237652956410661441144908963 356479434615992161717363445)
      ·
        refine ⟨33419946995249265161002823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 356479434615992161717363445 33419946995249265161002823)
        ·
          refine ⟨50129920492873897741504235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33419946995249265161002823 50129920492873897741504235)
          ·
            refine ⟨75194880739310846612256353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50129920492873897741504235 75194880739310846612256353)
            ·
              refine ⟨56396160554483134959192265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 75194880739310846612256353 56396160554483134959192265)
              ·
                refine ⟨42297120415862351219394199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 56396160554483134959192265 42297120415862351219394199)
                ·
                  refine ⟨63445680623793526829091299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 42297120415862351219394199 63445680623793526829091299)
                  ·
                    refine ⟨95168520935690290243636949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 63445680623793526829091299 95168520935690290243636949)
                    ·
                      refine ⟨2230512209430241177585241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 95168520935690290243636949 2230512209430241177585241)
                      ·
                        rfl

theorem cell23_4343907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 2, 1, 1, 7].length) (baseStart_4343907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4343907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4343907 prefixEnd_4343907 := by exact prefixLift 4343907
  have htrace : WordTrace (prefixWord ++ tailWord_4343907) baseStart_4343907 baseEnd_4343907 := by
    simpa [prefixWord, tailWord_4343907, baseEnd_4343907] using wordTrace_append hprefix tailTrace_4343907
  have hstable : (prefixWord ++ tailWord_4343907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4343907).length < 2 ^ (prefixWord ++ tailWord_4343907).sum := by decide
  have hdescent : baseEnd_4343907 < baseStart_4343907 := by decide
  rcases family_descends (prefixWord ++ tailWord_4343907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4343964 : List Nat := [2, 2, 3, 2, 1, 1, 1, 1, 2, 4, 4]
def baseStart_4343964 : Nat := 118140960795 + 4343964 * 2 ^ 59
def prefixEnd_4343964 : Nat := 4983230072969 + 3 ^ 40 * 4343964 * 2
def baseEnd_4343964 : Nat := 2230541477827547454572479

theorem tailTrace_4343964 : CollatzResearch.WordTrace tailWord_4343964 prefixEnd_4343964 2230541477827547454572479 := by
  unfold tailWord_4343964
  simp only [CollatzResearch.WordTrace]
  refine ⟨79218691617283896415715473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105624922156378528554287297 79218691617283896415715473)
  ·
    refine ⟨59414018712962922311786605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79218691617283896415715473 59414018712962922311786605)
    ·
      refine ⟨22280257017361095866919977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59414018712962922311786605 22280257017361095866919977)
      ·
        refine ⟨16710192763020821900189983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22280257017361095866919977 16710192763020821900189983)
        ·
          refine ⟨25065289144531232850284975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16710192763020821900189983 25065289144531232850284975)
          ·
            refine ⟨37597933716796849275427463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25065289144531232850284975 37597933716796849275427463)
            ·
              refine ⟨56396900575195273913141195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37597933716796849275427463 56396900575195273913141195)
              ·
                refine ⟨84595350862792910869711793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56396900575195273913141195 84595350862792910869711793)
                ·
                  refine ⟨63446513147094683152283845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 84595350862792910869711793 63446513147094683152283845)
                  ·
                    refine ⟨11896221215080253091053221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 63446513147094683152283845 11896221215080253091053221)
                    ·
                      refine ⟨2230541477827547454572479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11896221215080253091053221 2230541477827547454572479)
                      ·
                        rfl

theorem cell23_4343964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 1, 2, 4, 4].length) (baseStart_4343964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4343964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4343964 prefixEnd_4343964 := by exact prefixLift 4343964
  have htrace : WordTrace (prefixWord ++ tailWord_4343964) baseStart_4343964 baseEnd_4343964 := by
    simpa [prefixWord, tailWord_4343964, baseEnd_4343964] using wordTrace_append hprefix tailTrace_4343964
  have hstable : (prefixWord ++ tailWord_4343964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4343964).length < 2 ^ (prefixWord ++ tailWord_4343964).sum := by decide
  have hdescent : baseEnd_4343964 < baseStart_4343964 := by decide
  rcases family_descends (prefixWord ++ tailWord_4343964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4344011 : List Nat := [1, 1, 1, 1, 3, 2, 3, 2, 4, 3, 2]
def baseStart_4344011 : Nat := 118140960795 + 4344011 * 2 ^ 59
def prefixEnd_4344011 : Nat := 4983230072969 + 3 ^ 40 * 4344011 * 2
def baseEnd_4344011 : Nat := 2230565611418308770684763

theorem tailTrace_4344011 : CollatzResearch.WordTrace tailWord_4344011 prefixEnd_4344011 2230565611418308770684763 := by
  unfold tailWord_4344011
  simp only [CollatzResearch.WordTrace]
  refine ⟨158439097465397519858391887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105626064976931679905594591 158439097465397519858391887)
  ·
    refine ⟨237658646198096279787587831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158439097465397519858391887 237658646198096279787587831)
    ·
      refine ⟨356487969297144419681381747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 237658646198096279787587831 356487969297144419681381747)
      ·
        refine ⟨534731953945716629522072621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 356487969297144419681381747 534731953945716629522072621)
        ·
          refine ⟨200524482729643736070777233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 534731953945716629522072621 200524482729643736070777233)
          ·
            refine ⟨150393362047232802053082925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 200524482729643736070777233 150393362047232802053082925)
            ·
              refine ⟨56397510767712300769906097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 150393362047232802053082925 56397510767712300769906097)
              ·
                refine ⟨42298133075784225577429573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 56397510767712300769906097 42298133075784225577429573)
                ·
                  refine ⟨7930899951709542295768045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 42298133075784225577429573 7930899951709542295768045)
                  ·
                    refine ⟨2974087481891078360913017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7930899951709542295768045 2974087481891078360913017)
                    ·
                      refine ⟨2230565611418308770684763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2974087481891078360913017 2230565611418308770684763)
                      ·
                        rfl

theorem cell23_4344011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 2, 4, 3, 2].length) (baseStart_4344011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4344011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4344011 prefixEnd_4344011 := by exact prefixLift 4344011
  have htrace : WordTrace (prefixWord ++ tailWord_4344011) baseStart_4344011 baseEnd_4344011 := by
    simpa [prefixWord, tailWord_4344011, baseEnd_4344011] using wordTrace_append hprefix tailTrace_4344011
  have hstable : (prefixWord ++ tailWord_4344011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4344011).length < 2 ^ (prefixWord ++ tailWord_4344011).sum := by decide
  have hdescent : baseEnd_4344011 < baseStart_4344011 := by decide
  rcases family_descends (prefixWord ++ tailWord_4344011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4344064 : List Nat := [2, 1, 1, 2, 1, 1, 7, 8]
def baseStart_4344064 : Nat := 118140960795 + 4344064 * 2 ^ 59
def prefixEnd_4344064 : Nat := 4983230072969 + 3 ^ 40 * 4344064 * 2
def baseEnd_4344064 : Nat := 82614549107148039382297

theorem tailTrace_4344064 : CollatzResearch.WordTrace tailWord_4344064 prefixEnd_4344064 82614549107148039382297 := by
  unfold tailWord_4344064
  simp only [CollatzResearch.WordTrace]
  refine ⟨79220515267102754955035623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105627353689470339940047497 79220515267102754955035623)
  ·
    refine ⟨118830772900654132432553435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79220515267102754955035623 118830772900654132432553435)
    ·
      refine ⟨178246159350981198648830153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118830772900654132432553435 178246159350981198648830153)
      ·
        refine ⟨133684619513235898986622615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 178246159350981198648830153 133684619513235898986622615)
        ·
          refine ⟨200526929269853848479933923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 133684619513235898986622615 200526929269853848479933923)
          ·
            refine ⟨300790393904780772719900885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 200526929269853848479933923 300790393904780772719900885)
            ·
              refine ⟨7049774857143299360622677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 300790393904780772719900885 7049774857143299360622677)
              ·
                refine ⟨82614549107148039382297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7049774857143299360622677 82614549107148039382297)
                ·
                  rfl

theorem cell23_4344064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 7, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 7, 8].length) (baseStart_4344064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4344064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4344064 prefixEnd_4344064 := by exact prefixLift 4344064
  have htrace : WordTrace (prefixWord ++ tailWord_4344064) baseStart_4344064 baseEnd_4344064 := by
    simpa [prefixWord, tailWord_4344064, baseEnd_4344064] using wordTrace_append hprefix tailTrace_4344064
  have hstable : (prefixWord ++ tailWord_4344064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4344064).length < 2 ^ (prefixWord ++ tailWord_4344064).sum := by decide
  have hdescent : baseEnd_4344064 < baseStart_4344064 := by decide
  rcases family_descends (prefixWord ++ tailWord_4344064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4344068 : List Nat := [2, 3, 2, 2, 3, 1, 2, 1, 1, 6]
def baseStart_4344068 : Nat := 118140960795 + 4344068 * 2 ^ 59
def prefixEnd_4344068 : Nat := 4983230072969 + 3 ^ 40 * 4344068 * 2
def baseEnd_4344068 : Nat := 743531626605205015890667

theorem tailTrace_4344068 : CollatzResearch.WordTrace tailWord_4344068 prefixEnd_4344068 743531626605205015890667 := by
  unfold tailWord_4344068
  simp only [CollatzResearch.WordTrace]
  refine ⟨79220588213095509296608429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105627450950794012395477905 79220588213095509296608429)
  ·
    refine ⟨29707720579910815986228161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79220588213095509296608429 29707720579910815986228161)
    ·
      refine ⟨22280790434933111989671121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29707720579910815986228161 22280790434933111989671121)
      ·
        refine ⟨16710592826199833992253341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22280790434933111989671121 16710592826199833992253341)
        ·
          refine ⟨6266472309824937747095003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16710592826199833992253341 6266472309824937747095003)
          ·
            refine ⟨9399708464737406620642505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6266472309824937747095003 9399708464737406620642505)
            ·
              refine ⟨7049781348553054965481879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9399708464737406620642505 7049781348553054965481879)
              ·
                refine ⟨10574672022829582448222819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7049781348553054965481879 10574672022829582448222819)
                ·
                  refine ⟨15862008034244373672334229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10574672022829582448222819 15862008034244373672334229)
                  ·
                    refine ⟨743531626605205015890667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15862008034244373672334229 743531626605205015890667)
                    ·
                      rfl

theorem cell23_4344068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 2, 1, 1, 6].length) (baseStart_4344068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4344068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4344068 prefixEnd_4344068 := by exact prefixLift 4344068
  have htrace : WordTrace (prefixWord ++ tailWord_4344068) baseStart_4344068 baseEnd_4344068 := by
    simpa [prefixWord, tailWord_4344068, baseEnd_4344068] using wordTrace_append hprefix tailTrace_4344068
  have hstable : (prefixWord ++ tailWord_4344068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4344068).length < 2 ^ (prefixWord ++ tailWord_4344068).sum := by decide
  have hdescent : baseEnd_4344068 < baseStart_4344068 := by decide
  rcases family_descends (prefixWord ++ tailWord_4344068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4344078 : List Nat := [4, 1, 1, 2, 1, 2, 2, 4, 1, 2, 3]
def baseStart_4344078 : Nat := 118140960795 + 4344078 * 2 ^ 59
def prefixEnd_4344078 : Nat := 4983230072969 + 3 ^ 40 * 4344078 * 2
def baseEnd_4344078 : Nat := 2230600014622160008546955

theorem tailTrace_4344078 : CollatzResearch.WordTrace tailWord_4344078 prefixEnd_4344078 2230600014622160008546955 := by
  unfold tailWord_4344078
  simp only [CollatzResearch.WordTrace]
  refine ⟨19805192644519348787635111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 105627694104103193534053925 19805192644519348787635111)
  ·
    refine ⟨29707788966779023181452667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19805192644519348787635111 29707788966779023181452667)
    ·
      refine ⟨44561683450168534772179001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29707788966779023181452667 44561683450168534772179001)
      ·
        refine ⟨33421262587626401079134251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44561683450168534772179001 33421262587626401079134251)
        ·
          refine ⟨50131893881439601618701377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33421262587626401079134251 50131893881439601618701377)
          ·
            refine ⟨37598920411079701214026033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50131893881439601618701377 37598920411079701214026033)
            ·
              refine ⟨28199190308309775910519525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37598920411079701214026033 28199190308309775910519525)
              ·
                refine ⟨5287348182808082983222411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28199190308309775910519525 5287348182808082983222411)
                ·
                  refine ⟨7931022274212124474833617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5287348182808082983222411 7931022274212124474833617)
                  ·
                    refine ⟨5948266705659093356125213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7931022274212124474833617 5948266705659093356125213)
                    ·
                      refine ⟨2230600014622160008546955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5948266705659093356125213 2230600014622160008546955)
                      ·
                        rfl

theorem cell23_4344078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 2, 4, 1, 2, 3].length) (baseStart_4344078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4344078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4344078 prefixEnd_4344078 := by exact prefixLift 4344078
  have htrace : WordTrace (prefixWord ++ tailWord_4344078) baseStart_4344078 baseEnd_4344078 := by
    simpa [prefixWord, tailWord_4344078, baseEnd_4344078] using wordTrace_append hprefix tailTrace_4344078
  have hstable : (prefixWord ++ tailWord_4344078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4344078).length < 2 ^ (prefixWord ++ tailWord_4344078).sum := by decide
  have hdescent : baseEnd_4344078 < baseStart_4344078 := by decide
  rcases family_descends (prefixWord ++ tailWord_4344078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4344081 : List Nat := [1, 2, 2, 1, 1, 6, 3, 7]
def baseStart_4344081 : Nat := 118140960795 + 4344081 * 2 ^ 59
def prefixEnd_4344081 : Nat := 4983230072969 + 3 ^ 40 * 4344081 * 2
def baseEnd_4344081 : Nat := 82614872409782351733683

theorem tailTrace_4344081 : CollatzResearch.WordTrace tailWord_4344081 prefixEnd_4344081 82614872409782351733683 := by
  unfold tailWord_4344081
  simp only [CollatzResearch.WordTrace]
  refine ⟨158441650575143921813440097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105627767050095947875626731 158441650575143921813440097)
  ·
    refine ⟨118831237931357941360080073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 158441650575143921813440097 118831237931357941360080073)
    ·
      refine ⟨89123428448518456020060055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 118831237931357941360080073 89123428448518456020060055)
      ·
        refine ⟨133685142672777684030090083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89123428448518456020060055 133685142672777684030090083)
        ·
          refine ⟨200527714009166526045135125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 133685142672777684030090083 200527714009166526045135125)
          ·
            refine ⟨9399736594179680908365709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 200527714009166526045135125 9399736594179680908365709)
            ·
              refine ⟨3524901222817380340637141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9399736594179680908365709 3524901222817380340637141)
              ·
                refine ⟨82614872409782351733683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3524901222817380340637141 82614872409782351733683)
                ·
                  rfl

theorem cell23_4344081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 3, 7].length) (baseStart_4344081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4344081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4344081 prefixEnd_4344081 := by exact prefixLift 4344081
  have htrace : WordTrace (prefixWord ++ tailWord_4344081) baseStart_4344081 baseEnd_4344081 := by
    simpa [prefixWord, tailWord_4344081, baseEnd_4344081] using wordTrace_append hprefix tailTrace_4344081
  have hstable : (prefixWord ++ tailWord_4344081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4344081).length < 2 ^ (prefixWord ++ tailWord_4344081).sum := by decide
  have hdescent : baseEnd_4344081 < baseStart_4344081 := by decide
  rcases family_descends (prefixWord ++ tailWord_4344081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4344091 : List Nat := [1, 1, 1, 1, 1, 1, 8, 2, 1, 3, 3]
def baseStart_4344091 : Nat := 118140960795 + 4344091 * 2 ^ 59
def prefixEnd_4344091 : Nat := 4983230072969 + 3 ^ 40 * 4344091 * 2
def baseEnd_4344091 : Nat := 2230606689870668457684395

theorem tailTrace_4344091 : CollatzResearch.WordTrace tailWord_4344091 prefixEnd_4344091 2230606689870668457684395 := by
  unfold tailWord_4344091
  simp only [CollatzResearch.WordTrace]
  refine ⟨158442015305107693521304127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105628010203405129014202751 158442015305107693521304127)
  ·
    refine ⟨237663022957661540281956191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158442015305107693521304127 237663022957661540281956191)
    ·
      refine ⟨356494534436492310422934287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 237663022957661540281956191 356494534436492310422934287)
      ·
        refine ⟨534741801654738465634401431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 356494534436492310422934287 534741801654738465634401431)
        ·
          refine ⟨802112702482107698451602147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 534741801654738465634401431 802112702482107698451602147)
          ·
            refine ⟨1203169053723161547677403221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 802112702482107698451602147 1203169053723161547677403221)
            ·
              refine ⟨14099637348318299386844569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1203169053723161547677403221 14099637348318299386844569)
              ·
                refine ⟨10574728011238724540133427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14099637348318299386844569 10574728011238724540133427)
                ·
                  refine ⟨15862092016858086810200141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10574728011238724540133427 15862092016858086810200141)
                  ·
                    refine ⟨5948284506321782553825053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15862092016858086810200141 5948284506321782553825053)
                    ·
                      refine ⟨2230606689870668457684395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5948284506321782553825053 2230606689870668457684395)
                      ·
                        rfl

theorem cell23_4344091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 8, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 8, 2, 1, 3, 3].length) (baseStart_4344091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4344091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4344091 prefixEnd_4344091 := by exact prefixLift 4344091
  have htrace : WordTrace (prefixWord ++ tailWord_4344091) baseStart_4344091 baseEnd_4344091 := by
    simpa [prefixWord, tailWord_4344091, baseEnd_4344091] using wordTrace_append hprefix tailTrace_4344091
  have hstable : (prefixWord ++ tailWord_4344091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4344091).length < 2 ^ (prefixWord ++ tailWord_4344091).sum := by decide
  have hdescent : baseEnd_4344091 < baseStart_4344091 := by decide
  rcases family_descends (prefixWord ++ tailWord_4344091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4344095 : List Nat := [1, 1, 2, 4, 3, 1, 4, 1, 1, 2, 3]
def baseStart_4344095 : Nat := 118140960795 + 4344095 * 2 ^ 59
def prefixEnd_4344095 : Nat := 4983230072969 + 3 ^ 40 * 4344095 * 2
def baseEnd_4344095 : Nat := 2230608743793286442034377

theorem tailTrace_4344095 : CollatzResearch.WordTrace tailWord_4344095 prefixEnd_4344095 2230608743793286442034377 := by
  unfold tailWord_4344095
  simp only [CollatzResearch.WordTrace]
  refine ⟨158442161197093202204449739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105628107464728801469633159 158442161197093202204449739)
  ·
    refine ⟨237663241795639803306674609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158442161197093202204449739 237663241795639803306674609)
    ·
      refine ⟨178247431346729852480005957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 237663241795639803306674609 178247431346729852480005957)
      ·
        refine ⟨33421393377511847340001117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 178247431346729852480005957 33421393377511847340001117)
        ·
          refine ⟨12533022516566942752500419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33421393377511847340001117 12533022516566942752500419)
          ·
            refine ⟨18799533774850414128750629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12533022516566942752500419 18799533774850414128750629)
            ·
              refine ⟨3524912582784452649140743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18799533774850414128750629 3524912582784452649140743)
              ·
                refine ⟨5287368874176678973711115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3524912582784452649140743 5287368874176678973711115)
                ·
                  refine ⟨7931053311265018460566673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5287368874176678973711115 7931053311265018460566673)
                  ·
                    refine ⟨5948289983448763845425005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7931053311265018460566673 5948289983448763845425005)
                    ·
                      refine ⟨2230608743793286442034377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5948289983448763845425005 2230608743793286442034377)
                      ·
                        rfl

theorem cell23_4344095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 4, 1, 1, 2, 3].length) (baseStart_4344095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4344095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4344095 prefixEnd_4344095 := by exact prefixLift 4344095
  have htrace : WordTrace (prefixWord ++ tailWord_4344095) baseStart_4344095 baseEnd_4344095 := by
    simpa [prefixWord, tailWord_4344095, baseEnd_4344095] using wordTrace_append hprefix tailTrace_4344095
  have hstable : (prefixWord ++ tailWord_4344095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4344095).length < 2 ^ (prefixWord ++ tailWord_4344095).sum := by decide
  have hdescent : baseEnd_4344095 < baseStart_4344095 := by decide
  rcases family_descends (prefixWord ++ tailWord_4344095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4344109 : List Nat := [1, 5, 3, 1, 2, 1, 2, 1, 3, 2, 2]
def baseStart_4344109 : Nat := 118140960795 + 4344109 * 2 ^ 59
def prefixEnd_4344109 : Nat := 4983230072969 + 3 ^ 40 * 4344109 * 2
def baseEnd_4344109 : Nat := 2230615932522449387259313

theorem tailTrace_4344109 : CollatzResearch.WordTrace tailWord_4344109 prefixEnd_4344109 2230615932522449387259313 := by
  unfold tailWord_4344109
  simp only [CollatzResearch.WordTrace]
  refine ⟨158442671819042482595459381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105628447879361655063639587 158442671819042482595459381)
  ·
    refine ⟨14854000483035232743324317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 158442671819042482595459381 14854000483035232743324317)
    ·
      refine ⟨5570250181138212278746619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14854000483035232743324317 5570250181138212278746619)
      ·
        refine ⟨8355375271707318418119929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5570250181138212278746619 8355375271707318418119929)
        ·
          refine ⟨6266531453780488813589947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8355375271707318418119929 6266531453780488813589947)
          ·
            refine ⟨9399797180670733220384921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6266531453780488813589947 9399797180670733220384921)
            ·
              refine ⟨7049847885503049915288691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9399797180670733220384921 7049847885503049915288691)
              ·
                refine ⟨10574771828254574872933037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7049847885503049915288691 10574771828254574872933037)
                ·
                  refine ⟨3965539435595465577349889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10574771828254574872933037 3965539435595465577349889)
                  ·
                    refine ⟨2974154576696599183012417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3965539435595465577349889 2974154576696599183012417)
                    ·
                      refine ⟨2230615932522449387259313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2974154576696599183012417 2230615932522449387259313)
                      ·
                        rfl

theorem cell23_4344109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 2, 1, 3, 2, 2].length) (baseStart_4344109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4344109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4344109 prefixEnd_4344109 := by exact prefixLift 4344109
  have htrace : WordTrace (prefixWord ++ tailWord_4344109) baseStart_4344109 baseEnd_4344109 := by
    simpa [prefixWord, tailWord_4344109, baseEnd_4344109] using wordTrace_append hprefix tailTrace_4344109
  have hstable : (prefixWord ++ tailWord_4344109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4344109).length < 2 ^ (prefixWord ++ tailWord_4344109).sum := by decide
  have hdescent : baseEnd_4344109 < baseStart_4344109 := by decide
  rcases family_descends (prefixWord ++ tailWord_4344109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4344132 : List Nat := [2, 3, 4, 1, 3, 1, 2, 7]
def baseStart_4344132 : Nat := 118140960795 + 4344132 * 2 ^ 59
def prefixEnd_4344132 : Nat := 4983230072969 + 3 ^ 40 * 4344132 * 2
def baseEnd_4344132 : Nat := 82615842317685288787841

theorem tailTrace_4344132 : CollatzResearch.WordTrace tailWord_4344132 prefixEnd_4344132 82615842317685288787841 := by
  unfold tailWord_4344132
  simp only [CollatzResearch.WordTrace]
  refine ⟨79221755348979578761773325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105629007131972771682364433 79221755348979578761773325)
  ·
    refine ⟨29708158255867342035664997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79221755348979578761773325 29708158255867342035664997)
    ·
      refine ⟨5570279672975126631687187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29708158255867342035664997 5570279672975126631687187)
      ·
        refine ⟨8355419509462689947530781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5570279672975126631687187 8355419509462689947530781)
        ·
          refine ⟨3133282316048508730324043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8355419509462689947530781 3133282316048508730324043)
          ·
            refine ⟨4699923474072763095486065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3133282316048508730324043 4699923474072763095486065)
            ·
              refine ⟨3524942605554572321614549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4699923474072763095486065 3524942605554572321614549)
              ·
                refine ⟨82615842317685288787841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3524942605554572321614549 82615842317685288787841)
                ·
                  rfl

theorem cell23_4344132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 3, 1, 2, 7].length) (baseStart_4344132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4344132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4344132 prefixEnd_4344132 := by exact prefixLift 4344132
  have htrace : WordTrace (prefixWord ++ tailWord_4344132) baseStart_4344132 baseEnd_4344132 := by
    simpa [prefixWord, tailWord_4344132, baseEnd_4344132] using wordTrace_append hprefix tailTrace_4344132
  have hstable : (prefixWord ++ tailWord_4344132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4344132).length < 2 ^ (prefixWord ++ tailWord_4344132).sum := by decide
  have hdescent : baseEnd_4344132 < baseStart_4344132 := by decide
  rcases family_descends (prefixWord ++ tailWord_4344132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4344135 : List Nat := [1, 1, 4, 1, 2, 2, 4, 2, 1, 3, 2]
def baseStart_4344135 : Nat := 118140960795 + 4344135 * 2 ^ 59
def prefixEnd_4344135 : Nat := 4983230072969 + 3 ^ 40 * 4344135 * 2
def baseEnd_4344135 : Nat := 2230629283019466285534193

theorem tailTrace_4344135 : CollatzResearch.WordTrace tailWord_4344135 prefixEnd_4344135 2230629283019466285534193 := by
  unfold tailWord_4344135
  simp only [CollatzResearch.WordTrace]
  refine ⟨158443620116948289035905859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105629080077965526023937239 158443620116948289035905859)
  ·
    refine ⟨237665430175422433553858789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158443620116948289035905859 237665430175422433553858789)
    ·
      refine ⟨44562268157891706291348523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 237665430175422433553858789 44562268157891706291348523)
      ·
        refine ⟨66843402236837559437022785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44562268157891706291348523 66843402236837559437022785)
        ·
          refine ⟨50132551677628169577767089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66843402236837559437022785 50132551677628169577767089)
          ·
            refine ⟨37599413758221127183325317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50132551677628169577767089 37599413758221127183325317)
            ·
              refine ⟨7049890079666461346873497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 37599413758221127183325317 7049890079666461346873497)
              ·
                refine ⟨5287417559749846010155123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7049890079666461346873497 5287417559749846010155123)
                ·
                  refine ⟨7931126339624769015232685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5287417559749846010155123 7931126339624769015232685)
                  ·
                    refine ⟨2974172377359288380712257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7931126339624769015232685 2974172377359288380712257)
                    ·
                      refine ⟨2230629283019466285534193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2974172377359288380712257 2230629283019466285534193)
                      ·
                        rfl

theorem cell23_4344135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 4, 2, 1, 3, 2].length) (baseStart_4344135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4344135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4344135 prefixEnd_4344135 := by exact prefixLift 4344135
  have htrace : WordTrace (prefixWord ++ tailWord_4344135) baseStart_4344135 baseEnd_4344135 := by
    simpa [prefixWord, tailWord_4344135, baseEnd_4344135] using wordTrace_append hprefix tailTrace_4344135
  have hstable : (prefixWord ++ tailWord_4344135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4344135).length < 2 ^ (prefixWord ++ tailWord_4344135).sum := by decide
  have hdescent : baseEnd_4344135 < baseStart_4344135 := by decide
  rcases family_descends (prefixWord ++ tailWord_4344135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4344151 : List Nat := [1, 1, 3, 2, 3, 1, 3, 1, 2, 1, 5]
def baseStart_4344151 : Nat := 118140960795 + 4344151 * 2 ^ 59
def prefixEnd_4344151 : Nat := 4983230072969 + 3 ^ 40 * 4344151 * 2
def baseEnd_4344151 : Nat := 2230637498709938222934119

theorem tailTrace_4344151 : CollatzResearch.WordTrace tailWord_4344151 prefixEnd_4344151 2230637498709938222934119 := by
  unfold tailWord_4344151
  simp only [CollatzResearch.WordTrace]
  refine ⟨158444203684890323768488307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105629469123260215845658871 158444203684890323768488307)
  ·
    refine ⟨237666305527335485652732461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158444203684890323768488307 237666305527335485652732461)
    ·
      refine ⟨89124864572750807119774673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 237666305527335485652732461 89124864572750807119774673)
      ·
        refine ⟨66843648429563105339831005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89124864572750807119774673 66843648429563105339831005)
        ·
          refine ⟨25066368161086164502436627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 66843648429563105339831005 25066368161086164502436627)
          ·
            refine ⟨37599552241629246753654941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25066368161086164502436627 37599552241629246753654941)
            ·
              refine ⟨14099832090610967532620603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37599552241629246753654941 14099832090610967532620603)
              ·
                refine ⟨21149748135916451298930905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14099832090610967532620603 21149748135916451298930905)
                ·
                  refine ⟨15862311101937338474198179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21149748135916451298930905 15862311101937338474198179)
                  ·
                    refine ⟨23793466652906007711297269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15862311101937338474198179 23793466652906007711297269)
                    ·
                      refine ⟨2230637498709938222934119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23793466652906007711297269 2230637498709938222934119)
                      ·
                        rfl

theorem cell23_4344151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 3, 1, 2, 1, 5].length) (baseStart_4344151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4344151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4344151 prefixEnd_4344151 := by exact prefixLift 4344151
  have htrace : WordTrace (prefixWord ++ tailWord_4344151) baseStart_4344151 baseEnd_4344151 := by
    simpa [prefixWord, tailWord_4344151, baseEnd_4344151] using wordTrace_append hprefix tailTrace_4344151
  have hstable : (prefixWord ++ tailWord_4344151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4344151).length < 2 ^ (prefixWord ++ tailWord_4344151).sum := by decide
  have hdescent : baseEnd_4344151 < baseStart_4344151 := by decide
  rcases family_descends (prefixWord ++ tailWord_4344151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4344165 : List Nat := [1, 3, 1, 3, 1, 3, 2, 1, 4, 2, 2]
def baseStart_4344165 : Nat := 118140960795 + 4344165 * 2 ^ 59
def prefixEnd_4344165 : Nat := 4983230072969 + 3 ^ 40 * 4344165 * 2
def baseEnd_4344165 : Nat := 2230644687439101168159055

theorem tailTrace_4344165 : CollatzResearch.WordTrace tailWord_4344165 prefixEnd_4344165 2230644687439101168159055 := by
  unfold tailWord_4344165
  simp only [CollatzResearch.WordTrace]
  refine ⟨158444714306839604159497949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105629809537893069439665299 158444714306839604159497949)
  ·
    refine ⟨59416767865064851559811731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 158444714306839604159497949 59416767865064851559811731)
    ·
      refine ⟨89125151797597277339717597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59416767865064851559811731 89125151797597277339717597)
      ·
        refine ⟨33421931924098979002394099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 89125151797597277339717597 33421931924098979002394099)
        ·
          refine ⟨50132897886148468503591149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33421931924098979002394099 50132897886148468503591149)
          ·
            refine ⟨18799836707305675688846681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50132897886148468503591149 18799836707305675688846681)
            ·
              refine ⟨14099877530479256766635011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18799836707305675688846681 14099877530479256766635011)
              ·
                refine ⟨21149816295718885149952517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14099877530479256766635011 21149816295718885149952517)
                ·
                  refine ⟨3965590555447290965616097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21149816295718885149952517 3965590555447290965616097)
                  ·
                    refine ⟨2974192916585468224212073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3965590555447290965616097 2974192916585468224212073)
                    ·
                      refine ⟨2230644687439101168159055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2974192916585468224212073 2230644687439101168159055)
                      ·
                        rfl

theorem cell23_4344165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 2, 1, 4, 2, 2].length) (baseStart_4344165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4344165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4344165 prefixEnd_4344165 := by exact prefixLift 4344165
  have htrace : WordTrace (prefixWord ++ tailWord_4344165) baseStart_4344165 baseEnd_4344165 := by
    simpa [prefixWord, tailWord_4344165, baseEnd_4344165] using wordTrace_append hprefix tailTrace_4344165
  have hstable : (prefixWord ++ tailWord_4344165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4344165).length < 2 ^ (prefixWord ++ tailWord_4344165).sum := by decide
  have hdescent : baseEnd_4344165 < baseStart_4344165 := by decide
  rcases family_descends (prefixWord ++ tailWord_4344165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4344218 : List Nat := [3, 1, 1, 4, 1, 2, 2, 2, 2, 5]
def baseStart_4344218 : Nat := 118140960795 + 4344218 * 2 ^ 59
def prefixEnd_4344218 : Nat := 4983230072969 + 3 ^ 40 * 4344218 * 2
def baseEnd_4344218 : Nat := 743557300637929820265437

theorem tailTrace_4344218 : CollatzResearch.WordTrace tailWord_4344218 prefixEnd_4344218 743557300637929820265437 := by
  unfold tailWord_4344218
  simp only [CollatzResearch.WordTrace]
  refine ⟨39611661843911898552794327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105631098250431729474118205 39611661843911898552794327)
  ·
    refine ⟨59417492765867847829191491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39611661843911898552794327 59417492765867847829191491)
    ·
      refine ⟨89126239148801771743787237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59417492765867847829191491 89126239148801771743787237)
      ·
        refine ⟨16711169840400332201960107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 89126239148801771743787237 16711169840400332201960107)
        ·
          refine ⟨25066754760600498302940161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16711169840400332201960107 25066754760600498302940161)
          ·
            refine ⟨18800066070450373727205121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25066754760600498302940161 18800066070450373727205121)
            ·
              refine ⟨14100049552837780295403841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18800066070450373727205121 14100049552837780295403841)
              ·
                refine ⟨10575037164628335221552881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14100049552837780295403841 10575037164628335221552881)
                ·
                  refine ⟨7931277873471251416164661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10575037164628335221552881 7931277873471251416164661)
                  ·
                    refine ⟨743557300637929820265437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7931277873471251416164661 743557300637929820265437)
                    ·
                      rfl

theorem cell23_4344218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 2, 2, 2, 5].length) (baseStart_4344218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4344218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4344218 prefixEnd_4344218 := by exact prefixLift 4344218
  have htrace : WordTrace (prefixWord ++ tailWord_4344218) baseStart_4344218 baseEnd_4344218 := by
    simpa [prefixWord, tailWord_4344218, baseEnd_4344218] using wordTrace_append hprefix tailTrace_4344218
  have hstable : (prefixWord ++ tailWord_4344218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4344218).length < 2 ^ (prefixWord ++ tailWord_4344218).sum := by decide
  have hdescent : baseEnd_4344218 < baseStart_4344218 := by decide
  rcases family_descends (prefixWord ++ tailWord_4344218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4344222 : List Nat := [4, 3, 1, 2, 1, 2, 1, 4, 5]
def baseStart_4344222 : Nat := 118140960795 + 4344222 * 2 ^ 59
def prefixEnd_4344222 : Nat := 4983230072969 + 3 ^ 40 * 4344222 * 2
def baseEnd_4344222 : Nat := 247852661759600827238477

theorem tailTrace_4344222 : CollatzResearch.WordTrace tailWord_4344222 prefixEnd_4344222 247852661759600827238477 := by
  unfold tailWord_4344222
  simp only [CollatzResearch.WordTrace]
  refine ⟨19805849158454137861790365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 105631195511755401929548613 19805849158454137861790365)
  ·
    refine ⟨7427193434420301698171387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19805849158454137861790365 7427193434420301698171387)
    ·
      refine ⟨11140790151630452547257081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7427193434420301698171387 11140790151630452547257081)
      ·
        refine ⟨8355592613722839410442811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11140790151630452547257081 8355592613722839410442811)
        ·
          refine ⟨12533388920584259115664217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8355592613722839410442811 12533388920584259115664217)
          ·
            refine ⟨9400041690438194336748163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12533388920584259115664217 9400041690438194336748163)
            ·
              refine ⟨14100062535657291505122245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9400041690438194336748163 14100062535657291505122245)
              ·
                refine ⟨2643761725435742157210421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14100062535657291505122245 2643761725435742157210421)
                ·
                  refine ⟨247852661759600827238477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2643761725435742157210421 247852661759600827238477)
                  ·
                    rfl

theorem cell23_4344222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 1, 4, 5].length) (baseStart_4344222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4344222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4344222 prefixEnd_4344222 := by exact prefixLift 4344222
  have htrace : WordTrace (prefixWord ++ tailWord_4344222) baseStart_4344222 baseEnd_4344222 := by
    simpa [prefixWord, tailWord_4344222, baseEnd_4344222] using wordTrace_append hprefix tailTrace_4344222
  have hstable : (prefixWord ++ tailWord_4344222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4344222).length < 2 ^ (prefixWord ++ tailWord_4344222).sum := by decide
  have hdescent : baseEnd_4344222 < baseStart_4344222 := by decide
  rcases family_descends (prefixWord ++ tailWord_4344222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4344265 : List Nat := [1, 2, 1, 1, 2, 1, 5, 5, 1, 4]
def baseStart_4344265 : Nat := 118140960795 + 4344265 * 2 ^ 59
def prefixEnd_4344265 : Nat := 4983230072969 + 3 ^ 40 * 4344265 * 2
def baseEnd_4344265 : Nat := 743565345168183592302865

theorem tailTrace_4344265 : CollatzResearch.WordTrace tailWord_4344265 prefixEnd_4344265 743565345168183592302865 := by
  unfold tailWord_4344265
  simp only [CollatzResearch.WordTrace]
  refine ⟨158448361606477321238138249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105632241070984880825425499 158448361606477321238138249)
  ·
    refine ⟨118836271204857990928603687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 158448361606477321238138249 118836271204857990928603687)
    ·
      refine ⟨178254406807286986392905531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118836271204857990928603687 178254406807286986392905531)
      ·
        refine ⟨267381610210930479589358297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 178254406807286986392905531 267381610210930479589358297)
        ·
          refine ⟨200536207658197859692018723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 267381610210930479589358297 200536207658197859692018723)
          ·
            refine ⟨300804311487296789538028085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 200536207658197859692018723 300804311487296789538028085)
            ·
              refine ⟨28200404201934074019190133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 300804311487296789538028085 28200404201934074019190133)
              ·
                refine ⟨2643787893931319439299075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 28200404201934074019190133 2643787893931319439299075)
                ·
                  refine ⟨3965681840896979158948613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2643787893931319439299075 3965681840896979158948613)
                  ·
                    refine ⟨743565345168183592302865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3965681840896979158948613 743565345168183592302865)
                    ·
                      rfl

theorem cell23_4344265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 5, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 5, 5, 1, 4].length) (baseStart_4344265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4344265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4344265 prefixEnd_4344265 := by exact prefixLift 4344265
  have htrace : WordTrace (prefixWord ++ tailWord_4344265) baseStart_4344265 baseEnd_4344265 := by
    simpa [prefixWord, tailWord_4344265, baseEnd_4344265] using wordTrace_append hprefix tailTrace_4344265
  have hstable : (prefixWord ++ tailWord_4344265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4344265).length < 2 ^ (prefixWord ++ tailWord_4344265).sum := by decide
  have hdescent : baseEnd_4344265 < baseStart_4344265 := by decide
  rcases family_descends (prefixWord ++ tailWord_4344265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4344281 : List Nat := [1, 2, 1, 2, 4, 1, 1, 1, 1, 1, 8]
def baseStart_4344281 : Nat := 118140960795 + 4344281 * 2 ^ 59
def prefixEnd_4344281 : Nat := 4983230072969 + 3 ^ 40 * 4344281 * 2
def baseEnd_4344281 : Nat := 2230704251195022714308521

theorem tailTrace_4344281 : CollatzResearch.WordTrace tailWord_4344281 prefixEnd_4344281 2230704251195022714308521 := by
  unfold tailWord_4344281
  simp only [CollatzResearch.WordTrace]
  refine ⟨158448945174419355970720697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105632630116279570647147131 158448945174419355970720697)
  ·
    refine ⟨118836708880814516978040523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 158448945174419355970720697 118836708880814516978040523)
    ·
      refine ⟨178255063321221775467060785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118836708880814516978040523 178255063321221775467060785)
      ·
        refine ⟨133691297490916331600295589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 178255063321221775467060785 133691297490916331600295589)
        ·
          refine ⟨25067118279546812175055423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 133691297490916331600295589 25067118279546812175055423)
          ·
            refine ⟨37600677419320218262583135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25067118279546812175055423 37600677419320218262583135)
            ·
              refine ⟨56401016128980327393874703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37600677419320218262583135 56401016128980327393874703)
              ·
                refine ⟨84601524193470491090812055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56401016128980327393874703 84601524193470491090812055)
                ·
                  refine ⟨126902286290205736636218083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 84601524193470491090812055 126902286290205736636218083)
                  ·
                    refine ⟨190353429435308604954327125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 126902286290205736636218083 190353429435308604954327125)
                    ·
                      refine ⟨2230704251195022714308521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 190353429435308604954327125 2230704251195022714308521)
                      ·
                        rfl

theorem cell23_4344281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 1, 1, 1, 8].length) (baseStart_4344281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4344281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4344281 prefixEnd_4344281 := by exact prefixLift 4344281
  have htrace : WordTrace (prefixWord ++ tailWord_4344281) baseStart_4344281 baseEnd_4344281 := by
    simpa [prefixWord, tailWord_4344281, baseEnd_4344281] using wordTrace_append hprefix tailTrace_4344281
  have hstable : (prefixWord ++ tailWord_4344281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4344281).length < 2 ^ (prefixWord ++ tailWord_4344281).sum := by decide
  have hdescent : baseEnd_4344281 < baseStart_4344281 := by decide
  rcases family_descends (prefixWord ++ tailWord_4344281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4344295 : List Nat := [1, 1, 5, 2, 1, 1, 5, 1, 6]
def baseStart_4344295 : Nat := 118140960795 + 4344295 * 2 ^ 59
def prefixEnd_4344295 : Nat := 4983230072969 + 3 ^ 40 * 4344295 * 2
def baseEnd_4344295 : Nat := 247856826658242851059273

theorem tailTrace_4344295 : CollatzResearch.WordTrace tailWord_4344295 prefixEnd_4344295 247856826658242851059273 := by
  unfold tailWord_4344295
  simp only [CollatzResearch.WordTrace]
  refine ⟨158449455796368636361730339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105632970530912424241153559 158449455796368636361730339)
  ·
    refine ⟨237674183694552954542595509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158449455796368636361730339 237674183694552954542595509)
    ·
      refine ⟨22281954721364339488368329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 237674183694552954542595509 22281954721364339488368329)
      ·
        refine ⟨16711466041023254616276247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22281954721364339488368329 16711466041023254616276247)
        ·
          refine ⟨25067199061534881924414371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16711466041023254616276247 25067199061534881924414371)
          ·
            refine ⟨37600798592302322886621557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25067199061534881924414371 37600798592302322886621557)
            ·
              refine ⟨3525074868028342770620771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 37600798592302322886621557 3525074868028342770620771)
              ·
                refine ⟨5287612302042514155931157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3525074868028342770620771 5287612302042514155931157)
                ·
                  refine ⟨247856826658242851059273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5287612302042514155931157 247856826658242851059273)
                  ·
                    rfl

theorem cell23_4344295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 5, 1, 6].length) (baseStart_4344295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4344295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4344295 prefixEnd_4344295 := by exact prefixLift 4344295
  have htrace : WordTrace (prefixWord ++ tailWord_4344295) baseStart_4344295 baseEnd_4344295 := by
    simpa [prefixWord, tailWord_4344295, baseEnd_4344295] using wordTrace_append hprefix tailTrace_4344295
  have hstable : (prefixWord ++ tailWord_4344295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4344295).length < 2 ^ (prefixWord ++ tailWord_4344295).sum := by decide
  have hdescent : baseEnd_4344295 < baseStart_4344295 := by decide
  rcases family_descends (prefixWord ++ tailWord_4344295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4344305 : List Nat := [1, 2, 2, 2, 3, 1, 1, 4, 3, 1, 3]
def baseStart_4344305 : Nat := 118140960795 + 4344305 * 2 ^ 59
def prefixEnd_4344305 : Nat := 4983230072969 + 3 ^ 40 * 4344305 * 2
def baseEnd_4344305 : Nat := 2230716574730730620408411

theorem tailTrace_4344305 : CollatzResearch.WordTrace tailWord_4344305 prefixEnd_4344305 2230716574730730620408411 := by
  unfold tailWord_4344305
  simp only [CollatzResearch.WordTrace]
  refine ⟨158449820526332408069594369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105633213684221605379729579 158449820526332408069594369)
  ·
    refine ⟨118837365394749306052195777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 158449820526332408069594369 118837365394749306052195777)
    ·
      refine ⟨89128024046061979539146833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 118837365394749306052195777 89128024046061979539146833)
      ·
        refine ⟨66846018034546484654360125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89128024046061979539146833 66846018034546484654360125)
        ·
          refine ⟨25067256762954931745385047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 66846018034546484654360125 25067256762954931745385047)
          ·
            refine ⟨37600885144432397618077571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25067256762954931745385047 37600885144432397618077571)
            ·
              refine ⟨56401327716648596427116357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37600885144432397618077571 56401327716648596427116357)
              ·
                refine ⟨10575248946871611830084317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 56401327716648596427116357 10575248946871611830084317)
                ·
                  refine ⟨3965718355076854436281619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10575248946871611830084317 3965718355076854436281619)
                  ·
                    refine ⟨5948577532615281654422429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3965718355076854436281619 5948577532615281654422429)
                    ·
                      refine ⟨2230716574730730620408411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5948577532615281654422429 2230716574730730620408411)
                      ·
                        rfl

theorem cell23_4344305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 4, 3, 1, 3].length) (baseStart_4344305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4344305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4344305 prefixEnd_4344305 := by exact prefixLift 4344305
  have htrace : WordTrace (prefixWord ++ tailWord_4344305) baseStart_4344305 baseEnd_4344305 := by
    simpa [prefixWord, tailWord_4344305, baseEnd_4344305] using wordTrace_append hprefix tailTrace_4344305
  have hstable : (prefixWord ++ tailWord_4344305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4344305).length < 2 ^ (prefixWord ++ tailWord_4344305).sum := by decide
  have hdescent : baseEnd_4344305 < baseStart_4344305 := by decide
  rcases family_descends (prefixWord ++ tailWord_4344305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4344326 : List Nat := [6, 2, 1, 1, 1, 2, 1, 2, 2, 2, 3]
def baseStart_4344326 : Nat := 118140960795 + 4344326 * 2 ^ 59
def prefixEnd_4344326 : Nat := 4983230072969 + 3 ^ 40 * 4344326 * 2
def baseEnd_4344326 : Nat := 2230727357824475038245815

theorem tailTrace_4344326 : CollatzResearch.WordTrace tailWord_4344326 prefixEnd_4344326 2230727357824475038245815 := by
  unfold tailWord_4344326
  simp only [CollatzResearch.WordTrace]
  refine ⟨4951580826851760270503401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 105633724306170885770739221 4951580826851760270503401)
  ·
    refine ⟨3713685620138820202877551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4951580826851760270503401 3713685620138820202877551)
    ·
      refine ⟨5570528430208230304316327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3713685620138820202877551 5570528430208230304316327)
      ·
        refine ⟨8355792645312345456474491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5570528430208230304316327 8355792645312345456474491)
        ·
          refine ⟨12533688967968518184711737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8355792645312345456474491 12533688967968518184711737)
          ·
            refine ⟨9400266725976388638533803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12533688967968518184711737 9400266725976388638533803)
            ·
              refine ⟨14100400088964582957800705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9400266725976388638533803 14100400088964582957800705)
              ·
                refine ⟨10575300066723437218350529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14100400088964582957800705 10575300066723437218350529)
                ·
                  refine ⟨7931475050042577913762897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10575300066723437218350529 7931475050042577913762897)
                  ·
                    refine ⟨5948606287531933435322173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7931475050042577913762897 5948606287531933435322173)
                    ·
                      refine ⟨2230727357824475038245815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5948606287531933435322173 2230727357824475038245815)
                      ·
                        rfl

theorem cell23_4344326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 1, 2, 2, 2, 3].length) (baseStart_4344326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4344326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4344326 prefixEnd_4344326 := by exact prefixLift 4344326
  have htrace : WordTrace (prefixWord ++ tailWord_4344326) baseStart_4344326 baseEnd_4344326 := by
    simpa [prefixWord, tailWord_4344326, baseEnd_4344326] using wordTrace_append hprefix tailTrace_4344326
  have hstable : (prefixWord ++ tailWord_4344326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4344326).length < 2 ^ (prefixWord ++ tailWord_4344326).sum := by decide
  have hdescent : baseEnd_4344326 < baseStart_4344326 := by decide
  rcases family_descends (prefixWord ++ tailWord_4344326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4344328 : List Nat := [2, 1, 3, 2, 1, 1, 1, 2, 5, 1, 4]
def baseStart_4344328 : Nat := 118140960795 + 4344328 * 2 ^ 59
def prefixEnd_4344328 : Nat := 4983230072969 + 3 ^ 40 * 4344328 * 2
def baseEnd_4344328 : Nat := 2230728384785784030420805

theorem tailTrace_4344328 : CollatzResearch.WordTrace tailWord_4344328 prefixEnd_4344328 2230728384785784030420805 := by
  unfold tailWord_4344328
  simp only [CollatzResearch.WordTrace]
  refine ⟨79225329702624541498840819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105633772936832721998454425 79225329702624541498840819)
  ·
    refine ⟨118837994553936812248261229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79225329702624541498840819 118837994553936812248261229)
    ·
      refine ⟨44564247957726304593097961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 118837994553936812248261229 44564247957726304593097961)
      ·
        refine ⟨33423185968294728444823471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44564247957726304593097961 33423185968294728444823471)
        ·
          refine ⟨50134778952442092667235207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33423185968294728444823471 50134778952442092667235207)
          ·
            refine ⟨75202168428663139000852811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50134778952442092667235207 75202168428663139000852811)
            ·
              refine ⟨112803252642994708501279217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75202168428663139000852811 112803252642994708501279217)
              ·
                refine ⟨84602439482246031375959413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 112803252642994708501279217 84602439482246031375959413)
                ·
                  refine ⟨7931478701460565441496195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 84602439482246031375959413 7931478701460565441496195)
                  ·
                    refine ⟨11897218052190848162244293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7931478701460565441496195 11897218052190848162244293)
                    ·
                      refine ⟨2230728384785784030420805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11897218052190848162244293 2230728384785784030420805)
                      ·
                        rfl

theorem cell23_4344328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 2, 5, 1, 4].length) (baseStart_4344328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4344328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4344328 prefixEnd_4344328 := by exact prefixLift 4344328
  have htrace : WordTrace (prefixWord ++ tailWord_4344328) baseStart_4344328 baseEnd_4344328 := by
    simpa [prefixWord, tailWord_4344328, baseEnd_4344328] using wordTrace_append hprefix tailTrace_4344328
  have hstable : (prefixWord ++ tailWord_4344328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4344328).length < 2 ^ (prefixWord ++ tailWord_4344328).sum := by decide
  have hdescent : baseEnd_4344328 < baseStart_4344328 := by decide
  rcases family_descends (prefixWord ++ tailWord_4344328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4344332 : List Nat := [2, 2, 1, 2, 4, 2, 1, 2, 2, 3, 2]
def baseStart_4344332 : Nat := 118140960795 + 4344332 * 2 ^ 59
def prefixEnd_4344332 : Nat := 4983230072969 + 3 ^ 40 * 4344332 * 2
def baseEnd_4344332 : Nat := 2230730438708402014770787

theorem tailTrace_4344332 : CollatzResearch.WordTrace tailWord_4344332 prefixEnd_4344332 2230730438708402014770787 := by
  unfold tailWord_4344332
  simp only [CollatzResearch.WordTrace]
  refine ⟨79225402648617295840413625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105633870198156394453884833 79225402648617295840413625)
  ·
    refine ⟨59419051986462971880310219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79225402648617295840413625 59419051986462971880310219)
    ·
      refine ⟨89128577979694457820465329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59419051986462971880310219 89128577979694457820465329)
      ·
        refine ⟨66846433484770843365348997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89128577979694457820465329 66846433484770843365348997)
        ·
          refine ⟨12533706278394533131002937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 66846433484770843365348997 12533706278394533131002937)
          ·
            refine ⟨9400279708795899848252203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12533706278394533131002937 9400279708795899848252203)
            ·
              refine ⟨14100419563193849772378305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9400279708795899848252203 14100419563193849772378305)
              ·
                refine ⟨10575314672395387329283729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14100419563193849772378305 10575314672395387329283729)
                ·
                  refine ⟨7931486004296540496962797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10575314672395387329283729 7931486004296540496962797)
                  ·
                    refine ⟨2974307251611202686361049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7931486004296540496962797 2974307251611202686361049)
                    ·
                      refine ⟨2230730438708402014770787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2974307251611202686361049 2230730438708402014770787)
                      ·
                        rfl

theorem cell23_4344332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 1, 2, 2, 3, 2].length) (baseStart_4344332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4344332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4344332 prefixEnd_4344332 := by exact prefixLift 4344332
  have htrace : WordTrace (prefixWord ++ tailWord_4344332) baseStart_4344332 baseEnd_4344332 := by
    simpa [prefixWord, tailWord_4344332, baseEnd_4344332] using wordTrace_append hprefix tailTrace_4344332
  have hstable : (prefixWord ++ tailWord_4344332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4344332).length < 2 ^ (prefixWord ++ tailWord_4344332).sum := by decide
  have hdescent : baseEnd_4344332 < baseStart_4344332 := by decide
  rcases family_descends (prefixWord ++ tailWord_4344332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4344333 : List Nat := [1, 7, 1, 1, 1, 2, 3, 2, 1, 4]
def baseStart_4344333 : Nat := 118140960795 + 4344333 * 2 ^ 59
def prefixEnd_4344333 : Nat := 4983230072969 + 3 ^ 40 * 4344333 * 2
def baseEnd_4344333 : Nat := 743576984063018836952761

theorem tailTrace_4344333 : CollatzResearch.WordTrace tailWord_4344333 prefixEnd_4344333 743576984063018836952761 := by
  unfold tailWord_4344333
  simp only [CollatzResearch.WordTrace]
  refine ⟨158450841770230968851613653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105633894513487312567742435 158450841770230968851613653)
  ·
    refine ⟨3713691603989788332459695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 158450841770230968851613653 3713691603989788332459695)
    ·
      refine ⟨5570537405984682498689543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3713691603989788332459695 5570537405984682498689543)
      ·
        refine ⟨8355806108977023748034315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5570537405984682498689543 8355806108977023748034315)
        ·
          refine ⟨12533709163465535622051473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8355806108977023748034315 12533709163465535622051473)
          ·
            refine ⟨9400281872599151716538605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12533709163465535622051473 9400281872599151716538605)
            ·
              refine ⟨3525105702224681893701977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9400281872599151716538605 3525105702224681893701977)
              ·
                refine ⟨2643829276668511420276483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3525105702224681893701977 2643829276668511420276483)
                ·
                  refine ⟨3965743915002767130414725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2643829276668511420276483 3965743915002767130414725)
                  ·
                    refine ⟨743576984063018836952761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3965743915002767130414725 743576984063018836952761)
                    ·
                      rfl

theorem cell23_4344333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 3, 2, 1, 4].length) (baseStart_4344333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4344333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4344333 prefixEnd_4344333 := by exact prefixLift 4344333
  have htrace : WordTrace (prefixWord ++ tailWord_4344333) baseStart_4344333 baseEnd_4344333 := by
    simpa [prefixWord, tailWord_4344333, baseEnd_4344333] using wordTrace_append hprefix tailTrace_4344333
  have hstable : (prefixWord ++ tailWord_4344333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4344333).length < 2 ^ (prefixWord ++ tailWord_4344333).sum := by decide
  have hdescent : baseEnd_4344333 < baseStart_4344333 := by decide
  rcases family_descends (prefixWord ++ tailWord_4344333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4344339 : List Nat := [1, 1, 1, 2, 1, 5, 5, 2, 1, 1, 3]
def baseStart_4344339 : Nat := 118140960795 + 4344339 * 2 ^ 59
def prefixEnd_4344339 : Nat := 4983230072969 + 3 ^ 40 * 4344339 * 2
def baseEnd_4344339 : Nat := 2230734033072983487383255

theorem tailTrace_4344339 : CollatzResearch.WordTrace tailWord_4344339 prefixEnd_4344339 2230734033072983487383255 := by
  unfold tailWord_4344339
  simp only [CollatzResearch.WordTrace]
  refine ⟨158451060608209231876332071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105634040405472821250888047 158451060608209231876332071)
  ·
    refine ⟨237676590912313847814498107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158451060608209231876332071 237676590912313847814498107)
    ·
      refine ⟨356514886368470771721747161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 237676590912313847814498107 356514886368470771721747161)
      ·
        refine ⟨267386164776353078791310371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 356514886368470771721747161 267386164776353078791310371)
        ·
          refine ⟨401079247164529618186965557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 267386164776353078791310371 401079247164529618186965557)
          ·
            refine ⟨37601179421674651705028021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 401079247164529618186965557 37601179421674651705028021)
            ·
              refine ⟨3525110570781998597346377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 37601179421674651705028021 3525110570781998597346377)
              ·
                refine ⟨2643832928086498948009783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3525110570781998597346377 2643832928086498948009783)
                ·
                  refine ⟨3965749392129748422014675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2643832928086498948009783 3965749392129748422014675)
                  ·
                    refine ⟨5948624088194622633022013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3965749392129748422014675 5948624088194622633022013)
                    ·
                      refine ⟨2230734033072983487383255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5948624088194622633022013 2230734033072983487383255)
                      ·
                        rfl

theorem cell23_4344339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 5, 2, 1, 1, 3].length) (baseStart_4344339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4344339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4344339 prefixEnd_4344339 := by exact prefixLift 4344339
  have htrace : WordTrace (prefixWord ++ tailWord_4344339) baseStart_4344339 baseEnd_4344339 := by
    simpa [prefixWord, tailWord_4344339, baseEnd_4344339] using wordTrace_append hprefix tailTrace_4344339
  have hstable : (prefixWord ++ tailWord_4344339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4344339).length < 2 ^ (prefixWord ++ tailWord_4344339).sum := by decide
  have hdescent : baseEnd_4344339 < baseStart_4344339 := by decide
  rcases family_descends (prefixWord ++ tailWord_4344339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4344362 : List Nat := [3, 1, 4, 1, 1, 2, 3, 2, 1, 1, 4]
def baseStart_4344362 : Nat := 118140960795 + 4344362 * 2 ^ 59
def prefixEnd_4344362 : Nat := 4983230072969 + 3 ^ 40 * 4344362 * 2
def baseEnd_4344362 : Nat := 2230745843128036897395649

theorem tailTrace_4344362 : CollatzResearch.WordTrace tailWord_4344362 prefixEnd_4344362 2230745843128036897395649 := by
  unfold tailWord_4344362
  simp only [CollatzResearch.WordTrace]
  refine ⟨39612974871781476701104835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105634599658083937869612893 39612974871781476701104835)
  ·
    refine ⟨59419462307672215051657253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39612974871781476701104835 59419462307672215051657253)
    ·
      refine ⟨11141149182688540322185735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 59419462307672215051657253 11141149182688540322185735)
      ·
        refine ⟨16711723774032810483278603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11141149182688540322185735 16711723774032810483278603)
        ·
          refine ⟨25067585661049215724917905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16711723774032810483278603 25067585661049215724917905)
          ·
            refine ⟨18800689245786911793688429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25067585661049215724917905 18800689245786911793688429)
            ·
              refine ⟨7050258467170091922633161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18800689245786911793688429 7050258467170091922633161)
              ·
                refine ⟨5287693850377568941974871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7050258467170091922633161 5287693850377568941974871)
                ·
                  refine ⟨7931540775566353412962307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5287693850377568941974871 7931540775566353412962307)
                  ·
                    refine ⟨11897311163349530119443461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7931540775566353412962307 11897311163349530119443461)
                    ·
                      refine ⟨2230745843128036897395649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11897311163349530119443461 2230745843128036897395649)
                      ·
                        rfl

theorem cell23_4344362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 3, 2, 1, 1, 4].length) (baseStart_4344362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4344362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4344362 prefixEnd_4344362 := by exact prefixLift 4344362
  have htrace : WordTrace (prefixWord ++ tailWord_4344362) baseStart_4344362 baseEnd_4344362 := by
    simpa [prefixWord, tailWord_4344362, baseEnd_4344362] using wordTrace_append hprefix tailTrace_4344362
  have hstable : (prefixWord ++ tailWord_4344362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4344362).length < 2 ^ (prefixWord ++ tailWord_4344362).sum := by decide
  have hdescent : baseEnd_4344362 < baseStart_4344362 := by decide
  rcases family_descends (prefixWord ++ tailWord_4344362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4344390 : List Nat := [6, 1, 1, 1, 2, 3, 2, 2, 1, 1, 3]
def baseStart_4344390 : Nat := 118140960795 + 4344390 * 2 ^ 59
def prefixEnd_4344390 : Nat := 4983230072969 + 3 ^ 40 * 4344390 * 2
def baseEnd_4344390 : Nat := 2230760220586362787845521

theorem tailTrace_4344390 : CollatzResearch.WordTrace tailWord_4344390 prefixEnd_4344390 2230760220586362787845521 := by
  unfold tailWord_4344390
  simp only [CollatzResearch.WordTrace]
  refine ⟨4951653772844514612076207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 105635280487349645057625749 4951653772844514612076207)
  ·
    refine ⟨7427480659266771918114311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4951653772844514612076207 7427480659266771918114311)
    ·
      refine ⟨11141220988900157877171467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7427480659266771918114311 11141220988900157877171467)
      ·
        refine ⟨16711831483350236815757201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11141220988900157877171467 16711831483350236815757201)
        ·
          refine ⟨12533873612512677611817901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16711831483350236815757201 12533873612512677611817901)
          ·
            refine ⟨4700202604692254104431713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12533873612512677611817901 4700202604692254104431713)
            ·
              refine ⟨3525151953519190578323785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4700202604692254104431713 3525151953519190578323785)
              ·
                refine ⟨2643863965139392933742839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3525151953519190578323785 2643863965139392933742839)
                ·
                  refine ⟨3965795947709089400614259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2643863965139392933742839 3965795947709089400614259)
                  ·
                    refine ⟨5948693921563634100921389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3965795947709089400614259 5948693921563634100921389)
                    ·
                      refine ⟨2230760220586362787845521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5948693921563634100921389 2230760220586362787845521)
                      ·
                        rfl

theorem cell23_4344390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 3, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 3, 2, 2, 1, 1, 3].length) (baseStart_4344390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4344390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4344390 prefixEnd_4344390 := by exact prefixLift 4344390
  have htrace : WordTrace (prefixWord ++ tailWord_4344390) baseStart_4344390 baseEnd_4344390 := by
    simpa [prefixWord, tailWord_4344390, baseEnd_4344390] using wordTrace_append hprefix tailTrace_4344390
  have hstable : (prefixWord ++ tailWord_4344390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4344390).length < 2 ^ (prefixWord ++ tailWord_4344390).sum := by decide
  have hdescent : baseEnd_4344390 < baseStart_4344390 := by decide
  rcases family_descends (prefixWord ++ tailWord_4344390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4344395 : List Nat := [1, 1, 1, 1, 3, 1, 4, 3, 4, 1, 3]
def baseStart_4344395 : Nat := 118140960795 + 4344395 * 2 ^ 59
def prefixEnd_4344395 : Nat := 4983230072969 + 3 ^ 40 * 4344395 * 2
def baseEnd_4344395 : Nat := 2230762787989635268282997

theorem tailTrace_4344395 : CollatzResearch.WordTrace tailWord_4344395 prefixEnd_4344395 2230762787989635268282997 := by
  unfold tailWord_4344395
  simp only [CollatzResearch.WordTrace]
  refine ⟨158453103096006353440370639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105635402064004235626913759 158453103096006353440370639)
  ·
    refine ⟨237679654644009530160555959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158453103096006353440370639 237679654644009530160555959)
    ·
      refine ⟨356519481966014295240833939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 237679654644009530160555959 356519481966014295240833939)
      ·
        refine ⟨534779222949021442861250909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 356519481966014295240833939 534779222949021442861250909)
        ·
          refine ⟨200542208605883041072969091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 534779222949021442861250909 200542208605883041072969091)
          ·
            refine ⟨300813312908824561609453637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 200542208605883041072969091 300813312908824561609453637)
            ·
              refine ⟨56402496170404605301772557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 300813312908824561609453637 56402496170404605301772557)
              ·
                refine ⟨21150936063901726988164709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 56402496170404605301772557 21150936063901726988164709)
                ·
                  refine ⟨3965800511981573810280883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21150936063901726988164709 3965800511981573810280883)
                  ·
                    refine ⟨5948700767972360715421325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3965800511981573810280883 5948700767972360715421325)
                    ·
                      refine ⟨2230762787989635268282997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5948700767972360715421325 2230762787989635268282997)
                      ·
                        rfl

theorem cell23_4344395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 3, 4, 1, 3].length) (baseStart_4344395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4344395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4344395 prefixEnd_4344395 := by exact prefixLift 4344395
  have htrace : WordTrace (prefixWord ++ tailWord_4344395) baseStart_4344395 baseEnd_4344395 := by
    simpa [prefixWord, tailWord_4344395, baseEnd_4344395] using wordTrace_append hprefix tailTrace_4344395
  have hstable : (prefixWord ++ tailWord_4344395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4344395).length < 2 ^ (prefixWord ++ tailWord_4344395).sum := by decide
  have hdescent : baseEnd_4344395 < baseStart_4344395 := by decide
  rcases family_descends (prefixWord ++ tailWord_4344395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4344398 : List Nat := [4, 1, 1, 1, 1, 2, 3, 1, 2, 7]
def baseStart_4344398 : Nat := 118140960795 + 4344398 * 2 ^ 59
def prefixEnd_4344398 : Nat := 4983230072969 + 3 ^ 40 * 4344398 * 2
def baseEnd_4344398 : Nat := 743588109477199585515161

theorem tailTrace_4344398 : CollatzResearch.WordTrace tailWord_4344398 prefixEnd_4344398 743588109477199585515161 := by
  unfold tailWord_4344398
  simp only [CollatzResearch.WordTrace]
  refine ⟨19806651564374435619091231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 105635475009996989968486565 19806651564374435619091231)
  ·
    refine ⟨29709977346561653428636847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19806651564374435619091231 29709977346561653428636847)
    ·
      refine ⟨44564966019842480142955271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29709977346561653428636847 44564966019842480142955271)
      ·
        refine ⟨66847449029763720214432907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44564966019842480142955271 66847449029763720214432907)
        ·
          refine ⟨100271173544645580321649361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66847449029763720214432907 100271173544645580321649361)
          ·
            refine ⟨75203380158484185241237021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 100271173544645580321649361 75203380158484185241237021)
            ·
              refine ⟨28201267559431569465463883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 75203380158484185241237021 28201267559431569465463883)
              ·
                refine ⟨42301901339147354198195825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28201267559431569465463883 42301901339147354198195825)
                ·
                  refine ⟨31726426004360515648646869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 42301901339147354198195825 31726426004360515648646869)
                  ·
                    refine ⟨743588109477199585515161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 31726426004360515648646869 743588109477199585515161)
                    ·
                      rfl

theorem cell23_4344398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 3, 1, 2, 7].length) (baseStart_4344398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4344398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4344398 prefixEnd_4344398 := by exact prefixLift 4344398
  have htrace : WordTrace (prefixWord ++ tailWord_4344398) baseStart_4344398 baseEnd_4344398 := by
    simpa [prefixWord, tailWord_4344398, baseEnd_4344398] using wordTrace_append hprefix tailTrace_4344398
  have hstable : (prefixWord ++ tailWord_4344398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4344398).length < 2 ^ (prefixWord ++ tailWord_4344398).sum := by decide
  have hdescent : baseEnd_4344398 < baseStart_4344398 := by decide
  rcases family_descends (prefixWord ++ tailWord_4344398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4344435 : List Nat := [1, 1, 1, 2, 2, 1, 1, 5, 3, 4, 2]
def baseStart_4344435 : Nat := 118140960795 + 4344435 * 2 ^ 59
def prefixEnd_4344435 : Nat := 4983230072969 + 3 ^ 40 * 4344435 * 2
def baseEnd_4344435 : Nat := 2230783327215815111782813

theorem tailTrace_4344435 : CollatzResearch.WordTrace tailWord_4344435 prefixEnd_4344435 2230783327215815111782813 := by
  unfold tailWord_4344435
  simp only [CollatzResearch.WordTrace]
  refine ⟨158454562015861440271826759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105636374677240960181217839 158454562015861440271826759)
  ·
    refine ⟨237681843023792160407740139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158454562015861440271826759 237681843023792160407740139)
    ·
      refine ⟨356522764535688240611610209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 237681843023792160407740139 356522764535688240611610209)
      ·
        refine ⟨267392073401766180458707657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 356522764535688240611610209 267392073401766180458707657)
        ·
          refine ⟨200544055051324635344030743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 267392073401766180458707657 200544055051324635344030743)
          ·
            refine ⟨300816082576986953016046115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 200544055051324635344030743 300816082576986953016046115)
            ·
              refine ⟨451224123865480429524069173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 300816082576986953016046115 451224123865480429524069173)
              ·
                refine ⟨42302261612388790267881485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 451224123865480429524069173 42302261612388790267881485)
                ·
                  refine ⟨15863348104645796350455557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 42302261612388790267881485 15863348104645796350455557)
                  ·
                    refine ⟨2974377769621086815710417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15863348104645796350455557 2974377769621086815710417)
                    ·
                      refine ⟨2230783327215815111782813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2974377769621086815710417 2230783327215815111782813)
                      ·
                        rfl

theorem cell23_4344435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 5, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 5, 3, 4, 2].length) (baseStart_4344435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4344435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4344435 prefixEnd_4344435 := by exact prefixLift 4344435
  have htrace : WordTrace (prefixWord ++ tailWord_4344435) baseStart_4344435 baseEnd_4344435 := by
    simpa [prefixWord, tailWord_4344435, baseEnd_4344435] using wordTrace_append hprefix tailTrace_4344435
  have hstable : (prefixWord ++ tailWord_4344435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4344435).length < 2 ^ (prefixWord ++ tailWord_4344435).sum := by decide
  have hdescent : baseEnd_4344435 < baseStart_4344435 := by decide
  rcases family_descends (prefixWord ++ tailWord_4344435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4344439 : List Nat := [1, 1, 3, 1, 1, 3, 6, 1, 1, 3, 2]
def baseStart_4344439 : Nat := 118140960795 + 4344439 * 2 ^ 59
def prefixEnd_4344439 : Nat := 4983230072969 + 3 ^ 40 * 4344439 * 2
def baseEnd_4344439 : Nat := 2230785381138433096132795

theorem tailTrace_4344439 : CollatzResearch.WordTrace tailWord_4344439 prefixEnd_4344439 2230785381138433096132795 := by
  unfold tailWord_4344439
  simp only [CollatzResearch.WordTrace]
  refine ⟨158454707907846948954972371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105636471938564632636648247 158454707907846948954972371)
  ·
    refine ⟨237682061861770423432458557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158454707907846948954972371 237682061861770423432458557)
    ·
      refine ⟨89130773198163908787171959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 237682061861770423432458557 89130773198163908787171959)
      ·
        refine ⟨133696159797245863180757939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89130773198163908787171959 133696159797245863180757939)
        ·
          refine ⟨200544239695868794771136909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 133696159797245863180757939 200544239695868794771136909)
          ·
            refine ⟨75204089885950798039176341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 200544239695868794771136909 75204089885950798039176341)
            ·
              refine ⟨3525191713403943658086391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 75204089885950798039176341 3525191713403943658086391)
              ·
                refine ⟨5287787570105915487129587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3525191713403943658086391 5287787570105915487129587)
                ·
                  refine ⟨7931681355158873230694381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5287787570105915487129587 7931681355158873230694381)
                  ·
                    refine ⟨2974380508184577461510393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7931681355158873230694381 2974380508184577461510393)
                    ·
                      refine ⟨2230785381138433096132795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2974380508184577461510393 2230785381138433096132795)
                      ·
                        rfl

theorem cell23_4344439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 6, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 6, 1, 1, 3, 2].length) (baseStart_4344439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4344439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4344439 prefixEnd_4344439 := by exact prefixLift 4344439
  have htrace : WordTrace (prefixWord ++ tailWord_4344439) baseStart_4344439 baseEnd_4344439 := by
    simpa [prefixWord, tailWord_4344439, baseEnd_4344439] using wordTrace_append hprefix tailTrace_4344439
  have hstable : (prefixWord ++ tailWord_4344439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4344439).length < 2 ^ (prefixWord ++ tailWord_4344439).sum := by decide
  have hdescent : baseEnd_4344439 < baseStart_4344439 := by decide
  rcases family_descends (prefixWord ++ tailWord_4344439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4344509 : List Nat := [1, 4, 1, 2, 1, 4, 3, 2, 5]
def baseStart_4344509 : Nat := 118140960795 + 4344509 * 2 ^ 59
def prefixEnd_4344509 : Nat := 4983230072969 + 3 ^ 40 * 4344509 * 2
def baseEnd_4344509 : Nat := 247869036087138646917497

theorem tailTrace_4344509 : CollatzResearch.WordTrace tailWord_4344509 prefixEnd_4344509 247869036087138646917497 := by
  unfold tailWord_4344509
  simp only [CollatzResearch.WordTrace]
  refine ⟨158457261017593350910020581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105638174011728900606680387 158457261017593350910020581)
  ·
    refine ⟨29710736440798753295628859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 158457261017593350910020581 29710736440798753295628859)
    ·
      refine ⟨44566104661198129943443289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29710736440798753295628859 44566104661198129943443289)
      ·
        refine ⟨33424578495898597457582467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44566104661198129943443289 33424578495898597457582467)
        ·
          refine ⟨50136867743847896186373701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33424578495898597457582467 50136867743847896186373701)
          ·
            refine ⟨9400662701971480534945069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 50136867743847896186373701 9400662701971480534945069)
            ·
              refine ⟨3525248513239305200604401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9400662701971480534945069 3525248513239305200604401)
              ·
                refine ⟨2643936384929478900453301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3525248513239305200604401 2643936384929478900453301)
                ·
                  refine ⟨247869036087138646917497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2643936384929478900453301 247869036087138646917497)
                  ·
                    rfl

theorem cell23_4344509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 3, 2, 5].length) (baseStart_4344509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4344509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4344509 prefixEnd_4344509 := by exact prefixLift 4344509
  have htrace : WordTrace (prefixWord ++ tailWord_4344509) baseStart_4344509 baseEnd_4344509 := by
    simpa [prefixWord, tailWord_4344509, baseEnd_4344509] using wordTrace_append hprefix tailTrace_4344509
  have hstable : (prefixWord ++ tailWord_4344509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4344509).length < 2 ^ (prefixWord ++ tailWord_4344509).sum := by decide
  have hdescent : baseEnd_4344509 < baseStart_4344509 := by decide
  rcases family_descends (prefixWord ++ tailWord_4344509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4344528 : List Nat := [2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 9]
def baseStart_4344528 : Nat := 118140960795 + 4344528 * 2 ^ 59
def prefixEnd_4344528 : Nat := 4983230072969 + 3 ^ 40 * 4344528 * 2
def baseEnd_4344528 : Nat := 2230831080916683247919885

theorem tailTrace_4344528 : CollatzResearch.WordTrace tailWord_4344528 prefixEnd_4344528 2230831080916683247919885 := by
  unfold tailWord_4344528
  simp only [CollatzResearch.WordTrace]
  refine ⟨79228977002262258577481119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105638636003016344769974825 79228977002262258577481119)
  ·
    refine ⟨118843465503393387866221679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79228977002262258577481119 118843465503393387866221679)
    ·
      refine ⟨178265198255090081799332519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118843465503393387866221679 178265198255090081799332519)
      ·
        refine ⟨267397797382635122698998779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 178265198255090081799332519 267397797382635122698998779)
        ·
          refine ⟨401096696073952684048498169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 267397797382635122698998779 401096696073952684048498169)
          ·
            refine ⟨300822522055464513036373627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 401096696073952684048498169 300822522055464513036373627)
            ·
              refine ⟨451233783083196769554560441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 300822522055464513036373627 451233783083196769554560441)
              ·
                refine ⟨338425337312397577165920331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 451233783083196769554560441 338425337312397577165920331)
                ·
                  refine ⟨507638005968596365748880497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 338425337312397577165920331 507638005968596365748880497)
                  ·
                    refine ⟨380728504476447274311660373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 507638005968596365748880497 380728504476447274311660373)
                    ·
                      refine ⟨2230831080916683247919885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 380728504476447274311660373 2230831080916683247919885)
                      ·
                        rfl

theorem cell23_4344528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 9].length) (baseStart_4344528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4344528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4344528 prefixEnd_4344528 := by exact prefixLift 4344528
  have htrace : WordTrace (prefixWord ++ tailWord_4344528) baseStart_4344528 baseEnd_4344528 := by
    simpa [prefixWord, tailWord_4344528, baseEnd_4344528] using wordTrace_append hprefix tailTrace_4344528
  have hstable : (prefixWord ++ tailWord_4344528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4344528).length < 2 ^ (prefixWord ++ tailWord_4344528).sum := by decide
  have hdescent : baseEnd_4344528 < baseStart_4344528 := by decide
  rcases family_descends (prefixWord ++ tailWord_4344528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4344575 : List Nat := [1, 1, 2, 2, 1, 3, 1, 2, 2, 5, 3]
def baseStart_4344575 : Nat := 118140960795 + 4344575 * 2 ^ 59
def prefixEnd_4344575 : Nat := 4983230072969 + 3 ^ 40 * 4344575 * 2
def baseEnd_4344575 : Nat := 2230855214507444564032169

theorem tailTrace_4344575 : CollatzResearch.WordTrace tailWord_4344575 prefixEnd_4344575 2230855214507444564032169 := by
  unfold tailWord_4344575
  simp only [CollatzResearch.WordTrace]
  refine ⟨158459668235354244181923179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105639778823569496121282119 158459668235354244181923179)
  ·
    refine ⟨237689502353031366272884769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158459668235354244181923179 237689502353031366272884769)
    ·
      refine ⟨178267126764773524704663577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 237689502353031366272884769 178267126764773524704663577)
      ·
        refine ⟨133700345073580143528497683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 178267126764773524704663577 133700345073580143528497683)
        ·
          refine ⟨200550517610370215292746525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 133700345073580143528497683 200550517610370215292746525)
          ·
            refine ⟨75206444103888830734779947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 200550517610370215292746525 75206444103888830734779947)
            ·
              refine ⟨112809666155833246102169921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75206444103888830734779947 112809666155833246102169921)
              ·
                refine ⟨84607249616874934576627441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 112809666155833246102169921 84607249616874934576627441)
                ·
                  refine ⟨63455437212656200932470581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 84607249616874934576627441 63455437212656200932470581)
                  ·
                    refine ⟨5948947238686518837419117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 63455437212656200932470581 5948947238686518837419117)
                    ·
                      refine ⟨2230855214507444564032169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5948947238686518837419117 2230855214507444564032169)
                      ·
                        rfl

theorem cell23_4344575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 2, 2, 5, 3].length) (baseStart_4344575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4344575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4344575 prefixEnd_4344575 := by exact prefixLift 4344575
  have htrace : WordTrace (prefixWord ++ tailWord_4344575) baseStart_4344575 baseEnd_4344575 := by
    simpa [prefixWord, tailWord_4344575, baseEnd_4344575] using wordTrace_append hprefix tailTrace_4344575
  have hstable : (prefixWord ++ tailWord_4344575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4344575).length < 2 ^ (prefixWord ++ tailWord_4344575).sum := by decide
  have hdescent : baseEnd_4344575 < baseStart_4344575 := by decide
  rcases family_descends (prefixWord ++ tailWord_4344575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4344595 : List Nat := [1, 1, 1, 2, 1, 3, 3, 3, 3, 5]
def baseStart_4344595 : Nat := 118140960795 + 4344595 * 2 ^ 59
def prefixEnd_4344595 : Nat := 4983230072969 + 3 ^ 40 * 4344595 * 2
def baseEnd_4344595 : Nat := 743621828040178161927359

theorem tailTrace_4344595 : CollatzResearch.WordTrace tailWord_4344595 prefixEnd_4344595 743621828040178161927359 := by
  unfold tailWord_4344595
  simp only [CollatzResearch.WordTrace]
  refine ⟨158460397695281787597651239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105640265130187858398434159 158460397695281787597651239)
  ·
    refine ⟨237690596542922681396476859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158460397695281787597651239 237690596542922681396476859)
    ·
      refine ⟨356535894814384022094715289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 237690596542922681396476859 356535894814384022094715289)
      ·
        refine ⟨267401921110788016571036467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 356535894814384022094715289 267401921110788016571036467)
        ·
          refine ⟨401102881666182024856554701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 267401921110788016571036467 401102881666182024856554701)
          ·
            refine ⟨150413580624818259321208013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 401102881666182024856554701 150413580624818259321208013)
            ·
              refine ⟨56405092734306847245453005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 150413580624818259321208013 56405092734306847245453005)
              ·
                refine ⟨21151909775365067717044877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 56405092734306847245453005 21151909775365067717044877)
                ·
                  refine ⟨7931966165761900393891829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21151909775365067717044877 7931966165761900393891829)
                  ·
                    refine ⟨743621828040178161927359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7931966165761900393891829 743621828040178161927359)
                    ·
                      rfl

theorem cell23_4344595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 3, 3, 5].length) (baseStart_4344595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4344595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4344595 prefixEnd_4344595 := by exact prefixLift 4344595
  have htrace : WordTrace (prefixWord ++ tailWord_4344595) baseStart_4344595 baseEnd_4344595 := by
    simpa [prefixWord, tailWord_4344595, baseEnd_4344595] using wordTrace_append hprefix tailTrace_4344595
  have hstable : (prefixWord ++ tailWord_4344595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4344595).length < 2 ^ (prefixWord ++ tailWord_4344595).sum := by decide
  have hdescent : baseEnd_4344595 < baseStart_4344595 := by decide
  rcases family_descends (prefixWord ++ tailWord_4344595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4344626 : List Nat := [3, 2, 1, 1, 3, 1, 1, 6, 1, 1, 3]
def baseStart_4344626 : Nat := 118140960795 + 4344626 * 2 ^ 59
def prefixEnd_4344626 : Nat := 4983230072969 + 3 ^ 40 * 4344626 * 2
def baseEnd_4344626 : Nat := 2230881402020823864494435

theorem tailTrace_4344626 : CollatzResearch.WordTrace tailWord_4344626 prefixEnd_4344626 2230881402020823864494435 := by
  unfold tailWord_4344626
  simp only [CollatzResearch.WordTrace]
  refine ⟨39615382089542369973007433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105641018905446319928019821 39615382089542369973007433)
  ·
    refine ⟨29711536567156777479755575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39615382089542369973007433 29711536567156777479755575)
    ·
      refine ⟨44567304850735166219633363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29711536567156777479755575 44567304850735166219633363)
      ·
        refine ⟨66850957276102749329450045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44567304850735166219633363 66850957276102749329450045)
        ·
          refine ⟨25069108978538530998543767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 66850957276102749329450045 25069108978538530998543767)
          ·
            refine ⟨37603663467807796497815651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25069108978538530998543767 37603663467807796497815651)
            ·
              refine ⟨56405495201711694746723477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37603663467807796497815651 56405495201711694746723477)
              ·
                refine ⟨2644007587580235691252663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 56405495201711694746723477 2644007587580235691252663)
                ·
                  refine ⟨3966011381370353536878995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2644007587580235691252663 3966011381370353536878995)
                  ·
                    refine ⟨5949017072055530305318493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3966011381370353536878995 5949017072055530305318493)
                    ·
                      refine ⟨2230881402020823864494435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5949017072055530305318493 2230881402020823864494435)
                      ·
                        rfl

theorem cell23_4344626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 6, 1, 1, 3].length) (baseStart_4344626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4344626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4344626 prefixEnd_4344626 := by exact prefixLift 4344626
  have htrace : WordTrace (prefixWord ++ tailWord_4344626) baseStart_4344626 baseEnd_4344626 := by
    simpa [prefixWord, tailWord_4344626, baseEnd_4344626] using wordTrace_append hprefix tailTrace_4344626
  have hstable : (prefixWord ++ tailWord_4344626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4344626).length < 2 ^ (prefixWord ++ tailWord_4344626).sum := by decide
  have hdescent : baseEnd_4344626 < baseStart_4344626 := by decide
  rcases family_descends (prefixWord ++ tailWord_4344626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4344649 : List Nat := [1, 2, 1, 1, 2, 6, 2, 2, 1, 1, 4]
def baseStart_4344649 : Nat := 118140960795 + 4344649 * 2 ^ 59
def prefixEnd_4344649 : Nat := 4983230072969 + 3 ^ 40 * 4344649 * 2
def baseEnd_4344649 : Nat := 2230893212075877274506829

theorem tailTrace_4344649 : CollatzResearch.WordTrace tailWord_4344649 prefixEnd_4344649 2230893212075877274506829 := by
  unfold tailWord_4344649
  simp only [CollatzResearch.WordTrace]
  refine ⟨158462367237086154820117001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105641578158057436546744667 158462367237086154820117001)
  ·
    refine ⟨118846775427814616115087751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 158462367237086154820117001 118846775427814616115087751)
    ·
      refine ⟨178270163141721924172631627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118846775427814616115087751 178270163141721924172631627)
      ·
        refine ⟨267405244712582886258947441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 178270163141721924172631627 267405244712582886258947441)
        ·
          refine ⟨200553933534437164694210581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 267405244712582886258947441 200553933534437164694210581)
          ·
            refine ⟨9400965634426742095041121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 200553933534437164694210581 9400965634426742095041121)
            ·
              refine ⟨7050724225820056571280841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9400965634426742095041121 7050724225820056571280841)
              ·
                refine ⟨5288043169365042428460631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7050724225820056571280841 5288043169365042428460631)
                ·
                  refine ⟨7932064754047563642690947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5288043169365042428460631 7932064754047563642690947)
                  ·
                    refine ⟨11898097131071345464036421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7932064754047563642690947 11898097131071345464036421)
                    ·
                      refine ⟨2230893212075877274506829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11898097131071345464036421 2230893212075877274506829)
                      ·
                        rfl

theorem cell23_4344649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 2, 2, 1, 1, 4].length) (baseStart_4344649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4344649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4344649 prefixEnd_4344649 := by exact prefixLift 4344649
  have htrace : WordTrace (prefixWord ++ tailWord_4344649) baseStart_4344649 baseEnd_4344649 := by
    simpa [prefixWord, tailWord_4344649, baseEnd_4344649] using wordTrace_append hprefix tailTrace_4344649
  have hstable : (prefixWord ++ tailWord_4344649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4344649).length < 2 ^ (prefixWord ++ tailWord_4344649).sum := by decide
  have hdescent : baseEnd_4344649 < baseStart_4344649 := by decide
  rcases family_descends (prefixWord ++ tailWord_4344649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4344660 : List Nat := [2, 4, 1, 1, 4, 2, 1, 3, 1, 1, 3]
def baseStart_4344660 : Nat := 118140960795 + 4344660 * 2 ^ 59
def prefixEnd_4344660 : Nat := 4983230072969 + 3 ^ 40 * 4344660 * 2
def baseEnd_4344660 : Nat := 2230898860363076731469279

theorem tailTrace_4344660 : CollatzResearch.WordTrace tailWord_4344660 prefixEnd_4344660 2230898860363076731469279 := by
  unfold tailWord_4344660
  simp only [CollatzResearch.WordTrace]
  refine ⟨79231384220023151849383717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105641845626697535799178289 79231384220023151849383717)
  ·
    refine ⟨14855884541254340971759447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 79231384220023151849383717 14855884541254340971759447)
    ·
      refine ⟨22283826811881511457639171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14855884541254340971759447 22283826811881511457639171)
      ·
        refine ⟨33425740217822267186458757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22283826811881511457639171 33425740217822267186458757)
        ·
          refine ⟨6267326290841675097461017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 33425740217822267186458757 6267326290841675097461017)
          ·
            refine ⟨4700494718131256323095763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6267326290841675097461017 4700494718131256323095763)
            ·
              refine ⟨7050742077196884484643645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4700494718131256323095763 7050742077196884484643645)
              ·
                refine ⟨2644028278948831681741367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7050742077196884484643645 2644028278948831681741367)
                ·
                  refine ⟨3966042418423247522612051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2644028278948831681741367 3966042418423247522612051)
                  ·
                    refine ⟨5949063627634871283918077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3966042418423247522612051 5949063627634871283918077)
                    ·
                      refine ⟨2230898860363076731469279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5949063627634871283918077 2230898860363076731469279)
                      ·
                        rfl

theorem cell23_4344660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 2, 1, 3, 1, 1, 3].length) (baseStart_4344660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4344660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4344660 prefixEnd_4344660 := by exact prefixLift 4344660
  have htrace : WordTrace (prefixWord ++ tailWord_4344660) baseStart_4344660 baseEnd_4344660 := by
    simpa [prefixWord, tailWord_4344660, baseEnd_4344660] using wordTrace_append hprefix tailTrace_4344660
  have hstable : (prefixWord ++ tailWord_4344660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4344660).length < 2 ^ (prefixWord ++ tailWord_4344660).sum := by decide
  have hdescent : baseEnd_4344660 < baseStart_4344660 := by decide
  rcases family_descends (prefixWord ++ tailWord_4344660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4344693 : List Nat := [1, 3, 4, 1, 1, 4, 2, 1, 2, 4]
def baseStart_4344693 : Nat := 118140960795 + 4344693 * 2 ^ 59
def prefixEnd_4344693 : Nat := 4983230072969 + 3 ^ 40 * 4344693 * 2
def baseEnd_4344693 : Nat := 743638601741558367452209

theorem tailTrace_4344693 : CollatzResearch.WordTrace tailWord_4344693 prefixEnd_4344693 743638601741558367452209 := by
  unfold tailWord_4344693
  simp only [CollatzResearch.WordTrace]
  refine ⟨158463972048926750334718733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105642648032617833556479155 158463972048926750334718733)
  ·
    refine ⟨59423989518347531375519525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 158463972048926750334718733 59423989518347531375519525)
    ·
      refine ⟨11141998034690162132909911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 59423989518347531375519525 11141998034690162132909911)
      ·
        refine ⟨16712997052035243199364867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11141998034690162132909911 16712997052035243199364867)
        ·
          refine ⟨25069495578052864799047301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16712997052035243199364867 25069495578052864799047301)
          ·
            refine ⟨4700530420884912149821369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25069495578052864799047301 4700530420884912149821369)
            ·
              refine ⟨3525397815663684112366027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4700530420884912149821369 3525397815663684112366027)
              ·
                refine ⟨5288096723495526168549041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3525397815663684112366027 5288096723495526168549041)
                ·
                  refine ⟨3966072542621644626411781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5288096723495526168549041 3966072542621644626411781)
                  ·
                    refine ⟨743638601741558367452209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3966072542621644626411781 743638601741558367452209)
                    ·
                      rfl

theorem cell23_4344693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 4, 2, 1, 2, 4].length) (baseStart_4344693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4344693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4344693 prefixEnd_4344693 := by exact prefixLift 4344693
  have htrace : WordTrace (prefixWord ++ tailWord_4344693) baseStart_4344693 baseEnd_4344693 := by
    simpa [prefixWord, tailWord_4344693, baseEnd_4344693] using wordTrace_append hprefix tailTrace_4344693
  have hstable : (prefixWord ++ tailWord_4344693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4344693).length < 2 ^ (prefixWord ++ tailWord_4344693).sum := by decide
  have hdescent : baseEnd_4344693 < baseStart_4344693 := by decide
  rcases family_descends (prefixWord ++ tailWord_4344693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4344762 : List Nat := [3, 1, 1, 1, 2, 1, 5, 2, 7]
def baseStart_4344762 : Nat := 118140960795 + 4344762 * 2 ^ 59
def prefixEnd_4344762 : Nat := 4983230072969 + 3 ^ 40 * 4344762 * 2
def baseEnd_4344762 : Nat := 247883470598870592488201

theorem tailTrace_4344762 : CollatzResearch.WordTrace tailWord_4344762 prefixEnd_4344762 247883470598870592488201 := by
  unfold tailWord_4344762
  simp only [CollatzResearch.WordTrace]
  refine ⟨39616622171419193779745135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105644325790451183412653693 39616622171419193779745135)
  ·
    refine ⟨59424933257128790669617703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39616622171419193779745135 59424933257128790669617703)
    ·
      refine ⟨89137399885693186004426555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59424933257128790669617703 89137399885693186004426555)
      ·
        refine ⟨133706099828539779006639833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89137399885693186004426555 133706099828539779006639833)
        ·
          refine ⟨100279574871404834254979875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 133706099828539779006639833 100279574871404834254979875)
          ·
            refine ⟨150419362307107251382469813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 100279574871404834254979875 150419362307107251382469813)
            ·
              refine ⟨14101815216291304817106545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 150419362307107251382469813 14101815216291304817106545)
              ·
                refine ⟨10576361412218478612829909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14101815216291304817106545 10576361412218478612829909)
                ·
                  refine ⟨247883470598870592488201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10576361412218478612829909 247883470598870592488201)
                  ·
                    rfl

theorem cell23_4344762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 5, 2, 7].length) (baseStart_4344762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4344762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4344762 prefixEnd_4344762 := by exact prefixLift 4344762
  have htrace : WordTrace (prefixWord ++ tailWord_4344762) baseStart_4344762 baseEnd_4344762 := by
    simpa [prefixWord, tailWord_4344762, baseEnd_4344762] using wordTrace_append hprefix tailTrace_4344762
  have hstable : (prefixWord ++ tailWord_4344762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4344762).length < 2 ^ (prefixWord ++ tailWord_4344762).sum := by decide
  have hdescent : baseEnd_4344762 < baseStart_4344762 := by decide
  rcases family_descends (prefixWord ++ tailWord_4344762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4344779 : List Nat := [1, 1, 1, 1, 3, 5, 1, 5, 5]
def baseStart_4344779 : Nat := 118140960795 + 4344779 * 2 ^ 59
def prefixEnd_4344779 : Nat := 4983230072969 + 3 ^ 40 * 4344779 * 2
def baseEnd_4344779 : Nat := 247884440506773529542359

theorem tailTrace_4344779 : CollatzResearch.WordTrace tailWord_4344779 prefixEnd_4344779 247884440506773529542359 := by
  unfold tailWord_4344779
  simp only [CollatzResearch.WordTrace]
  refine ⟨158467108726615187022349391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105644739151076791348232927 158467108726615187022349391)
  ·
    refine ⟨237700663089922780533524087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158467108726615187022349391 237700663089922780533524087)
    ·
      refine ⟨356550994634884170800286131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 237700663089922780533524087 356550994634884170800286131)
      ·
        refine ⟨534826491952326256200429197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 356550994634884170800286131 534826491952326256200429197)
        ·
          refine ⟨200559934482122346075160949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 534826491952326256200429197 200559934482122346075160949)
          ·
            refine ⟨18802493857698969944546339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 200559934482122346075160949 18802493857698969944546339)
            ·
              refine ⟨28203740786548454916819509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18802493857698969944546339 28203740786548454916819509)
              ·
                refine ⟨2644100698738917648451829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 28203740786548454916819509 2644100698738917648451829)
                ·
                  refine ⟨247884440506773529542359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2644100698738917648451829 247884440506773529542359)
                  ·
                    rfl

theorem cell23_4344779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 1, 5, 5].length) (baseStart_4344779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4344779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4344779 prefixEnd_4344779 := by exact prefixLift 4344779
  have htrace : WordTrace (prefixWord ++ tailWord_4344779) baseStart_4344779 baseEnd_4344779 := by
    simpa [prefixWord, tailWord_4344779, baseEnd_4344779] using wordTrace_append hprefix tailTrace_4344779
  have hstable : (prefixWord ++ tailWord_4344779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4344779).length < 2 ^ (prefixWord ++ tailWord_4344779).sum := by decide
  have hdescent : baseEnd_4344779 < baseStart_4344779 := by decide
  rcases family_descends (prefixWord ++ tailWord_4344779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4344790 : List Nat := [5, 2, 1, 1, 2, 2, 1, 1, 4, 2, 2]
def baseStart_4344790 : Nat := 118140960795 + 4344790 * 2 ^ 59
def prefixEnd_4344790 : Nat := 4983230072969 + 3 ^ 40 * 4344790 * 2
def baseEnd_4344790 : Nat := 2230965612848161222843681

theorem tailTrace_4344790 : CollatzResearch.WordTrace tailWord_4344790 prefixEnd_4344790 2230965612848161222843681 := by
  unfold tailWord_4344790
  simp only [CollatzResearch.WordTrace]
  refine ⟨9904219370598458493812489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 105645006619716890600666549 9904219370598458493812489)
  ·
    refine ⟨7428164527948843870359367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9904219370598458493812489 7428164527948843870359367)
    ·
      refine ⟨11142246791923265805539051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7428164527948843870359367 11142246791923265805539051)
      ·
        refine ⟨16713370187884898708308577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11142246791923265805539051 16713370187884898708308577)
        ·
          refine ⟨12535027640913674031231433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16713370187884898708308577 12535027640913674031231433)
          ·
            refine ⟨9401270730685255523423575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12535027640913674031231433 9401270730685255523423575)
            ·
              refine ⟨14101906096027883285135363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9401270730685255523423575 14101906096027883285135363)
              ·
                refine ⟨21152859144041824927703045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14101906096027883285135363 21152859144041824927703045)
                ·
                  refine ⟨3966161089507842173944321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21152859144041824927703045 3966161089507842173944321)
                  ·
                    refine ⟨2974620817130881630458241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3966161089507842173944321 2974620817130881630458241)
                    ·
                      refine ⟨2230965612848161222843681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2974620817130881630458241 2230965612848161222843681)
                      ·
                        rfl

theorem cell23_4344790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 1, 1, 4, 2, 2].length) (baseStart_4344790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4344790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4344790 prefixEnd_4344790 := by exact prefixLift 4344790
  have htrace : WordTrace (prefixWord ++ tailWord_4344790) baseStart_4344790 baseEnd_4344790 := by
    simpa [prefixWord, tailWord_4344790, baseEnd_4344790] using wordTrace_append hprefix tailTrace_4344790
  have hstable : (prefixWord ++ tailWord_4344790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4344790).length < 2 ^ (prefixWord ++ tailWord_4344790).sum := by decide
  have hdescent : baseEnd_4344790 < baseStart_4344790 := by decide
  rcases family_descends (prefixWord ++ tailWord_4344790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4344829 : List Nat := [1, 4, 1, 1, 1, 2, 1, 5, 2, 1, 4]
def baseStart_4344829 : Nat := 118140960795 + 4344829 * 2 ^ 59
def prefixEnd_4344829 : Nat := 4983230072969 + 3 ^ 40 * 4344829 * 2
def baseEnd_4344829 : Nat := 2230985638593686570256001

theorem tailTrace_4344829 : CollatzResearch.WordTrace tailWord_4344829 prefixEnd_4344829 2230985638593686570256001 := by
  unfold tailWord_4344829
  simp only [CollatzResearch.WordTrace]
  refine ⟨158468932376434045561669541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105645954917622697041113027 158468932376434045561669541)
  ·
    refine ⟨29712924820581383542813039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 158468932376434045561669541 29712924820581383542813039)
    ·
      refine ⟨44569387230872075314219559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29712924820581383542813039 44569387230872075314219559)
      ·
        refine ⟨66854080846308112971329339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44569387230872075314219559 66854080846308112971329339)
        ·
          refine ⟨100281121269462169456994009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66854080846308112971329339 100281121269462169456994009)
          ·
            refine ⟨75210840952096627092745507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 100281121269462169456994009 75210840952096627092745507)
            ·
              refine ⟨112816261428144940639118261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75210840952096627092745507 112816261428144940639118261)
              ·
                refine ⟨10576524508888588184917337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 112816261428144940639118261 10576524508888588184917337)
                ·
                  refine ⟨7932393381666441138688003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10576524508888588184917337 7932393381666441138688003)
                  ·
                    refine ⟨11898590072499661708032005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7932393381666441138688003 11898590072499661708032005)
                    ·
                      refine ⟨2230985638593686570256001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11898590072499661708032005 2230985638593686570256001)
                      ·
                        rfl

theorem cell23_4344829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 5, 2, 1, 4].length) (baseStart_4344829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4344829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4344829 prefixEnd_4344829 := by exact prefixLift 4344829
  have htrace : WordTrace (prefixWord ++ tailWord_4344829) baseStart_4344829 baseEnd_4344829 := by
    simpa [prefixWord, tailWord_4344829, baseEnd_4344829] using wordTrace_append hprefix tailTrace_4344829
  have hstable : (prefixWord ++ tailWord_4344829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4344829).length < 2 ^ (prefixWord ++ tailWord_4344829).sum := by decide
  have hdescent : baseEnd_4344829 < baseStart_4344829 := by decide
  rcases family_descends (prefixWord ++ tailWord_4344829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4344830 : List Nat := [4, 2, 2, 2, 2, 2, 1, 3, 5]
def baseStart_4344830 : Nat := 118140960795 + 4344830 * 2 ^ 59
def prefixEnd_4344830 : Nat := 4983230072969 + 3 ^ 40 * 4344830 * 2
def baseEnd_4344830 : Nat := 247887350230482340704833

theorem tailTrace_4344830 : CollatzResearch.WordTrace tailWord_4344830 prefixEnd_4344830 247887350230482340704833 := by
  unfold tailWord_4344830
  simp only [CollatzResearch.WordTrace]
  refine ⟨19808621106178802841556993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 105645979232953615154970629 19808621106178802841556993)
  ·
    refine ⟨14856465829634102131167745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19808621106178802841556993 14856465829634102131167745)
    ·
      refine ⟨11142349372225576598375809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14856465829634102131167745 11142349372225576598375809)
      ·
        refine ⟨8356762029169182448781857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11142349372225576598375809 8356762029169182448781857)
        ·
          refine ⟨6267571521876886836586393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8356762029169182448781857 6267571521876886836586393)
          ·
            refine ⟨4700678641407665127439795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6267571521876886836586393 4700678641407665127439795)
            ·
              refine ⟨7051017962111497691159693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4700678641407665127439795 7051017962111497691159693)
              ·
                refine ⟨2644131735791811634184885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7051017962111497691159693 2644131735791811634184885)
                ·
                  refine ⟨247887350230482340704833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2644131735791811634184885 247887350230482340704833)
                  ·
                    rfl

theorem cell23_4344830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 2, 1, 3, 5].length) (baseStart_4344830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4344830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4344830 prefixEnd_4344830 := by exact prefixLift 4344830
  have htrace : WordTrace (prefixWord ++ tailWord_4344830) baseStart_4344830 baseEnd_4344830 := by
    simpa [prefixWord, tailWord_4344830, baseEnd_4344830] using wordTrace_append hprefix tailTrace_4344830
  have hstable : (prefixWord ++ tailWord_4344830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4344830).length < 2 ^ (prefixWord ++ tailWord_4344830).sum := by decide
  have hdescent : baseEnd_4344830 < baseStart_4344830 := by decide
  rcases family_descends (prefixWord ++ tailWord_4344830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4344846 : List Nat := [4, 1, 1, 2, 2, 3, 1, 2, 2, 1, 4]
def baseStart_4344846 : Nat := 118140960795 + 4344846 * 2 ^ 59
def prefixEnd_4344846 : Nat := 4983230072969 + 3 ^ 40 * 4344846 * 2
def baseEnd_4344846 : Nat := 2230994367764813003743423

theorem tailTrace_4344846 : CollatzResearch.WordTrace tailWord_4344846 prefixEnd_4344846 2230994367764813003743423 := by
  unfold tailWord_4344846
  simp only [CollatzResearch.WordTrace]
  refine ⟨19808694052171557183129799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 105646368278248304976692261 19808694052171557183129799)
  ·
    refine ⟨29713041078257335774694699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19808694052171557183129799 29713041078257335774694699)
    ·
      refine ⟨44569561617386003662042049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29713041078257335774694699 44569561617386003662042049)
      ·
        refine ⟨33427171213039502746531537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44569561617386003662042049 33427171213039502746531537)
        ·
          refine ⟨25070378409779627059898653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33427171213039502746531537 25070378409779627059898653)
          ·
            refine ⟨9401391903667360147461995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25070378409779627059898653 9401391903667360147461995)
            ·
              refine ⟨14102087855501040221192993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9401391903667360147461995 14102087855501040221192993)
              ·
                refine ⟨10576565891625780165894745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14102087855501040221192993 10576565891625780165894745)
                ·
                  refine ⟨7932424418719335124421059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10576565891625780165894745 7932424418719335124421059)
                  ·
                    refine ⟨11898636628079002686631589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7932424418719335124421059 11898636628079002686631589)
                    ·
                      refine ⟨2230994367764813003743423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11898636628079002686631589 2230994367764813003743423)
                      ·
                        rfl

theorem cell23_4344846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 1, 2, 2, 1, 4].length) (baseStart_4344846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4344846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4344846 prefixEnd_4344846 := by exact prefixLift 4344846
  have htrace : WordTrace (prefixWord ++ tailWord_4344846) baseStart_4344846 baseEnd_4344846 := by
    simpa [prefixWord, tailWord_4344846, baseEnd_4344846] using wordTrace_append hprefix tailTrace_4344846
  have hstable : (prefixWord ++ tailWord_4344846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4344846).length < 2 ^ (prefixWord ++ tailWord_4344846).sum := by decide
  have hdescent : baseEnd_4344846 < baseStart_4344846 := by decide
  rcases family_descends (prefixWord ++ tailWord_4344846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4344856 : List Nat := [2, 1, 2, 3, 2, 2, 3, 1, 3, 4]
def baseStart_4344856 : Nat := 118140960795 + 4344856 * 2 ^ 59
def prefixEnd_4344856 : Nat := 4983230072969 + 3 ^ 40 * 4344856 * 2
def baseEnd_4344856 : Nat := 743666500857119321539459

theorem tailTrace_4344856 : CollatzResearch.WordTrace tailWord_4344856 prefixEnd_4344856 743666500857119321539459 := by
  unfold tailWord_4344856
  simp only [CollatzResearch.WordTrace]
  refine ⟨79234958573668114586451211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105646611431557486115268281 79234958573668114586451211)
  ·
    refine ⟨118852437860502171879676817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79234958573668114586451211 118852437860502171879676817)
    ·
      refine ⟨89139328395376628909757613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 118852437860502171879676817 89139328395376628909757613)
      ·
        refine ⟨33427248148266235841159105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 89139328395376628909757613 33427248148266235841159105)
        ·
          refine ⟨25070436111199676880869329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33427248148266235841159105 25070436111199676880869329)
          ·
            refine ⟨18802827083399757660651997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25070436111199676880869329 18802827083399757660651997)
            ·
              refine ⟨7051060156274909122744499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18802827083399757660651997 7051060156274909122744499)
              ·
                refine ⟨10576590234412363684116749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7051060156274909122744499 10576590234412363684116749)
                ·
                  refine ⟨3966221337904636381543781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10576590234412363684116749 3966221337904636381543781)
                  ·
                    refine ⟨743666500857119321539459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3966221337904636381543781 743666500857119321539459)
                    ·
                      rfl

theorem cell23_4344856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 3, 1, 3, 4].length) (baseStart_4344856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4344856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4344856 prefixEnd_4344856 := by exact prefixLift 4344856
  have htrace : WordTrace (prefixWord ++ tailWord_4344856) baseStart_4344856 baseEnd_4344856 := by
    simpa [prefixWord, tailWord_4344856, baseEnd_4344856] using wordTrace_append hprefix tailTrace_4344856
  have hstable : (prefixWord ++ tailWord_4344856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4344856).length < 2 ^ (prefixWord ++ tailWord_4344856).sum := by decide
  have hdescent : baseEnd_4344856 < baseStart_4344856 := by decide
  rcases family_descends (prefixWord ++ tailWord_4344856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4344869 : List Nat := [1, 3, 1, 2, 2, 2, 3, 3, 6]
def baseStart_4344869 : Nat := 118140960795 + 4344869 * 2 ^ 59
def prefixEnd_4344869 : Nat := 4983230072969 + 3 ^ 40 * 4344869 * 2
def baseEnd_4344869 : Nat := 247889575313318490417313

theorem tailTrace_4344869 : CollatzResearch.WordTrace tailWord_4344869 prefixEnd_4344869 247889575313318490417313 := by
  unfold tailWord_4344869
  simp only [CollatzResearch.WordTrace]
  refine ⟨158470391296289132393125661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105646927530859421595417107 158470391296289132393125661)
  ·
    refine ⟨59426396736108424647422123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 158470391296289132393125661 59426396736108424647422123)
    ·
      refine ⟨89139595104162636971133185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59426396736108424647422123 89139595104162636971133185)
      ·
        refine ⟨66854696328121977728349889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89139595104162636971133185 66854696328121977728349889)
        ·
          refine ⟨50141022246091483296262417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66854696328121977728349889 50141022246091483296262417)
          ·
            refine ⟨37605766684568612472196813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50141022246091483296262417 37605766684568612472196813)
            ·
              refine ⟨14102162506713229677073805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37605766684568612472196813 14102162506713229677073805)
              ·
                refine ⟨5288310940017461128902677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14102162506713229677073805 5288310940017461128902677)
                ·
                  refine ⟨247889575313318490417313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5288310940017461128902677 247889575313318490417313)
                  ·
                    rfl

theorem cell23_4344869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 3, 3, 6].length) (baseStart_4344869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4344869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4344869 prefixEnd_4344869 := by exact prefixLift 4344869
  have htrace : WordTrace (prefixWord ++ tailWord_4344869) baseStart_4344869 baseEnd_4344869 := by
    simpa [prefixWord, tailWord_4344869, baseEnd_4344869] using wordTrace_append hprefix tailTrace_4344869
  have hstable : (prefixWord ++ tailWord_4344869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4344869).length < 2 ^ (prefixWord ++ tailWord_4344869).sum := by decide
  have hdescent : baseEnd_4344869 < baseStart_4344869 := by decide
  rcases family_descends (prefixWord ++ tailWord_4344869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4344929 : List Nat := [1, 2, 3, 1, 1, 2, 3, 3, 1, 6]
def baseStart_4344929 : Nat := 118140960795 + 4344929 * 2 ^ 59
def prefixEnd_4344929 : Nat := 4983230072969 + 3 ^ 40 * 4344929 * 2
def baseEnd_4344929 : Nat := 743678995553045393001847

theorem tailTrace_4344929 : CollatzResearch.WordTrace tailWord_4344929 prefixEnd_4344929 743678995553045393001847 := by
  unfold tailWord_4344929
  simp only [CollatzResearch.WordTrace]
  refine ⟨158472579676071762640309841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105648386450714508426873227 158472579676071762640309841)
  ·
    refine ⟨118854434757053821980232381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 158472579676071762640309841 118854434757053821980232381)
    ·
      refine ⟨44570413033895183242587143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 118854434757053821980232381 44570413033895183242587143)
      ·
        refine ⟨66855619550842774863880715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44570413033895183242587143 66855619550842774863880715)
        ·
          refine ⟨100283429326264162295821073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66855619550842774863880715 100283429326264162295821073)
          ·
            refine ⟨75212571994698121721865805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 100283429326264162295821073 75212571994698121721865805)
            ·
              refine ⟨28204714498011795645699677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 75212571994698121721865805 28204714498011795645699677)
              ·
                refine ⟨10576767936754423367137379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28204714498011795645699677 10576767936754423367137379)
                ·
                  refine ⟨15865151905131635050706069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10576767936754423367137379 15865151905131635050706069)
                  ·
                    refine ⟨743678995553045393001847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15865151905131635050706069 743678995553045393001847)
                    ·
                      rfl

theorem cell23_4344929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 3, 3, 1, 6].length) (baseStart_4344929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4344929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4344929 prefixEnd_4344929 := by exact prefixLift 4344929
  have htrace : WordTrace (prefixWord ++ tailWord_4344929) baseStart_4344929 baseEnd_4344929 := by
    simpa [prefixWord, tailWord_4344929, baseEnd_4344929] using wordTrace_append hprefix tailTrace_4344929
  have hstable : (prefixWord ++ tailWord_4344929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4344929).length < 2 ^ (prefixWord ++ tailWord_4344929).sum := by decide
  have hdescent : baseEnd_4344929 < baseStart_4344929 := by decide
  rcases family_descends (prefixWord ++ tailWord_4344929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4344930 : List Nat := [3, 3, 2, 2, 1, 2, 1, 2, 3, 1, 3]
def baseStart_4344930 : Nat := 118140960795 + 4344930 * 2 ^ 59
def prefixEnd_4344930 : Nat := 4983230072969 + 3 ^ 40 * 4344930 * 2
def baseEnd_4344930 : Nat := 2231037500139790675093037

theorem tailTrace_4344930 : CollatzResearch.WordTrace tailWord_4344930 prefixEnd_4344930 2231037500139790675093037 := by
  unfold tailWord_4344930
  simp only [CollatzResearch.WordTrace]
  refine ⟨39618154037267034952774061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105648410766045426540730829 39618154037267034952774061)
  ·
    refine ⟨14856807763975138107290273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39618154037267034952774061 14856807763975138107290273)
    ·
      refine ⟨11142605822981353580467705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14856807763975138107290273 11142605822981353580467705)
      ·
        refine ⟨8356954367236015185350779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11142605822981353580467705 8356954367236015185350779)
        ·
          refine ⟨12535431550854022778026169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8356954367236015185350779 12535431550854022778026169)
          ·
            refine ⟨9401573663140517083519627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12535431550854022778026169 9401573663140517083519627)
            ·
              refine ⟨14102360494710775625279441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9401573663140517083519627 14102360494710775625279441)
              ·
                refine ⟨10576770371033081718959581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14102360494710775625279441 10576770371033081718959581)
                ·
                  refine ⟨3966288889137405644609843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10576770371033081718959581 3966288889137405644609843)
                  ·
                    refine ⟨5949433333706108466914765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3966288889137405644609843 5949433333706108466914765)
                    ·
                      refine ⟨2231037500139790675093037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5949433333706108466914765 2231037500139790675093037)
                      ·
                        rfl

theorem cell23_4344930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 1, 2, 3, 1, 3].length) (baseStart_4344930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4344930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4344930 prefixEnd_4344930 := by exact prefixLift 4344930
  have htrace : WordTrace (prefixWord ++ tailWord_4344930) baseStart_4344930 baseEnd_4344930 := by
    simpa [prefixWord, tailWord_4344930, baseEnd_4344930] using wordTrace_append hprefix tailTrace_4344930
  have hstable : (prefixWord ++ tailWord_4344930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4344930).length < 2 ^ (prefixWord ++ tailWord_4344930).sum := by decide
  have hdescent : baseEnd_4344930 < baseStart_4344930 := by decide
  rcases family_descends (prefixWord ++ tailWord_4344930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4344946 : List Nat := [3, 2, 1, 2, 2, 1, 2, 2, 4, 4]
def baseStart_4344946 : Nat := 118140960795 + 4344946 * 2 ^ 59
def prefixEnd_4344946 : Nat := 4983230072969 + 3 ^ 40 * 4344946 * 2
def baseEnd_4344946 : Nat := 743681905276754204164321

theorem tailTrace_4344946 : CollatzResearch.WordTrace tailWord_4344946 prefixEnd_4344946 743681905276754204164321 := by
  unfold tailWord_4344946
  simp only [CollatzResearch.WordTrace]
  refine ⟨39618299929252543635919673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105648799811340116362452461 39618299929252543635919673)
  ·
    refine ⟨29713724946939407726939755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39618299929252543635919673 29713724946939407726939755)
    ·
      refine ⟨44570587420409111590409633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29713724946939407726939755 44570587420409111590409633)
      ·
        refine ⟨33427940565306833692807225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44570587420409111590409633 33427940565306833692807225)
        ·
          refine ⟨25070955423980125269605419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33427940565306833692807225 25070955423980125269605419)
          ·
            refine ⟨37606433135970187904408129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25070955423980125269605419 37606433135970187904408129)
            ·
              refine ⟨28204824851977640928306097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37606433135970187904408129 28204824851977640928306097)
              ·
                refine ⟨21153618638983230696229573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28204824851977640928306097 21153618638983230696229573)
                ·
                  refine ⟨3966303494809355755543045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21153618638983230696229573 3966303494809355755543045)
                  ·
                    refine ⟨743681905276754204164321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3966303494809355755543045 743681905276754204164321)
                    ·
                      rfl

theorem cell23_4344946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 2, 2, 4, 4].length) (baseStart_4344946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4344946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4344946 prefixEnd_4344946 := by exact prefixLift 4344946
  have htrace : WordTrace (prefixWord ++ tailWord_4344946) baseStart_4344946 baseEnd_4344946 := by
    simpa [prefixWord, tailWord_4344946, baseEnd_4344946] using wordTrace_append hprefix tailTrace_4344946
  have hstable : (prefixWord ++ tailWord_4344946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4344946).length < 2 ^ (prefixWord ++ tailWord_4344946).sum := by decide
  have hdescent : baseEnd_4344946 < baseStart_4344946 := by decide
  rcases family_descends (prefixWord ++ tailWord_4344946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4344953 : List Nat := [1, 2, 1, 3, 5, 1, 1, 3, 1, 1, 4]
def baseStart_4344953 : Nat := 118140960795 + 4344953 * 2 ^ 59
def prefixEnd_4344953 : Nat := 4983230072969 + 3 ^ 40 * 4344953 * 2
def baseEnd_4344953 : Nat := 2231049310194844085105431

theorem tailTrace_4344953 : CollatzResearch.WordTrace tailWord_4344953 prefixEnd_4344953 2231049310194844085105431 := by
  unfold tailWord_4344953
  simp only [CollatzResearch.WordTrace]
  refine ⟨158473455027984814739183513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105648970018656543159455675 158473455027984814739183513)
  ·
    refine ⟨118855091270988611054387635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 158473455027984814739183513 118855091270988611054387635)
    ·
      refine ⟨178282636906482916581581453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118855091270988611054387635 178282636906482916581581453)
      ·
        refine ⟨66855988839931093718093045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 178282636906482916581581453 66855988839931093718093045)
        ·
          refine ⟨6267748953743540036071223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 66855988839931093718093045 6267748953743540036071223)
          ·
            refine ⟨9401623430615310054106835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6267748953743540036071223 9401623430615310054106835)
            ·
              refine ⟨14102435145922965081160253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9401623430615310054106835 14102435145922965081160253)
              ·
                refine ⟨5288413179721111905435095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14102435145922965081160253 5288413179721111905435095)
                ·
                  refine ⟨7932619769581667858152643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5288413179721111905435095 7932619769581667858152643)
                  ·
                    refine ⟨11898929654372501787228965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7932619769581667858152643 11898929654372501787228965)
                    ·
                      refine ⟨2231049310194844085105431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11898929654372501787228965 2231049310194844085105431)
                      ·
                        rfl

theorem cell23_4344953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 1, 3, 1, 1, 4].length) (baseStart_4344953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4344953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4344953 prefixEnd_4344953 := by exact prefixLift 4344953
  have htrace : WordTrace (prefixWord ++ tailWord_4344953) baseStart_4344953 baseEnd_4344953 := by
    simpa [prefixWord, tailWord_4344953, baseEnd_4344953] using wordTrace_append hprefix tailTrace_4344953
  have hstable : (prefixWord ++ tailWord_4344953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4344953).length < 2 ^ (prefixWord ++ tailWord_4344953).sum := by decide
  have hdescent : baseEnd_4344953 < baseStart_4344953 := by decide
  rcases family_descends (prefixWord ++ tailWord_4344953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4344970 : List Nat := [3, 1, 2, 3, 1, 1, 4, 1, 3, 2, 2]
def baseStart_4344970 : Nat := 118140960795 + 4344970 * 2 ^ 59
def prefixEnd_4344970 : Nat := 4983230072969 + 3 ^ 40 * 4344970 * 2
def baseEnd_4344970 : Nat := 2231058039365970518592853

theorem tailTrace_4344970 : CollatzResearch.WordTrace tailWord_4344970 prefixEnd_4344970 2231058039365970518592853 := by
  unfold tailWord_4344970
  simp only [CollatzResearch.WordTrace]
  refine ⟨39618518767230806660638091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105649383379282151095034909 39618518767230806660638091)
  ·
    refine ⟨59427778150846209990957137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39618518767230806660638091 59427778150846209990957137)
    ·
      refine ⟨44570833613134657493217853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59427778150846209990957137 44570833613134657493217853)
      ·
        refine ⟨16714062604925496559956695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44570833613134657493217853 16714062604925496559956695)
        ·
          refine ⟨25071093907388244839935043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16714062604925496559956695 25071093907388244839935043)
          ·
            refine ⟨37606640861082367259902565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25071093907388244839935043 37606640861082367259902565)
            ·
              refine ⟨7051245161452943861231731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 37606640861082367259902565 7051245161452943861231731)
              ·
                refine ⟨10576867742179415791847597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7051245161452943861231731 10576867742179415791847597)
                ·
                  refine ⟨3966325403317280921942849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10576867742179415791847597 3966325403317280921942849)
                  ·
                    refine ⟨2974744052487960691457137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3966325403317280921942849 2974744052487960691457137)
                    ·
                      refine ⟨2231058039365970518592853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2974744052487960691457137 2231058039365970518592853)
                      ·
                        rfl

theorem cell23_4344970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 4, 1, 3, 2, 2].length) (baseStart_4344970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4344970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4344970 prefixEnd_4344970 := by exact prefixLift 4344970
  have htrace : WordTrace (prefixWord ++ tailWord_4344970) baseStart_4344970 baseEnd_4344970 := by
    simpa [prefixWord, tailWord_4344970, baseEnd_4344970] using wordTrace_append hprefix tailTrace_4344970
  have hstable : (prefixWord ++ tailWord_4344970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4344970).length < 2 ^ (prefixWord ++ tailWord_4344970).sum := by decide
  have hdescent : baseEnd_4344970 < baseStart_4344970 := by decide
  rcases family_descends (prefixWord ++ tailWord_4344970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4344983 : List Nat := [1, 1, 3, 3, 3, 3, 1, 1, 1, 2, 4]
def baseStart_4344983 : Nat := 118140960795 + 4344983 * 2 ^ 59
def prefixEnd_4344983 : Nat := 4983230072969 + 3 ^ 40 * 4344983 * 2
def baseEnd_4344983 : Nat := 2231064714614478967730293

theorem tailTrace_4344983 : CollatzResearch.WordTrace tailWord_4344983 prefixEnd_4344983 2231064714614478967730293 := by
  unfold tailWord_4344983
  simp only [CollatzResearch.WordTrace]
  refine ⟨158474549217876129862775603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105649699478584086575183735 158474549217876129862775603)
  ·
    refine ⟨237711823826814194794163405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158474549217876129862775603 237711823826814194794163405)
    ·
      refine ⟨89141933935055323047811277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 237711823826814194794163405 89141933935055323047811277)
      ·
        refine ⟨33428225225645746142929229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 89141933935055323047811277 33428225225645746142929229)
        ·
          refine ⟨12535584459617154803598461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33428225225645746142929229 12535584459617154803598461)
          ·
            refine ⟨4700844172356433051349423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12535584459617154803598461 4700844172356433051349423)
            ·
              refine ⟨7051266258534649577024135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4700844172356433051349423 7051266258534649577024135)
              ·
                refine ⟨10576899387801974365536203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7051266258534649577024135 10576899387801974365536203)
                ·
                  refine ⟨15865349081702961548304305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10576899387801974365536203 15865349081702961548304305)
                  ·
                    refine ⟨11899011811277221161228229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15865349081702961548304305 11899011811277221161228229)
                    ·
                      refine ⟨2231064714614478967730293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11899011811277221161228229 2231064714614478967730293)
                      ·
                        rfl

theorem cell23_4344983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 3, 1, 1, 1, 2, 4].length) (baseStart_4344983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4344983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4344983 prefixEnd_4344983 := by exact prefixLift 4344983
  have htrace : WordTrace (prefixWord ++ tailWord_4344983) baseStart_4344983 baseEnd_4344983 := by
    simpa [prefixWord, tailWord_4344983, baseEnd_4344983] using wordTrace_append hprefix tailTrace_4344983
  have hstable : (prefixWord ++ tailWord_4344983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4344983).length < 2 ^ (prefixWord ++ tailWord_4344983).sum := by decide
  have hdescent : baseEnd_4344983 < baseStart_4344983 := by decide
  rcases family_descends (prefixWord ++ tailWord_4344983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4344990 : List Nat := [4, 3, 1, 1, 2, 1, 1, 4, 1, 2, 3]
def baseStart_4344990 : Nat := 118140960795 + 4344990 * 2 ^ 59
def prefixEnd_4344990 : Nat := 4983230072969 + 3 ^ 40 * 4344990 * 2
def baseEnd_4344990 : Nat := 2231068308979060440342761

theorem tailTrace_4344990 : CollatzResearch.WordTrace tailWord_4344990 prefixEnd_4344990 2231068308979060440342761 := by
  unfold tailWord_4344990
  simp only [CollatzResearch.WordTrace]
  refine ⟨19809350566106346257285053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 105649869685900513372186949 19809350566106346257285053)
  ·
    refine ⟨7428506462289879846481895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19809350566106346257285053 7428506462289879846481895)
    ·
      refine ⟨11142759693434819769722843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7428506462289879846481895 11142759693434819769722843)
      ·
        refine ⟨16714139540152229654584265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11142759693434819769722843 16714139540152229654584265)
        ·
          refine ⟨12535604655114172240938199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16714139540152229654584265 12535604655114172240938199)
          ·
            refine ⟨18803406982671258361407299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12535604655114172240938199 18803406982671258361407299)
            ·
              refine ⟨28205110474006887542110949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18803406982671258361407299 28205110474006887542110949)
              ·
                refine ⟨5288458213876291414145803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28205110474006887542110949 5288458213876291414145803)
                ·
                  refine ⟨7932687320814437121218705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5288458213876291414145803 7932687320814437121218705)
                  ·
                    refine ⟨5949515490610827840914029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7932687320814437121218705 5949515490610827840914029)
                    ·
                      refine ⟨2231068308979060440342761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5949515490610827840914029 2231068308979060440342761)
                      ·
                        rfl

theorem cell23_4344990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 1, 4, 1, 2, 3].length) (baseStart_4344990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4344990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4344990 prefixEnd_4344990 := by exact prefixLift 4344990
  have htrace : WordTrace (prefixWord ++ tailWord_4344990) baseStart_4344990 baseEnd_4344990 := by
    simpa [prefixWord, tailWord_4344990, baseEnd_4344990] using wordTrace_append hprefix tailTrace_4344990
  have hstable : (prefixWord ++ tailWord_4344990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4344990).length < 2 ^ (prefixWord ++ tailWord_4344990).sum := by decide
  have hdescent : baseEnd_4344990 < baseStart_4344990 := by decide
  rcases family_descends (prefixWord ++ tailWord_4344990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4345019 : List Nat := [1, 1, 1, 1, 1, 2, 4, 4, 2, 6]
def baseStart_4345019 : Nat := 118140960795 + 4345019 * 2 ^ 59
def prefixEnd_4345019 : Nat := 4983230072969 + 3 ^ 40 * 4345019 * 2
def baseEnd_4345019 : Nat := 743694399972680275626709

theorem tailTrace_4345019 : CollatzResearch.WordTrace tailWord_4345019 prefixEnd_4345019 743694399972680275626709 := by
  unfold tailWord_4345019
  simp only [CollatzResearch.WordTrace]
  refine ⟨158475862245745708011086111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105650574830497138674057407 158475862245745708011086111)
  ·
    refine ⟨237713793368618562016629167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158475862245745708011086111 237713793368618562016629167)
    ·
      refine ⟨356570690052927843024943751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 237713793368618562016629167 356570690052927843024943751)
      ·
        refine ⟨534856035079391764537415627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 356570690052927843024943751 534856035079391764537415627)
        ·
          refine ⟨802284052619087646806123441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 534856035079391764537415627 802284052619087646806123441)
          ·
            refine ⟨601713039464315735104592581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 802284052619087646806123441 601713039464315735104592581)
            ·
              refine ⟨112821194899559200332111109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 601713039464315735104592581 112821194899559200332111109)
              ·
                refine ⟨21153974043667350062270833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 112821194899559200332111109 21153974043667350062270833)
                ·
                  refine ⟨15865480532750512546703125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21153974043667350062270833 15865480532750512546703125)
                  ·
                    refine ⟨743694399972680275626709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15865480532750512546703125 743694399972680275626709)
                    ·
                      rfl

theorem cell23_4345019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 4, 2, 6].length) (baseStart_4345019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4345019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4345019 prefixEnd_4345019 := by exact prefixLift 4345019
  have htrace : WordTrace (prefixWord ++ tailWord_4345019) baseStart_4345019 baseEnd_4345019 := by
    simpa [prefixWord, tailWord_4345019, baseEnd_4345019] using wordTrace_append hprefix tailTrace_4345019
  have hstable : (prefixWord ++ tailWord_4345019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4345019).length < 2 ^ (prefixWord ++ tailWord_4345019).sum := by decide
  have hdescent : baseEnd_4345019 < baseStart_4345019 := by decide
  rcases family_descends (prefixWord ++ tailWord_4345019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4345029 : List Nat := [1, 3, 1, 1, 1, 1, 3, 1, 3, 3, 5]
def baseStart_4345029 : Nat := 118140960795 + 4345029 * 2 ^ 59
def prefixEnd_4345029 : Nat := 4983230072969 + 3 ^ 40 * 4345029 * 2
def baseEnd_4345029 : Nat := 2231088334724585787755081

theorem tailTrace_4345029 : CollatzResearch.WordTrace tailWord_4345029 prefixEnd_4345029 2231088334724585787755081 := by
  unfold tailWord_4345029
  simp only [CollatzResearch.WordTrace]
  refine ⟨158476226975709479718950141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105650817983806319812633427 158476226975709479718950141)
  ·
    refine ⟨59428585115891054894606303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 158476226975709479718950141 59428585115891054894606303)
    ·
      refine ⟨89142877673836582341909455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59428585115891054894606303 89142877673836582341909455)
      ·
        refine ⟨133714316510754873512864183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89142877673836582341909455 133714316510754873512864183)
        ·
          refine ⟨200571474766132310269296275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 133714316510754873512864183 200571474766132310269296275)
          ·
            refine ⟨300857212149198465403944413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 200571474766132310269296275 300857212149198465403944413)
            ·
              refine ⟨112821454555949424526479155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 300857212149198465403944413 112821454555949424526479155)
              ·
                refine ⟨169232181833924136789718733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 112821454555949424526479155 169232181833924136789718733)
                ·
                  refine ⟨63462068187721551296144525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 169232181833924136789718733 63462068187721551296144525)
                  ·
                    refine ⟨23798275570395581736054197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 63462068187721551296144525 23798275570395581736054197)
                    ·
                      refine ⟨2231088334724585787755081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23798275570395581736054197 2231088334724585787755081)
                      ·
                        rfl

theorem cell23_4345029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 1, 3, 3, 5].length) (baseStart_4345029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4345029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4345029 prefixEnd_4345029 := by exact prefixLift 4345029
  have htrace : WordTrace (prefixWord ++ tailWord_4345029) baseStart_4345029 baseEnd_4345029 := by
    simpa [prefixWord, tailWord_4345029, baseEnd_4345029] using wordTrace_append hprefix tailTrace_4345029
  have hstable : (prefixWord ++ tailWord_4345029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4345029).length < 2 ^ (prefixWord ++ tailWord_4345029).sum := by decide
  have hdescent : baseEnd_4345029 < baseStart_4345029 := by decide
  rcases family_descends (prefixWord ++ tailWord_4345029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4345049 : List Nat := [1, 2, 1, 2, 3, 1, 1, 3, 9]
def baseStart_4345049 : Nat := 118140960795 + 4345049 * 2 ^ 59
def prefixEnd_4345049 : Nat := 4983230072969 + 3 ^ 40 * 4345049 * 2
def baseEnd_4345049 : Nat := 247899844926408412167221

theorem tailTrace_4345049 : CollatzResearch.WordTrace tailWord_4345049 prefixEnd_4345049 247899844926408412167221 := by
  unfold tailWord_4345049
  simp only [CollatzResearch.WordTrace]
  refine ⟨158476956435637023134678201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105651304290424682089785467 158476956435637023134678201)
  ·
    refine ⟨118857717326727767351008651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 158476956435637023134678201 118857717326727767351008651)
    ·
      refine ⟨178286575990091651026512977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118857717326727767351008651 178286575990091651026512977)
      ·
        refine ⟨133714931992568738269884733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 178286575990091651026512977 133714931992568738269884733)
        ·
          refine ⟨50143099497213276851206775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 133714931992568738269884733 50143099497213276851206775)
          ·
            refine ⟨75214649245819915276810163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50143099497213276851206775 75214649245819915276810163)
            ·
              refine ⟨112821973868729872915215245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75214649245819915276810163 112821973868729872915215245)
              ·
                refine ⟨42308240200773702343205717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 112821973868729872915215245 42308240200773702343205717)
                ·
                  refine ⟨247899844926408412167221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 42308240200773702343205717 247899844926408412167221)
                  ·
                    rfl

theorem cell23_4345049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 3, 9].length) (baseStart_4345049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4345049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4345049 prefixEnd_4345049 := by exact prefixLift 4345049
  have htrace : WordTrace (prefixWord ++ tailWord_4345049) baseStart_4345049 baseEnd_4345049 := by
    simpa [prefixWord, tailWord_4345049, baseEnd_4345049] using wordTrace_append hprefix tailTrace_4345049
  have hstable : (prefixWord ++ tailWord_4345049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4345049).length < 2 ^ (prefixWord ++ tailWord_4345049).sum := by decide
  have hdescent : baseEnd_4345049 < baseStart_4345049 := by decide
  rcases family_descends (prefixWord ++ tailWord_4345049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4345090 : List Nat := [3, 4, 1, 1, 3, 1, 1, 1, 2, 2, 4]
def baseStart_4345090 : Nat := 118140960795 + 4345090 * 2 ^ 59
def prefixEnd_4345090 : Nat := 4983230072969 + 3 ^ 40 * 4345090 * 2
def baseEnd_4345090 : Nat := 2231119657044510049092301

theorem tailTrace_4345090 : CollatzResearch.WordTrace tailWord_4345090 prefixEnd_4345090 2231119657044510049092301 := by
  unfold tailWord_4345090
  simp only [CollatzResearch.WordTrace]
  refine ⟨39619612957122121784230181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105652301218992324757947149 39619612957122121784230181)
  ·
    refine ⟨7428677429460397834543159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 39619612957122121784230181 7428677429460397834543159)
    ·
      refine ⟨11143016144190596751814739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7428677429460397834543159 11143016144190596751814739)
      ·
        refine ⟨16714524216285895127722109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11143016144190596751814739 16714524216285895127722109)
        ·
          refine ⟨6267946581107210672895791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16714524216285895127722109 6267946581107210672895791)
          ·
            refine ⟨9401919871660816009343687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6267946581107210672895791 9401919871660816009343687)
            ·
              refine ⟨14102879807491224014015531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9401919871660816009343687 14102879807491224014015531)
              ·
                refine ⟨21154319711236836021023297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14102879807491224014015531 21154319711236836021023297)
                ·
                  refine ⟨15865739783427627015767473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21154319711236836021023297 15865739783427627015767473)
                  ·
                    refine ⟨11899304837570720261825605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15865739783427627015767473 11899304837570720261825605)
                    ·
                      refine ⟨2231119657044510049092301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11899304837570720261825605 2231119657044510049092301)
                      ·
                        rfl

theorem cell23_4345090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 1, 1, 2, 2, 4].length) (baseStart_4345090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4345090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4345090 prefixEnd_4345090 := by exact prefixLift 4345090
  have htrace : WordTrace (prefixWord ++ tailWord_4345090) baseStart_4345090 baseEnd_4345090 := by
    simpa [prefixWord, tailWord_4345090, baseEnd_4345090] using wordTrace_append hprefix tailTrace_4345090
  have hstable : (prefixWord ++ tailWord_4345090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4345090).length < 2 ^ (prefixWord ++ tailWord_4345090).sum := by decide
  have hdescent : baseEnd_4345090 < baseStart_4345090 := by decide
  rcases family_descends (prefixWord ++ tailWord_4345090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4345146 : List Nat := [3, 1, 1, 1, 4, 1, 1, 2, 2, 1, 6]
def baseStart_4345146 : Nat := 118140960795 + 4345146 * 2 ^ 59
def prefixEnd_4345146 : Nat := 4983230072969 + 3 ^ 40 * 4345146 * 2
def baseEnd_4345146 : Nat := 2231148411961161829992043

theorem tailTrace_4345146 : CollatzResearch.WordTrace tailWord_4345146 prefixEnd_4345146 2231148411961161829992043 := by
  unfold tailWord_4345146
  simp only [CollatzResearch.WordTrace]
  refine ⟨39620123579071402175239823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105653662877523739133972861 39620123579071402175239823)
  ·
    refine ⟨59430185368607103262859735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39620123579071402175239823 59430185368607103262859735)
    ·
      refine ⟨89145278052910654894289603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59430185368607103262859735 89145278052910654894289603)
      ·
        refine ⟨133717917079365982341434405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89145278052910654894289603 133717917079365982341434405)
        ·
          refine ⟨25072109452381121689018951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 133717917079365982341434405 25072109452381121689018951)
          ·
            refine ⟨37608164178571682533528427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25072109452381121689018951 37608164178571682533528427)
            ·
              refine ⟨56412246267857523800292641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37608164178571682533528427 56412246267857523800292641)
              ·
                refine ⟨42309184700893142850219481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 56412246267857523800292641 42309184700893142850219481)
                ·
                  refine ⟨31731888525669857137664611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 42309184700893142850219481 31731888525669857137664611)
                  ·
                    refine ⟨47597832788504785706496917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 31731888525669857137664611 47597832788504785706496917)
                    ·
                      refine ⟨2231148411961161829992043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 47597832788504785706496917 2231148411961161829992043)
                      ·
                        rfl

theorem cell23_4345146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 2, 2, 1, 6].length) (baseStart_4345146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4345146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4345146 prefixEnd_4345146 := by exact prefixLift 4345146
  have htrace : WordTrace (prefixWord ++ tailWord_4345146) baseStart_4345146 baseEnd_4345146 := by
    simpa [prefixWord, tailWord_4345146, baseEnd_4345146] using wordTrace_append hprefix tailTrace_4345146
  have hstable : (prefixWord ++ tailWord_4345146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4345146).length < 2 ^ (prefixWord ++ tailWord_4345146).sum := by decide
  have hdescent : baseEnd_4345146 < baseStart_4345146 := by decide
  rcases family_descends (prefixWord ++ tailWord_4345146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4345150 : List Nat := [4, 2, 1, 2, 1, 1, 1, 3, 2, 4, 2]
def baseStart_4345150 : Nat := 118140960795 + 4345150 * 2 ^ 59
def prefixEnd_4345150 : Nat := 4983230072969 + 3 ^ 40 * 4345150 * 2
def baseEnd_4345150 : Nat := 2231150465883779814342025

theorem tailTrace_4345150 : CollatzResearch.WordTrace tailWord_4345150 prefixEnd_4345150 2231150465883779814342025 := by
  unfold tailWord_4345150
  simp only [CollatzResearch.WordTrace]
  refine ⟨19810080026033889673013113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 105653760138847411589403269 19810080026033889673013113)
  ·
    refine ⟨14857560019525417254759835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19810080026033889673013113 14857560019525417254759835)
    ·
      refine ⟨22286340029288125882139753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14857560019525417254759835 22286340029288125882139753)
      ·
        refine ⟨16714755021966094411604815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22286340029288125882139753 16714755021966094411604815)
        ·
          refine ⟨25072132532949141617407223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16714755021966094411604815 25072132532949141617407223)
          ·
            refine ⟨37608198799423712426110835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25072132532949141617407223 37608198799423712426110835)
            ·
              refine ⟨56412298199135568639166253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37608198799423712426110835 56412298199135568639166253)
              ·
                refine ⟨21154611824675838239687345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 56412298199135568639166253 21154611824675838239687345)
                ·
                  refine ⟨15865958868506878679765509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21154611824675838239687345 15865958868506878679765509)
                  ·
                    refine ⟨2974867287845039752456033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15865958868506878679765509 2974867287845039752456033)
                    ·
                      refine ⟨2231150465883779814342025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2974867287845039752456033 2231150465883779814342025)
                      ·
                        rfl

theorem cell23_4345150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 3, 2, 4, 2].length) (baseStart_4345150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4345150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4345150 prefixEnd_4345150 := by exact prefixLift 4345150
  have htrace : WordTrace (prefixWord ++ tailWord_4345150) baseStart_4345150 baseEnd_4345150 := by
    simpa [prefixWord, tailWord_4345150, baseEnd_4345150] using wordTrace_append hprefix tailTrace_4345150
  have hstable : (prefixWord ++ tailWord_4345150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4345150).length < 2 ^ (prefixWord ++ tailWord_4345150).sum := by decide
  have hdescent : baseEnd_4345150 < baseStart_4345150 := by decide
  rcases family_descends (prefixWord ++ tailWord_4345150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4345193 : List Nat := [1, 2, 1, 1, 1, 3, 2, 2, 3, 5, 2]
def baseStart_4345193 : Nat := 118140960795 + 4345193 * 2 ^ 59
def prefixEnd_4345193 : Nat := 4983230072969 + 3 ^ 40 * 4345193 * 2
def baseEnd_4345193 : Nat := 2231172545551923146104327

theorem tailTrace_4345193 : CollatzResearch.WordTrace tailWord_4345193 prefixEnd_4345193 2231172545551923146104327 := by
  unfold tailWord_4345193
  simp only [CollatzResearch.WordTrace]
  refine ⟨158482208547115335727920233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105654805698076890485280155 158482208547115335727920233)
  ·
    refine ⟨118861656410336501795940175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 158482208547115335727920233 118861656410336501795940175)
    ·
      refine ⟨178292484615504752693910263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118861656410336501795940175 178292484615504752693910263)
      ·
        refine ⟨267438726923257129040865395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 178292484615504752693910263 267438726923257129040865395)
        ·
          refine ⟨401158090384885693561298093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 267438726923257129040865395 401158090384885693561298093)
          ·
            refine ⟨150434283894332135085486785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 401158090384885693561298093 150434283894332135085486785)
            ·
              refine ⟨112825712920749101314115089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 150434283894332135085486785 112825712920749101314115089)
              ·
                refine ⟨84619284690561825985586317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 112825712920749101314115089 84619284690561825985586317)
                ·
                  refine ⟨31732231758960684744594869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 84619284690561825985586317 31732231758960684744594869)
                  ·
                    refine ⟨2974896727402564194805769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 31732231758960684744594869 2974896727402564194805769)
                    ·
                      refine ⟨2231172545551923146104327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2974896727402564194805769 2231172545551923146104327)
                      ·
                        rfl

theorem cell23_4345193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 2, 3, 5, 2].length) (baseStart_4345193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4345193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4345193 prefixEnd_4345193 := by exact prefixLift 4345193
  have htrace : WordTrace (prefixWord ++ tailWord_4345193) baseStart_4345193 baseEnd_4345193 := by
    simpa [prefixWord, tailWord_4345193, baseEnd_4345193] using wordTrace_append hprefix tailTrace_4345193
  have hstable : (prefixWord ++ tailWord_4345193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4345193).length < 2 ^ (prefixWord ++ tailWord_4345193).sum := by decide
  have hdescent : baseEnd_4345193 < baseStart_4345193 := by decide
  rcases family_descends (prefixWord ++ tailWord_4345193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4345194 : List Nat := [3, 1, 3, 3, 3, 1, 1, 1, 3, 4]
def baseStart_4345194 : Nat := 118140960795 + 4345194 * 2 ^ 59
def prefixEnd_4345194 : Nat := 4983230072969 + 3 ^ 40 * 4345194 * 2
def baseEnd_4345194 : Nat := 743724353010859214063941

theorem tailTrace_4345194 : CollatzResearch.WordTrace tailWord_4345194 prefixEnd_4345194 743724353010859214063941 := by
  unfold tailWord_4345194
  simp only [CollatzResearch.WordTrace]
  refine ⟨39620561255027928224676659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105654830013407808599137757 39620561255027928224676659)
  ·
    refine ⟨59430841882541892337014989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39620561255027928224676659 59430841882541892337014989)
    ·
      refine ⟨22286565705953209626380621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59430841882541892337014989 22286565705953209626380621)
      ·
        refine ⟨8357462139732453609892733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22286565705953209626380621 8357462139732453609892733)
        ·
          refine ⟨3134048302399670103709775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8357462139732453609892733 3134048302399670103709775)
          ·
            refine ⟨4701072453599505155564663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3134048302399670103709775 4701072453599505155564663)
            ·
              refine ⟨7051608680399257733346995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4701072453599505155564663 7051608680399257733346995)
              ·
                refine ⟨10577413020598886600020493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7051608680399257733346995 10577413020598886600020493)
                ·
                  refine ⟨3966529882724582475007685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10577413020598886600020493 3966529882724582475007685)
                  ·
                    refine ⟨743724353010859214063941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3966529882724582475007685 743724353010859214063941)
                    ·
                      rfl

theorem cell23_4345194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 3, 1, 1, 1, 3, 4].length) (baseStart_4345194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4345194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4345194 prefixEnd_4345194 := by exact prefixLift 4345194
  have htrace : WordTrace (prefixWord ++ tailWord_4345194) baseStart_4345194 baseEnd_4345194 := by
    simpa [prefixWord, tailWord_4345194, baseEnd_4345194] using wordTrace_append hprefix tailTrace_4345194
  have hstable : (prefixWord ++ tailWord_4345194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4345194).length < 2 ^ (prefixWord ++ tailWord_4345194).sum := by decide
  have hdescent : baseEnd_4345194 < baseStart_4345194 := by decide
  rcases family_descends (prefixWord ++ tailWord_4345194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4345216 : List Nat := [2, 1, 1, 2, 1, 2, 1, 2, 5, 6]
def baseStart_4345216 : Nat := 118140960795 + 4345216 * 2 ^ 59
def prefixEnd_4345216 : Nat := 4983230072969 + 3 ^ 40 * 4345216 * 2
def baseEnd_4345216 : Nat := 743728118535658852038907

theorem tailTrace_4345216 : CollatzResearch.WordTrace tailWord_4345216 prefixEnd_4345216 743728118535658852038907 := by
  unfold tailWord_4345216
  simp only [CollatzResearch.WordTrace]
  refine ⟨79241523713016005328003751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105655364950688007104005001 79241523713016005328003751)
  ·
    refine ⟨118862285569524007992005627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79241523713016005328003751 118862285569524007992005627)
    ·
      refine ⟨178293428354286011988008441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118862285569524007992005627 178293428354286011988008441)
      ·
        refine ⟨133720071265714508991006331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 178293428354286011988008441 133720071265714508991006331)
        ·
          refine ⟨200580106898571763486509497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 133720071265714508991006331 200580106898571763486509497)
          ·
            refine ⟨150435080173928822614882123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 200580106898571763486509497 150435080173928822614882123)
            ·
              refine ⟨225652620260893233922323185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 150435080173928822614882123 225652620260893233922323185)
              ·
                refine ⟨169239465195669925441742389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 225652620260893233922323185 169239465195669925441742389)
                ·
                  refine ⟨15866199862094055510163349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 169239465195669925441742389 15866199862094055510163349)
                  ·
                    refine ⟨743728118535658852038907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15866199862094055510163349 743728118535658852038907)
                    ·
                      rfl

theorem cell23_4345216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 2, 5, 6].length) (baseStart_4345216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4345216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4345216 prefixEnd_4345216 := by exact prefixLift 4345216
  have htrace : WordTrace (prefixWord ++ tailWord_4345216) baseStart_4345216 baseEnd_4345216 := by
    simpa [prefixWord, tailWord_4345216, baseEnd_4345216] using wordTrace_append hprefix tailTrace_4345216
  have hstable : (prefixWord ++ tailWord_4345216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4345216).length < 2 ^ (prefixWord ++ tailWord_4345216).sum := by decide
  have hdescent : baseEnd_4345216 < baseStart_4345216 := by decide
  rcases family_descends (prefixWord ++ tailWord_4345216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4345220 : List Nat := [2, 3, 2, 1, 1, 3, 3, 2, 1, 5]
def baseStart_4345220 : Nat := 118140960795 + 4345220 * 2 ^ 59
def prefixEnd_4345220 : Nat := 4983230072969 + 3 ^ 40 * 4345220 * 2
def baseEnd_4345220 : Nat := 743728803176531513488901

theorem tailTrace_4345220 : CollatzResearch.WordTrace tailWord_4345220 prefixEnd_4345220 743728803176531513488901 := by
  unfold tailWord_4345220
  simp only [CollatzResearch.WordTrace]
  refine ⟨79241596659008759669576557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105655462212011679559435409 79241596659008759669576557)
  ·
    refine ⟨29715598747128284876091209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79241596659008759669576557 29715598747128284876091209)
    ·
      refine ⟨22286699060346213657068407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29715598747128284876091209 22286699060346213657068407)
      ·
        refine ⟨33430048590519320485602611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22286699060346213657068407 33430048590519320485602611)
        ·
          refine ⟨50145072885778980728403917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33430048590519320485602611 50145072885778980728403917)
          ·
            refine ⟨18804402332167117773151469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50145072885778980728403917 18804402332167117773151469)
            ·
              refine ⟨7051650874562669164931801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18804402332167117773151469 7051650874562669164931801)
              ·
                refine ⟨5288738155922001873698851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7051650874562669164931801 5288738155922001873698851)
                ·
                  refine ⟨7933107233883002810548277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5288738155922001873698851 7933107233883002810548277)
                  ·
                    refine ⟨743728803176531513488901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7933107233883002810548277 743728803176531513488901)
                    ·
                      rfl

theorem cell23_4345220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 3, 2, 1, 5].length) (baseStart_4345220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4345220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4345220 prefixEnd_4345220 := by exact prefixLift 4345220
  have htrace : WordTrace (prefixWord ++ tailWord_4345220) baseStart_4345220 baseEnd_4345220 := by
    simpa [prefixWord, tailWord_4345220, baseEnd_4345220] using wordTrace_append hprefix tailTrace_4345220
  have hstable : (prefixWord ++ tailWord_4345220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4345220).length < 2 ^ (prefixWord ++ tailWord_4345220).sum := by decide
  have hdescent : baseEnd_4345220 < baseStart_4345220 := by decide
  rcases family_descends (prefixWord ++ tailWord_4345220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4345290 : List Nat := [3, 1, 2, 1, 2, 3, 2, 2, 1, 3, 3]
def baseStart_4345290 : Nat := 118140960795 + 4345290 * 2 ^ 59
def prefixEnd_4345290 : Nat := 4983230072969 + 3 ^ 40 * 4345290 * 2
def baseEnd_4345290 : Nat := 2231222353175409266591381

theorem tailTrace_4345290 : CollatzResearch.WordTrace tailWord_4345290 prefixEnd_4345290 2231222353175409266591381 := by
  unfold tailWord_4345290
  simp only [CollatzResearch.WordTrace]
  refine ⟨39621436606940980323550331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105657164285175947529467549 39621436606940980323550331)
  ·
    refine ⟨59432154910411470485325497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39621436606940980323550331 59432154910411470485325497)
    ·
      refine ⟨44574116182808602863994123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59432154910411470485325497 44574116182808602863994123)
      ·
        refine ⟨66861174274212904295991185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44574116182808602863994123 66861174274212904295991185)
        ·
          refine ⟨50145880705659678221993389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66861174274212904295991185 50145880705659678221993389)
          ·
            refine ⟨18804705264622379333247521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50145880705659678221993389 18804705264622379333247521)
            ·
              refine ⟨14103528948466784499935641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18804705264622379333247521 14103528948466784499935641)
              ·
                refine ⟨10577646711350088374951731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14103528948466784499935641 10577646711350088374951731)
                ·
                  refine ⟨15866470067025132562427597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10577646711350088374951731 15866470067025132562427597)
                  ·
                    refine ⟨5949926275134424710910349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15866470067025132562427597 5949926275134424710910349)
                    ·
                      refine ⟨2231222353175409266591381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5949926275134424710910349 2231222353175409266591381)
                      ·
                        rfl

theorem cell23_4345290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 2, 2, 1, 3, 3].length) (baseStart_4345290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4345290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4345290 prefixEnd_4345290 := by exact prefixLift 4345290
  have htrace : WordTrace (prefixWord ++ tailWord_4345290) baseStart_4345290 baseEnd_4345290 := by
    simpa [prefixWord, tailWord_4345290, baseEnd_4345290] using wordTrace_append hprefix tailTrace_4345290
  have hstable : (prefixWord ++ tailWord_4345290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4345290).length < 2 ^ (prefixWord ++ tailWord_4345290).sum := by decide
  have hdescent : baseEnd_4345290 < baseStart_4345290 := by decide
  rcases family_descends (prefixWord ++ tailWord_4345290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4345334 : List Nat := [5, 1, 1, 1, 2, 2, 1, 4, 1, 3, 2]
def baseStart_4345334 : Nat := 118140960795 + 4345334 * 2 ^ 59
def prefixEnd_4345334 : Nat := 4983230072969 + 3 ^ 40 * 4345334 * 2
def baseEnd_4345334 : Nat := 2231244946324207094441179

theorem tailTrace_4345334 : CollatzResearch.WordTrace tailWord_4345334 prefixEnd_4345334 2231244946324207094441179 := by
  unfold tailWord_4345334
  simp only [CollatzResearch.WordTrace]
  refine ⟨9905459452475282300550191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 105658234159736344539202037 9905459452475282300550191)
  ·
    refine ⟨14858189178712923450825287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9905459452475282300550191 14858189178712923450825287)
    ·
      refine ⟨22287283768069385176237931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14858189178712923450825287 22287283768069385176237931)
      ·
        refine ⟨33430925652104077764356897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22287283768069385176237931 33430925652104077764356897)
        ·
          refine ⟨25073194239078058323267673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33430925652104077764356897 25073194239078058323267673)
          ·
            refine ⟨18804895679308543742450755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25073194239078058323267673 18804895679308543742450755)
            ·
              refine ⟨28207343518962815613676133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18804895679308543742450755 28207343518962815613676133)
              ·
                refine ⟨5288876909805527927564275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28207343518962815613676133 5288876909805527927564275)
                ·
                  refine ⟨7933315364708291891346413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5288876909805527927564275 7933315364708291891346413)
                  ·
                    refine ⟨2974993261765609459254905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7933315364708291891346413 2974993261765609459254905)
                    ·
                      refine ⟨2231244946324207094441179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2974993261765609459254905 2231244946324207094441179)
                      ·
                        rfl

theorem cell23_4345334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 1, 4, 1, 3, 2].length) (baseStart_4345334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4345334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4345334 prefixEnd_4345334 := by exact prefixLift 4345334
  have htrace : WordTrace (prefixWord ++ tailWord_4345334) baseStart_4345334 baseEnd_4345334 := by
    simpa [prefixWord, tailWord_4345334, baseEnd_4345334] using wordTrace_append hprefix tailTrace_4345334
  have hstable : (prefixWord ++ tailWord_4345334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4345334).length < 2 ^ (prefixWord ++ tailWord_4345334).sum := by decide
  have hdescent : baseEnd_4345334 < baseStart_4345334 := by decide
  rcases family_descends (prefixWord ++ tailWord_4345334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4345342 : List Nat := [4, 2, 2, 3, 2, 1, 1, 3, 1, 2, 2]
def baseStart_4345342 : Nat := 118140960795 + 4345342 * 2 ^ 59
def prefixEnd_4345342 : Nat := 4983230072969 + 3 ^ 40 * 4345342 * 2
def baseEnd_4345342 : Nat := 2231249054169443063141143

theorem tailTrace_4345342 : CollatzResearch.WordTrace tailWord_4345342 prefixEnd_4345342 2231249054169443063141143 := by
  unfold tailWord_4345342
  simp only [CollatzResearch.WordTrace]
  refine ⟨19810955377946941771886785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 105658428682383689450062853 19810955377946941771886785)
  ·
    refine ⟨14858216533460206328915089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19810955377946941771886785 14858216533460206328915089)
    ·
      refine ⟨11143662400095154746686317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14858216533460206328915089 11143662400095154746686317)
      ·
        refine ⟨4178873400035683030007369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11143662400095154746686317 4178873400035683030007369)
        ·
          refine ⟨3134155050026762272505527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4178873400035683030007369 3134155050026762272505527)
          ·
            refine ⟨4701232575040143408758291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3134155050026762272505527 4701232575040143408758291)
            ·
              refine ⟨7051848862560215113137437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4701232575040143408758291 7051848862560215113137437)
              ·
                refine ⟨2644443323460080667426539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7051848862560215113137437 2644443323460080667426539)
                ·
                  refine ⟨3966664985190121001139809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2644443323460080667426539 3966664985190121001139809)
                  ·
                    refine ⟨2974998738892590750854857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3966664985190121001139809 2974998738892590750854857)
                    ·
                      refine ⟨2231249054169443063141143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2974998738892590750854857 2231249054169443063141143)
                      ·
                        rfl

theorem cell23_4345342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 2, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 2, 1, 1, 3, 1, 2, 2].length) (baseStart_4345342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4345342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4345342 prefixEnd_4345342 := by exact prefixLift 4345342
  have htrace : WordTrace (prefixWord ++ tailWord_4345342) baseStart_4345342 baseEnd_4345342 := by
    simpa [prefixWord, tailWord_4345342, baseEnd_4345342] using wordTrace_append hprefix tailTrace_4345342
  have hstable : (prefixWord ++ tailWord_4345342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4345342).length < 2 ^ (prefixWord ++ tailWord_4345342).sum := by decide
  have hdescent : baseEnd_4345342 < baseStart_4345342 := by decide
  rcases family_descends (prefixWord ++ tailWord_4345342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4345343 : List Nat := [1, 1, 2, 2, 1, 2, 2, 2, 4, 2, 4]
def baseStart_4345343 : Nat := 118140960795 + 4345343 * 2 ^ 59
def prefixEnd_4345343 : Nat := 4983230072969 + 3 ^ 40 * 4345343 * 2
def baseEnd_4345343 : Nat := 2231249567650097559228637

theorem tailTrace_4345343 : CollatzResearch.WordTrace tailWord_4345343 prefixEnd_4345343 2231249567650097559228637 := by
  unfold tailWord_4345343
  simp only [CollatzResearch.WordTrace]
  refine ⟨158487679496571911345880683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105658452997714607563920455 158487679496571911345880683)
  ·
    refine ⟨237731519244857867018821025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158487679496571911345880683 237731519244857867018821025)
    ·
      refine ⟨178298639433643400264115769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 237731519244857867018821025 178298639433643400264115769)
      ·
        refine ⟨133723979575232550198086827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 178298639433643400264115769 133723979575232550198086827)
        ·
          refine ⟨200585969362848825297130241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 133723979575232550198086827 200585969362848825297130241)
          ·
            refine ⟨150439477022136618972847681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 200585969362848825297130241 150439477022136618972847681)
            ·
              refine ⟨112829607766602464229635761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 150439477022136618972847681 112829607766602464229635761)
              ·
                refine ⟨84622205824951848172226821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 112829607766602464229635761 84622205824951848172226821)
                ·
                  refine ⟨15866663592178471532292529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 84622205824951848172226821 15866663592178471532292529)
                  ·
                    refine ⟨11899997694133853649219397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15866663592178471532292529 11899997694133853649219397)
                    ·
                      refine ⟨2231249567650097559228637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11899997694133853649219397 2231249567650097559228637)
                      ·
                        rfl

theorem cell23_4345343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 2, 4, 2, 4].length) (baseStart_4345343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4345343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4345343 prefixEnd_4345343 := by exact prefixLift 4345343
  have htrace : WordTrace (prefixWord ++ tailWord_4345343) baseStart_4345343 baseEnd_4345343 := by
    simpa [prefixWord, tailWord_4345343, baseEnd_4345343] using wordTrace_append hprefix tailTrace_4345343
  have hstable : (prefixWord ++ tailWord_4345343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4345343).length < 2 ^ (prefixWord ++ tailWord_4345343).sum := by decide
  have hdescent : baseEnd_4345343 < baseStart_4345343 := by decide
  rcases family_descends (prefixWord ++ tailWord_4345343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4345393 : List Nat := [1, 2, 2, 3, 1, 1, 1, 1, 3, 1, 7]
def baseStart_4345393 : Nat := 118140960795 + 4345393 * 2 ^ 59
def prefixEnd_4345393 : Nat := 4983230072969 + 3 ^ 40 * 4345393 * 2
def baseEnd_4345393 : Nat := 2231275241682822363603407

theorem tailTrace_4345393 : CollatzResearch.WordTrace tailWord_4345393 prefixEnd_4345393 2231275241682822363603407 := by
  unfold tailWord_4345393
  simp only [CollatzResearch.WordTrace]
  refine ⟨158489503146390769885200833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105659668764260513256800555 158489503146390769885200833)
  ·
    refine ⟨118867127359793077413900625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 158489503146390769885200833 118867127359793077413900625)
    ·
      refine ⟨89150345519844808060425469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 118867127359793077413900625 89150345519844808060425469)
      ·
        refine ⟨33431379569941803022659551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 89150345519844808060425469 33431379569941803022659551)
        ·
          refine ⟨50147069354912704533989327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33431379569941803022659551 50147069354912704533989327)
          ·
            refine ⟨75220604032369056800983991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50147069354912704533989327 75220604032369056800983991)
            ·
              refine ⟨112830906048553585201475987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75220604032369056800983991 112830906048553585201475987)
              ·
                refine ⟨169246359072830377802213981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 112830906048553585201475987 169246359072830377802213981)
                ·
                  refine ⟨63467384652311391675830243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 169246359072830377802213981 63467384652311391675830243)
                  ·
                    refine ⟨95201076978467087513745365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 63467384652311391675830243 95201076978467087513745365)
                    ·
                      refine ⟨2231275241682822363603407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 95201076978467087513745365 2231275241682822363603407)
                      ·
                        rfl

theorem cell23_4345393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 1, 3, 1, 7].length) (baseStart_4345393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4345393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4345393 prefixEnd_4345393 := by exact prefixLift 4345393
  have htrace : WordTrace (prefixWord ++ tailWord_4345393) baseStart_4345393 baseEnd_4345393 := by
    simpa [prefixWord, tailWord_4345393, baseEnd_4345393] using wordTrace_append hprefix tailTrace_4345393
  have hstable : (prefixWord ++ tailWord_4345393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4345393).length < 2 ^ (prefixWord ++ tailWord_4345393).sum := by decide
  have hdescent : baseEnd_4345393 < baseStart_4345393 := by decide
  rcases family_descends (prefixWord ++ tailWord_4345393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4345400 : List Nat := [2, 1, 2, 1, 4, 2, 1, 3, 2, 5]
def baseStart_4345400 : Nat := 118140960795 + 4345400 * 2 ^ 59
def prefixEnd_4345400 : Nat := 4983230072969 + 3 ^ 40 * 4345400 * 2
def baseEnd_4345400 : Nat := 743759612015801278738625

theorem tailTrace_4345400 : CollatzResearch.WordTrace tailWord_4345400 prefixEnd_4345400 743759612015801278738625 := by
  unfold tailWord_4345400
  simp only [CollatzResearch.WordTrace]
  refine ⟨79244879228682705040352827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105659838971576940053803769 79244879228682705040352827)
  ·
    refine ⟨118867318843024057560529241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79244879228682705040352827 118867318843024057560529241)
    ·
      refine ⟨89150489132268043170396931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 118867318843024057560529241 89150489132268043170396931)
      ·
        refine ⟨133725733698402064755595397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89150489132268043170396931 133725733698402064755595397)
        ·
          refine ⟨25073575068450387141674137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 133725733698402064755595397 25073575068450387141674137)
          ·
            refine ⟨18805181301337790356255603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25073575068450387141674137 18805181301337790356255603)
            ·
              refine ⟨28207771952006685534383405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18805181301337790356255603 28207771952006685534383405)
              ·
                refine ⟨10577914482002507075393777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28207771952006685534383405 10577914482002507075393777)
                ·
                  refine ⟨7933435861501880306545333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10577914482002507075393777 7933435861501880306545333)
                  ·
                    refine ⟨743759612015801278738625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7933435861501880306545333 743759612015801278738625)
                    ·
                      rfl

theorem cell23_4345400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 1, 3, 2, 5].length) (baseStart_4345400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4345400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4345400 prefixEnd_4345400 := by exact prefixLift 4345400
  have htrace : WordTrace (prefixWord ++ tailWord_4345400) baseStart_4345400 baseEnd_4345400 := by
    simpa [prefixWord, tailWord_4345400, baseEnd_4345400] using wordTrace_append hprefix tailTrace_4345400
  have hstable : (prefixWord ++ tailWord_4345400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4345400).length < 2 ^ (prefixWord ++ tailWord_4345400).sum := by decide
  have hdescent : baseEnd_4345400 < baseStart_4345400 := by decide
  rcases family_descends (prefixWord ++ tailWord_4345400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4345423 : List Nat := [1, 1, 2, 1, 1, 2, 3, 1, 1, 5, 5]
def baseStart_4345423 : Nat := 118140960795 + 4345423 * 2 ^ 59
def prefixEnd_4345423 : Nat := 4983230072969 + 3 ^ 40 * 4345423 * 2
def baseEnd_4345423 : Nat := 2231290646102457246228269

theorem tailTrace_4345423 : CollatzResearch.WordTrace tailWord_4345423 prefixEnd_4345423 2231290646102457246228269 := by
  unfold tailWord_4345423
  simp only [CollatzResearch.WordTrace]
  refine ⟨158490597336282085008792923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105660398224188056672528615 158490597336282085008792923)
  ·
    refine ⟨237735896004423127513189385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158490597336282085008792923 237735896004423127513189385)
    ·
      refine ⟨178301922003317345634892039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 237735896004423127513189385 178301922003317345634892039)
      ·
        refine ⟨267452883004976018452338059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 178301922003317345634892039 267452883004976018452338059)
        ·
          refine ⟨401179324507464027678507089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 267452883004976018452338059 401179324507464027678507089)
          ·
            refine ⟨300884493380598020758880317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 401179324507464027678507089 300884493380598020758880317)
            ·
              refine ⟨112831685017724257784580119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 300884493380598020758880317 112831685017724257784580119)
              ·
                refine ⟨169247527526586386676870179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 112831685017724257784580119 169247527526586386676870179)
                ·
                  refine ⟨253871291289879580015305269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 169247527526586386676870179 253871291289879580015305269)
                  ·
                    refine ⟨23800433558426210626434869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 253871291289879580015305269 23800433558426210626434869)
                    ·
                      refine ⟨2231290646102457246228269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23800433558426210626434869 2231290646102457246228269)
                      ·
                        rfl

theorem cell23_4345423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 1, 1, 5, 5].length) (baseStart_4345423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4345423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4345423 prefixEnd_4345423 := by exact prefixLift 4345423
  have htrace : WordTrace (prefixWord ++ tailWord_4345423) baseStart_4345423 baseEnd_4345423 := by
    simpa [prefixWord, tailWord_4345423, baseEnd_4345423] using wordTrace_append hprefix tailTrace_4345423
  have hstable : (prefixWord ++ tailWord_4345423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4345423).length < 2 ^ (prefixWord ++ tailWord_4345423).sum := by decide
  have hdescent : baseEnd_4345423 < baseStart_4345423 := by decide
  rcases family_descends (prefixWord ++ tailWord_4345423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4345440 : List Nat := [2, 1, 1, 3, 2, 1, 1, 4, 1, 4, 3]
def baseStart_4345440 : Nat := 118140960795 + 4345440 * 2 ^ 59
def prefixEnd_4345440 : Nat := 4983230072969 + 3 ^ 40 * 4345440 * 2
def baseEnd_4345440 : Nat := 2231299375273583679715691

theorem tailTrace_4345440 : CollatzResearch.WordTrace tailWord_4345440 prefixEnd_4345440 2231299375273583679715691 := by
  unfold tailWord_4345440
  simp only [CollatzResearch.WordTrace]
  refine ⟨79245608688610248456080887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105660811584813664608107849 79245608688610248456080887)
  ·
    refine ⟨118868413032915372684121331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79245608688610248456080887 118868413032915372684121331)
    ·
      refine ⟨178302619549373059026181997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118868413032915372684121331 178302619549373059026181997)
      ·
        refine ⟨66863482331014897134818249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 178302619549373059026181997 66863482331014897134818249)
        ·
          refine ⟨50147611748261172851113687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66863482331014897134818249 50147611748261172851113687)
          ·
            refine ⟨75221417622391759276670531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50147611748261172851113687 75221417622391759276670531)
            ·
              refine ⟨112832126433587638915005797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75221417622391759276670531 112832126433587638915005797)
              ·
                refine ⟨21156023706297682296563587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 112832126433587638915005797 21156023706297682296563587)
                ·
                  refine ⟨31734035559446523444845381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21156023706297682296563587 31734035559446523444845381)
                  ·
                    refine ⟨5950131667396223145908509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 31734035559446523444845381 5950131667396223145908509)
                    ·
                      refine ⟨2231299375273583679715691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5950131667396223145908509 2231299375273583679715691)
                      ·
                        rfl

theorem cell23_4345440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 4, 1, 4, 3].length) (baseStart_4345440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4345440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4345440 prefixEnd_4345440 := by exact prefixLift 4345440
  have htrace : WordTrace (prefixWord ++ tailWord_4345440) baseStart_4345440 baseEnd_4345440 := by
    simpa [prefixWord, tailWord_4345440, baseEnd_4345440] using wordTrace_append hprefix tailTrace_4345440
  have hstable : (prefixWord ++ tailWord_4345440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4345440).length < 2 ^ (prefixWord ++ tailWord_4345440).sum := by decide
  have hdescent : baseEnd_4345440 < baseStart_4345440 := by decide
  rcases family_descends (prefixWord ++ tailWord_4345440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4345497 : List Nat := [1, 2, 1, 2, 1, 2, 2, 1, 6, 3, 2]
def baseStart_4345497 : Nat := 118140960795 + 4345497 * 2 ^ 59
def prefixEnd_4345497 : Nat := 4983230072969 + 3 ^ 40 * 4345497 * 2
def baseEnd_4345497 : Nat := 2231328643670889956702929

theorem tailTrace_4345497 : CollatzResearch.WordTrace tailWord_4345497 prefixEnd_4345497 2231328643670889956702929 := by
  unfold tailWord_4345497
  simp only [CollatzResearch.WordTrace]
  refine ⟨158493296338013995646986745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105662197558675997097991163 158493296338013995646986745)
  ·
    refine ⟨118869972253510496735240059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 158493296338013995646986745 118869972253510496735240059)
    ·
      refine ⟨178304958380265745102860089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118869972253510496735240059 178304958380265745102860089)
      ·
        refine ⟨133728718785199308827145067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 178304958380265745102860089 133728718785199308827145067)
        ·
          refine ⟨200593078177798963240717601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 133728718785199308827145067 200593078177798963240717601)
          ·
            refine ⟨150444808633349222430538201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 200593078177798963240717601 150444808633349222430538201)
            ·
              refine ⟨112833606475011916822903651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 150444808633349222430538201 112833606475011916822903651)
              ·
                refine ⟨169250409712517875234355477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 112833606475011916822903651 169250409712517875234355477)
                ·
                  refine ⟨7933612955274275401610413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 169250409712517875234355477 7933612955274275401610413)
                  ·
                    refine ⟨2975104858227853275603905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7933612955274275401610413 2975104858227853275603905)
                    ·
                      refine ⟨2231328643670889956702929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2975104858227853275603905 2231328643670889956702929)
                      ·
                        rfl

theorem cell23_4345497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 1, 6, 3, 2].length) (baseStart_4345497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4345497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4345497 prefixEnd_4345497 := by exact prefixLift 4345497
  have htrace : WordTrace (prefixWord ++ tailWord_4345497) baseStart_4345497 baseEnd_4345497 := by
    simpa [prefixWord, tailWord_4345497, baseEnd_4345497] using wordTrace_append hprefix tailTrace_4345497
  have hstable : (prefixWord ++ tailWord_4345497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4345497).length < 2 ^ (prefixWord ++ tailWord_4345497).sum := by decide
  have hdescent : baseEnd_4345497 < baseStart_4345497 := by decide
  rcases family_descends (prefixWord ++ tailWord_4345497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4345504 : List Nat := [2, 1, 1, 4, 3, 1, 2, 2, 3, 1, 3]
def baseStart_4345504 : Nat := 118140960795 + 4345504 * 2 ^ 59
def prefixEnd_4345504 : Nat := 4983230072969 + 3 ^ 40 * 4345504 * 2
def baseEnd_4345504 : Nat := 2231332238035471429315397

theorem tailTrace_4345504 : CollatzResearch.WordTrace tailWord_4345504 prefixEnd_4345504 2231332238035471429315397 := by
  unfold tailWord_4345504
  simp only [CollatzResearch.WordTrace]
  refine ⟨79246775824494317921245783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105662367765992423894994377 79246775824494317921245783)
  ·
    refine ⟨118870163736741476881868675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79246775824494317921245783 118870163736741476881868675)
    ·
      refine ⟨178305245605112215322803013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118870163736741476881868675 178305245605112215322803013)
      ·
        refine ⟨33432233550958540373025565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 178305245605112215322803013 33432233550958540373025565)
        ·
          refine ⟨12537087581609452639884587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33432233550958540373025565 12537087581609452639884587)
          ·
            refine ⟨18805631372414178959826881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12537087581609452639884587 18805631372414178959826881)
            ·
              refine ⟨14104223529310634219870161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18805631372414178959826881 14104223529310634219870161)
              ·
                refine ⟨10578167646982975664902621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14104223529310634219870161 10578167646982975664902621)
                ·
                  refine ⟨3966812867618615874338483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10578167646982975664902621 3966812867618615874338483)
                  ·
                    refine ⟨5950219301427923811507725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3966812867618615874338483 5950219301427923811507725)
                    ·
                      refine ⟨2231332238035471429315397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5950219301427923811507725 2231332238035471429315397)
                      ·
                        rfl

theorem cell23_4345504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 2, 2, 3, 1, 3].length) (baseStart_4345504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4345504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4345504 prefixEnd_4345504 := by exact prefixLift 4345504
  have htrace : WordTrace (prefixWord ++ tailWord_4345504) baseStart_4345504 baseEnd_4345504 := by
    simpa [prefixWord, tailWord_4345504, baseEnd_4345504] using wordTrace_append hprefix tailTrace_4345504
  have hstable : (prefixWord ++ tailWord_4345504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4345504).length < 2 ^ (prefixWord ++ tailWord_4345504).sum := by decide
  have hdescent : baseEnd_4345504 < baseStart_4345504 := by decide
  rcases family_descends (prefixWord ++ tailWord_4345504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4345507 : List Nat := [1, 1, 1, 4, 1, 1, 6, 2, 1, 5]
def baseStart_4345507 : Nat := 118140960795 + 4345507 * 2 ^ 59
def prefixEnd_4345507 : Nat := 4983230072969 + 3 ^ 40 * 4345507 * 2
def baseEnd_4345507 : Nat := 743777926159144972525961

theorem tailTrace_4345507 : CollatzResearch.WordTrace tailWord_4345507 prefixEnd_4345507 743777926159144972525961 := by
  unfold tailWord_4345507
  simp only [CollatzResearch.WordTrace]
  refine ⟨158493661067977767354850775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105662440711985178236567183 158493661067977767354850775)
  ·
    refine ⟨237740491601966651032276163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158493661067977767354850775 237740491601966651032276163)
    ·
      refine ⟨356610737402949976548414245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 237740491601966651032276163 356610737402949976548414245)
      ·
        refine ⟨66864513263053120602827671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 356610737402949976548414245 66864513263053120602827671)
        ·
          refine ⟨100296769894579680904241507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66864513263053120602827671 100296769894579680904241507)
          ·
            refine ⟨150445154841869521356362261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 100296769894579680904241507 150445154841869521356362261)
            ·
              refine ⟨7052116633212633813579481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 150445154841869521356362261 7052116633212633813579481)
              ·
                refine ⟨5289087474909475360184611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7052116633212633813579481 5289087474909475360184611)
                ·
                  refine ⟨7933631212364213040276917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5289087474909475360184611 7933631212364213040276917)
                  ·
                    refine ⟨743777926159144972525961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7933631212364213040276917 743777926159144972525961)
                    ·
                      rfl

theorem cell23_4345507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 6, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 6, 2, 1, 5].length) (baseStart_4345507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4345507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4345507 prefixEnd_4345507 := by exact prefixLift 4345507
  have htrace : WordTrace (prefixWord ++ tailWord_4345507) baseStart_4345507 baseEnd_4345507 := by
    simpa [prefixWord, tailWord_4345507, baseEnd_4345507] using wordTrace_append hprefix tailTrace_4345507
  have hstable : (prefixWord ++ tailWord_4345507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4345507).length < 2 ^ (prefixWord ++ tailWord_4345507).sum := by decide
  have hdescent : baseEnd_4345507 < baseStart_4345507 := by decide
  rcases family_descends (prefixWord ++ tailWord_4345507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4345520 : List Nat := [2, 1, 1, 1, 2, 1, 4, 4, 1, 6]
def baseStart_4345520 : Nat := 118140960795 + 4345520 * 2 ^ 59
def prefixEnd_4345520 : Nat := 4983230072969 + 3 ^ 40 * 4345520 * 2
def baseEnd_4345520 : Nat := 743780151241981122238441

theorem tailTrace_4345520 : CollatzResearch.WordTrace tailWord_4345520 prefixEnd_4345520 743780151241981122238441 := by
  unfold tailWord_4345520
  simp only [CollatzResearch.WordTrace]
  refine ⟨79247067608465335287537007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105662756811287113716716009 79247067608465335287537007)
  ·
    refine ⟨118870601412698002931305511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79247067608465335287537007 118870601412698002931305511)
    ·
      refine ⟨178305902119047004396958267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118870601412698002931305511 178305902119047004396958267)
      ·
        refine ⟨267458853178570506595437401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 178305902119047004396958267 267458853178570506595437401)
        ·
          refine ⟨200594139883927879946578051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 267458853178570506595437401 200594139883927879946578051)
          ·
            refine ⟨300891209825891819919867077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 200594139883927879946578051 300891209825891819919867077)
            ·
              refine ⟨56417101842354716234975077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 300891209825891819919867077 56417101842354716234975077)
              ·
                refine ⟨10578206595441509294057827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 56417101842354716234975077 10578206595441509294057827)
                ·
                  refine ⟨15867309893162263941086741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10578206595441509294057827 15867309893162263941086741)
                  ·
                    refine ⟨743780151241981122238441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15867309893162263941086741 743780151241981122238441)
                    ·
                      rfl

theorem cell23_4345520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 4, 1, 6].length) (baseStart_4345520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4345520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4345520 prefixEnd_4345520 := by exact prefixLift 4345520
  have htrace : WordTrace (prefixWord ++ tailWord_4345520) baseStart_4345520 baseEnd_4345520 := by
    simpa [prefixWord, tailWord_4345520, baseEnd_4345520] using wordTrace_append hprefix tailTrace_4345520
  have hstable : (prefixWord ++ tailWord_4345520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4345520).length < 2 ^ (prefixWord ++ tailWord_4345520).sum := by decide
  have hdescent : baseEnd_4345520 < baseStart_4345520 := by decide
  rcases family_descends (prefixWord ++ tailWord_4345520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4345588 : List Nat := [2, 6, 1, 1, 1, 1, 1, 4, 2, 4]
def baseStart_4345588 : Nat := 118140960795 + 4345588 * 2 ^ 59
def prefixEnd_4345588 : Nat := 4983230072969 + 3 ^ 40 * 4345588 * 2
def baseEnd_4345588 : Nat := 743791790136816366888337

theorem tailTrace_4345588 : CollatzResearch.WordTrace tailWord_4345588 prefixEnd_4345588 743791790136816366888337 := by
  unfold tailWord_4345588
  simp only [CollatzResearch.WordTrace]
  refine ⟨79248307690342159094274709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105664410253789545459032945 79248307690342159094274709)
  ·
    refine ⟨3714764422984788707544127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 79248307690342159094274709 3714764422984788707544127)
    ·
      refine ⟨5572146634477183061316191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3714764422984788707544127 5572146634477183061316191)
      ·
        refine ⟨8358219951715774591974287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5572146634477183061316191 8358219951715774591974287)
        ·
          refine ⟨12537329927573661887961431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8358219951715774591974287 12537329927573661887961431)
          ·
            refine ⟨18805994891360492831942147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12537329927573661887961431 18805994891360492831942147)
            ·
              refine ⟨28208992337040739247913221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18805994891360492831942147 28208992337040739247913221)
              ·
                refine ⟨5289186063195138608983729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28208992337040739247913221 5289186063195138608983729)
                ·
                  refine ⟨3966889547396353956737797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5289186063195138608983729 3966889547396353956737797)
                  ·
                    refine ⟨743791790136816366888337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3966889547396353956737797 743791790136816366888337)
                    ·
                      rfl

theorem cell23_4345588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 1, 4, 2, 4].length) (baseStart_4345588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4345588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4345588 prefixEnd_4345588 := by exact prefixLift 4345588
  have htrace : WordTrace (prefixWord ++ tailWord_4345588) baseStart_4345588 baseEnd_4345588 := by
    simpa [prefixWord, tailWord_4345588, baseEnd_4345588] using wordTrace_append hprefix tailTrace_4345588
  have hstable : (prefixWord ++ tailWord_4345588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4345588).length < 2 ^ (prefixWord ++ tailWord_4345588).sum := by decide
  have hdescent : baseEnd_4345588 < baseStart_4345588 := by decide
  rcases family_descends (prefixWord ++ tailWord_4345588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4345697 : List Nat := [1, 2, 3, 1, 1, 1, 4, 2, 1, 2, 5]
def baseStart_4345697 : Nat := 118140960795 + 4345697 * 2 ^ 59
def prefixEnd_4345697 : Nat := 4983230072969 + 3 ^ 40 * 4345697 * 2
def baseEnd_4345697 : Nat := 2231431339801789174202009

theorem tailTrace_4345697 : CollatzResearch.WordTrace tailWord_4345697 prefixEnd_4345697 2231431339801789174202009 := by
  unfold tailWord_4345697
  simp only [CollatzResearch.WordTrace]
  refine ⟨158500590937289429804267345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105667060624859619869511563 158500590937289429804267345)
  ·
    refine ⟨118875443202967072353200509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 158500590937289429804267345 118875443202967072353200509)
    ·
      refine ⟨44578291201112652132450191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 118875443202967072353200509 44578291201112652132450191)
      ·
        refine ⟨66867436801668978198675287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44578291201112652132450191 66867436801668978198675287)
        ·
          refine ⟨100301155202503467298012931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66867436801668978198675287 100301155202503467298012931)
          ·
            refine ⟨150451732803755200947019397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 100301155202503467298012931 150451732803755200947019397)
            ·
              refine ⟨28209699900704100177566137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 150451732803755200947019397 28209699900704100177566137)
              ·
                refine ⟨21157274925528075133174603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28209699900704100177566137 21157274925528075133174603)
                ·
                  refine ⟨31735912388292112699761905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21157274925528075133174603 31735912388292112699761905)
                  ·
                    refine ⟨23801934291219084524821429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 31735912388292112699761905 23801934291219084524821429)
                    ·
                      refine ⟨2231431339801789174202009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23801934291219084524821429 2231431339801789174202009)
                      ·
                        rfl

theorem cell23_4345697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 4, 2, 1, 2, 5].length) (baseStart_4345697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4345697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4345697 prefixEnd_4345697 := by exact prefixLift 4345697
  have htrace : WordTrace (prefixWord ++ tailWord_4345697) baseStart_4345697 baseEnd_4345697 := by
    simpa [prefixWord, tailWord_4345697, baseEnd_4345697] using wordTrace_append hprefix tailTrace_4345697
  have hstable : (prefixWord ++ tailWord_4345697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4345697).length < 2 ^ (prefixWord ++ tailWord_4345697).sum := by decide
  have hdescent : baseEnd_4345697 < baseStart_4345697 := by decide
  rcases family_descends (prefixWord ++ tailWord_4345697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4345704 : List Nat := [2, 1, 4, 2, 1, 1, 3, 2, 2, 5]
def baseStart_4345704 : Nat := 118140960795 + 4345704 * 2 ^ 59
def prefixEnd_4345704 : Nat := 4983230072969 + 3 ^ 40 * 4345704 * 2
def baseEnd_4345704 : Nat := 743811644722123548938159

theorem tailTrace_4345704 : CollatzResearch.WordTrace tailWord_4345704 prefixEnd_4345704 743811644722123548938159 := by
  unfold tailWord_4345704
  simp only [CollatzResearch.WordTrace]
  refine ⟨79250423124132034999886083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105667230832176046666514777 79250423124132034999886083)
  ·
    refine ⟨118875634686198052499829125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79250423124132034999886083 118875634686198052499829125)
    ·
      refine ⟨22289181503662134843717961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 118875634686198052499829125 22289181503662134843717961)
      ·
        refine ⟨16716886127746601132788471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22289181503662134843717961 16716886127746601132788471)
        ·
          refine ⟨25075329191619901699182707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16716886127746601132788471 25075329191619901699182707)
          ·
            refine ⟨37612993787429852548774061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25075329191619901699182707 37612993787429852548774061)
            ·
              refine ⟨14104872670286194705790273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37612993787429852548774061 14104872670286194705790273)
              ·
                refine ⟨10578654502714646029342705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14104872670286194705790273 10578654502714646029342705)
                ·
                  refine ⟨7933990877035984522007029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10578654502714646029342705 7933990877035984522007029)
                  ·
                    refine ⟨743811644722123548938159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7933990877035984522007029 743811644722123548938159)
                    ·
                      rfl

theorem cell23_4345704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 3, 2, 2, 5].length) (baseStart_4345704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4345704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4345704 prefixEnd_4345704 := by exact prefixLift 4345704
  have htrace : WordTrace (prefixWord ++ tailWord_4345704) baseStart_4345704 baseEnd_4345704 := by
    simpa [prefixWord, tailWord_4345704, baseEnd_4345704] using wordTrace_append hprefix tailTrace_4345704
  have hstable : (prefixWord ++ tailWord_4345704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4345704).length < 2 ^ (prefixWord ++ tailWord_4345704).sum := by decide
  have hdescent : baseEnd_4345704 < baseStart_4345704 := by decide
  rcases family_descends (prefixWord ++ tailWord_4345704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4345744 : List Nat := [2, 1, 1, 1, 1, 1, 2, 7, 2, 2, 3]
def baseStart_4345744 : Nat := 118140960795 + 4345744 * 2 ^ 59
def prefixEnd_4345744 : Nat := 4983230072969 + 3 ^ 40 * 4345744 * 2
def baseEnd_4345744 : Nat := 2231455473392550490314293

theorem tailTrace_4345744 : CollatzResearch.WordTrace tailWord_4345744 prefixEnd_4345744 2231455473392550490314293 := by
  unfold tailWord_4345744
  simp only [CollatzResearch.WordTrace]
  refine ⟨79251152584059578415614143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105668203445412771220818857 79251152584059578415614143)
  ·
    refine ⟨118876728876089367623421215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79251152584059578415614143 118876728876089367623421215)
    ·
      refine ⟨178315093314134051435131823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118876728876089367623421215 178315093314134051435131823)
      ·
        refine ⟨267472639971201077152697735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 178315093314134051435131823 267472639971201077152697735)
        ·
          refine ⟨401208959956801615729046603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 267472639971201077152697735 401208959956801615729046603)
          ·
            refine ⟨601813439935202423593569905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 401208959956801615729046603 601813439935202423593569905)
            ·
              refine ⟨451360079951401817695177429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 601813439935202423593569905 451360079951401817695177429)
              ·
                refine ⟨10578751873860980102230721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 451360079951401817695177429 10578751873860980102230721)
                ·
                  refine ⟨7934063905395735076673041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10578751873860980102230721 7934063905395735076673041)
                  ·
                    refine ⟨5950547929046801307504781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7934063905395735076673041 5950547929046801307504781)
                    ·
                      refine ⟨2231455473392550490314293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5950547929046801307504781 2231455473392550490314293)
                      ·
                        rfl

theorem cell23_4345744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 7, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 7, 2, 2, 3].length) (baseStart_4345744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4345744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4345744 prefixEnd_4345744 := by exact prefixLift 4345744
  have htrace : WordTrace (prefixWord ++ tailWord_4345744) baseStart_4345744 baseEnd_4345744 := by
    simpa [prefixWord, tailWord_4345744, baseEnd_4345744] using wordTrace_append hprefix tailTrace_4345744
  have hstable : (prefixWord ++ tailWord_4345744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4345744).length < 2 ^ (prefixWord ++ tailWord_4345744).sum := by decide
  have hdescent : baseEnd_4345744 < baseStart_4345744 := by decide
  rcases family_descends (prefixWord ++ tailWord_4345744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4345764 : List Nat := [2, 3, 1, 2, 1, 3, 1, 4, 6]
def baseStart_4345764 : Nat := 118140960795 + 4345764 * 2 ^ 59
def prefixEnd_4345764 : Nat := 4983230072969 + 3 ^ 40 * 4345764 * 2
def baseEnd_4345764 : Nat := 247940638111737823562689

theorem tailTrace_4345764 : CollatzResearch.WordTrace tailWord_4345764 prefixEnd_4345764 247940638111737823562689 := by
  unfold tailWord_4345764
  simp only [CollatzResearch.WordTrace]
  refine ⟨79251517314023350123478173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105668689752031133497970897 79251517314023350123478173)
  ·
    refine ⟨29719318992758756296304315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79251517314023350123478173 29719318992758756296304315)
    ·
      refine ⟨44578978489138134444456473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29719318992758756296304315 44578978489138134444456473)
      ·
        refine ⟨33434233866853600833342355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44578978489138134444456473 33434233866853600833342355)
        ·
          refine ⟨50151350800280401250013533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33434233866853600833342355 50151350800280401250013533)
          ·
            refine ⟨18806756550105150468755075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50151350800280401250013533 18806756550105150468755075)
            ·
              refine ⟨28210134825157725703132613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18806756550105150468755075 28210134825157725703132613)
              ·
                refine ⟨5289400279717073569337365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28210134825157725703132613 5289400279717073569337365)
                ·
                  refine ⟨247940638111737823562689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5289400279717073569337365 247940638111737823562689)
                  ·
                    rfl

theorem cell23_4345764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 1, 4, 6].length) (baseStart_4345764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4345764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4345764 prefixEnd_4345764 := by exact prefixLift 4345764
  have htrace : WordTrace (prefixWord ++ tailWord_4345764) baseStart_4345764 baseEnd_4345764 := by
    simpa [prefixWord, tailWord_4345764, baseEnd_4345764] using wordTrace_append hprefix tailTrace_4345764
  have hstable : (prefixWord ++ tailWord_4345764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4345764).length < 2 ^ (prefixWord ++ tailWord_4345764).sum := by decide
  have hdescent : baseEnd_4345764 < baseStart_4345764 := by decide
  rcases family_descends (prefixWord ++ tailWord_4345764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4345791 : List Nat := [1, 1, 2, 2, 2, 1, 5, 2, 3, 1, 3]
def baseStart_4345791 : Nat := 118140960795 + 4345791 * 2 ^ 59
def prefixEnd_4345791 : Nat := 4983230072969 + 3 ^ 40 * 4345791 * 2
def baseEnd_4345791 : Nat := 2231479606983311806426577

theorem tailTrace_4345791 : CollatzResearch.WordTrace tailWord_4345791 prefixEnd_4345791 2231479606983311806426577 := by
  unfold tailWord_4345791
  simp only [CollatzResearch.WordTrace]
  refine ⟨158504019398948883858189227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105669346265965922572126151 158504019398948883858189227)
  ·
    refine ⟨237756029098423325787283841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158504019398948883858189227 237756029098423325787283841)
    ·
      refine ⟨178317021823817494340462881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 237756029098423325787283841 178317021823817494340462881)
      ·
        refine ⟨133737766367863120755347161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 178317021823817494340462881 133737766367863120755347161)
        ·
          refine ⟨100303324775897340566510371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 133737766367863120755347161 100303324775897340566510371)
          ·
            refine ⟨150454987163846010849765557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 100303324775897340566510371 150454987163846010849765557)
            ·
              refine ⟨14105155046610563517165521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 150454987163846010849765557 14105155046610563517165521)
              ·
                refine ⟨10578866284957922637874141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14105155046610563517165521 10578866284957922637874141)
                ·
                  refine ⟨3967074856859220989202803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10578866284957922637874141 3967074856859220989202803)
                  ·
                    refine ⟨5950612285288831483804205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3967074856859220989202803 5950612285288831483804205)
                    ·
                      refine ⟨2231479606983311806426577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5950612285288831483804205 2231479606983311806426577)
                      ·
                        rfl

theorem cell23_4345791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 5, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 5, 2, 3, 1, 3].length) (baseStart_4345791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4345791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4345791 prefixEnd_4345791 := by exact prefixLift 4345791
  have htrace : WordTrace (prefixWord ++ tailWord_4345791) baseStart_4345791 baseEnd_4345791 := by
    simpa [prefixWord, tailWord_4345791, baseEnd_4345791] using wordTrace_append hprefix tailTrace_4345791
  have hstable : (prefixWord ++ tailWord_4345791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4345791).length < 2 ^ (prefixWord ++ tailWord_4345791).sum := by decide
  have hdescent : baseEnd_4345791 < baseStart_4345791 := by decide
  rcases family_descends (prefixWord ++ tailWord_4345791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4345808 : List Nat := [2, 1, 1, 1, 1, 2, 5, 5, 1, 1, 3]
def baseStart_4345808 : Nat := 118140960795 + 4345808 * 2 ^ 59
def prefixEnd_4345808 : Nat := 4983230072969 + 3 ^ 40 * 4345808 * 2
def baseEnd_4345808 : Nat := 2231488336154438239913999

theorem tailTrace_4345808 : CollatzResearch.WordTrace tailWord_4345808 prefixEnd_4345808 2231488336154438239913999 := by
  unfold tailWord_4345808
  simp only [CollatzResearch.WordTrace]
  refine ⟨79252319719943647880779039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105669759626591530507705385 79252319719943647880779039)
  ·
    refine ⟨118878479579915471821168559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79252319719943647880779039 118878479579915471821168559)
    ·
      refine ⟨178317719369873207731752839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118878479579915471821168559 178317719369873207731752839)
      ·
        refine ⟨267476579054809811597629259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 178317719369873207731752839 267476579054809811597629259)
        ·
          refine ⟨401214868582214717396443889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 267476579054809811597629259 401214868582214717396443889)
          ·
            refine ⟨300911151436661038047332917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 401214868582214717396443889 300911151436661038047332917)
            ·
              refine ⟨28210420447186972316937461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 300911151436661038047332917 28210420447186972316937461)
              ·
                refine ⟨2644726916923778654712887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 28210420447186972316937461 2644726916923778654712887)
                ·
                  refine ⟨3967090375385667982069331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2644726916923778654712887 3967090375385667982069331)
                  ·
                    refine ⟨5950635563078501973103997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3967090375385667982069331 5950635563078501973103997)
                    ·
                      refine ⟨2231488336154438239913999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5950635563078501973103997 2231488336154438239913999)
                      ·
                        rfl

theorem cell23_4345808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 5, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 5, 5, 1, 1, 3].length) (baseStart_4345808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4345808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4345808 prefixEnd_4345808 := by exact prefixLift 4345808
  have htrace : WordTrace (prefixWord ++ tailWord_4345808) baseStart_4345808 baseEnd_4345808 := by
    simpa [prefixWord, tailWord_4345808, baseEnd_4345808] using wordTrace_append hprefix tailTrace_4345808
  have hstable : (prefixWord ++ tailWord_4345808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4345808).length < 2 ^ (prefixWord ++ tailWord_4345808).sum := by decide
  have hdescent : baseEnd_4345808 < baseStart_4345808 := by decide
  rcases family_descends (prefixWord ++ tailWord_4345808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4345848 : List Nat := [2, 1, 2, 1, 1, 3, 4, 2, 3, 2, 2]
def baseStart_4345848 : Nat := 118140960795 + 4345848 * 2 ^ 59
def prefixEnd_4345848 : Nat := 4983230072969 + 3 ^ 40 * 4345848 * 2
def baseEnd_4345848 : Nat := 2231508875380618083413815

theorem tailTrace_4345848 : CollatzResearch.WordTrace tailWord_4345848 prefixEnd_4345848 2231508875380618083413815 := by
  unfold tailWord_4345848
  simp only [CollatzResearch.WordTrace]
  refine ⟨79253049179871191296507099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105670732239828255062009465 79253049179871191296507099)
  ·
    refine ⟨118879573769806786944760649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79253049179871191296507099 118879573769806786944760649)
    ·
      refine ⟨89159680327355090208570487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 118879573769806786944760649 89159680327355090208570487)
      ·
        refine ⟨133739520491032635312855731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89159680327355090208570487 133739520491032635312855731)
        ·
          refine ⟨200609280736548952969283597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 133739520491032635312855731 200609280736548952969283597)
          ·
            refine ⟨75228480276205857363481349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 200609280736548952969283597 75228480276205857363481349)
            ·
              refine ⟨14105340051788598255652753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 75228480276205857363481349 14105340051788598255652753)
              ·
                refine ⟨10579005038841448691739565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14105340051788598255652753 10579005038841448691739565)
                ·
                  refine ⟨3967126889565543259402337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10579005038841448691739565 3967126889565543259402337)
                  ·
                    refine ⟨2975345167174157444551753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3967126889565543259402337 2975345167174157444551753)
                    ·
                      refine ⟨2231508875380618083413815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2975345167174157444551753 2231508875380618083413815)
                      ·
                        rfl

theorem cell23_4345848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 4, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 4, 2, 3, 2, 2].length) (baseStart_4345848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4345848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4345848 prefixEnd_4345848 := by exact prefixLift 4345848
  have htrace : WordTrace (prefixWord ++ tailWord_4345848) baseStart_4345848 baseEnd_4345848 := by
    simpa [prefixWord, tailWord_4345848, baseEnd_4345848] using wordTrace_append hprefix tailTrace_4345848
  have hstable : (prefixWord ++ tailWord_4345848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4345848).length < 2 ^ (prefixWord ++ tailWord_4345848).sum := by decide
  have hdescent : baseEnd_4345848 < baseStart_4345848 := by decide
  rcases family_descends (prefixWord ++ tailWord_4345848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4345851 : List Nat := [1, 1, 1, 1, 1, 3, 5, 4, 1, 2, 3]
def baseStart_4345851 : Nat := 118140960795 + 4345851 * 2 ^ 59
def prefixEnd_4345851 : Nat := 4983230072969 + 3 ^ 40 * 4345851 * 2
def baseEnd_4345851 : Nat := 2231510415822581571676301

theorem tailTrace_4345851 : CollatzResearch.WordTrace tailWord_4345851 prefixEnd_4345851 2231510415822581571676301 := by
  unfold tailWord_4345851
  simp only [CollatzResearch.WordTrace]
  refine ⟨158506207778731514105373407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105670805185821009403582271 158506207778731514105373407)
  ·
    refine ⟨237759311668097271158060111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158506207778731514105373407 237759311668097271158060111)
    ·
      refine ⟨356638967502145906737090167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 237759311668097271158060111 356638967502145906737090167)
      ·
        refine ⟨534958451253218860105635251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 356638967502145906737090167 534958451253218860105635251)
        ·
          refine ⟨802437676879828290158452877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 534958451253218860105635251 802437676879828290158452877)
          ·
            refine ⟨300914128829935608809419829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 802437676879828290158452877 300914128829935608809419829)
            ·
              refine ⟨28210699577806463325883109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 300914128829935608809419829 28210699577806463325883109)
              ·
                refine ⟨5289506170838711873603083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28210699577806463325883109 5289506170838711873603083)
                ·
                  refine ⟨7934259256258067810404625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5289506170838711873603083 7934259256258067810404625)
                  ·
                    refine ⟨5950694442193550857803469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7934259256258067810404625 5950694442193550857803469)
                    ·
                      refine ⟨2231510415822581571676301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5950694442193550857803469 2231510415822581571676301)
                      ·
                        rfl

theorem cell23_4345851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 5, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 5, 4, 1, 2, 3].length) (baseStart_4345851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4345851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4345851 prefixEnd_4345851 := by exact prefixLift 4345851
  have htrace : WordTrace (prefixWord ++ tailWord_4345851) baseStart_4345851 baseEnd_4345851 := by
    simpa [prefixWord, tailWord_4345851, baseEnd_4345851] using wordTrace_append hprefix tailTrace_4345851
  have hstable : (prefixWord ++ tailWord_4345851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4345851).length < 2 ^ (prefixWord ++ tailWord_4345851).sum := by decide
  have hdescent : baseEnd_4345851 < baseStart_4345851 := by decide
  rcases family_descends (prefixWord ++ tailWord_4345851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4345869 : List Nat := [1, 7, 1, 2, 1, 1, 1, 2, 2, 3, 2]
def baseStart_4345869 : Nat := 118140960795 + 4345869 * 2 ^ 59
def prefixEnd_4345869 : Nat := 4983230072969 + 3 ^ 40 * 4345869 * 2
def baseEnd_4345869 : Nat := 2231519658474362501251219

theorem tailTrace_4345869 : CollatzResearch.WordTrace tailWord_4345869 prefixEnd_4345869 2231519658474362501251219 := by
  unfold tailWord_4345869
  simp only [CollatzResearch.WordTrace]
  refine ⟨158506864292666303179528661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105671242861777535453019107 158506864292666303179528661)
  ·
    refine ⟨3715004631859366480770203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 158506864292666303179528661 3715004631859366480770203)
    ·
      refine ⟨5572506947789049721155305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3715004631859366480770203 5572506947789049721155305)
      ·
        refine ⟨4179380210841787290866479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5572506947789049721155305 4179380210841787290866479)
        ·
          refine ⟨6269070316262680936299719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4179380210841787290866479 6269070316262680936299719)
          ·
            refine ⟨9403605474394021404449579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6269070316262680936299719 9403605474394021404449579)
            ·
              refine ⟨14105408211591032106674369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9403605474394021404449579 14105408211591032106674369)
              ·
                refine ⟨10579056158693274080005777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14105408211591032106674369 10579056158693274080005777)
                ·
                  refine ⟨7934292119019955560004333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10579056158693274080005777 7934292119019955560004333)
                  ·
                    refine ⟨2975359544632483335001625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7934292119019955560004333 2975359544632483335001625)
                    ·
                      refine ⟨2231519658474362501251219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2975359544632483335001625 2231519658474362501251219)
                      ·
                        rfl

theorem cell23_4345869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 1, 2, 2, 3, 2].length) (baseStart_4345869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4345869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4345869 prefixEnd_4345869 := by exact prefixLift 4345869
  have htrace : WordTrace (prefixWord ++ tailWord_4345869) baseStart_4345869 baseEnd_4345869 := by
    simpa [prefixWord, tailWord_4345869, baseEnd_4345869] using wordTrace_append hprefix tailTrace_4345869
  have hstable : (prefixWord ++ tailWord_4345869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4345869).length < 2 ^ (prefixWord ++ tailWord_4345869).sum := by decide
  have hdescent : baseEnd_4345869 < baseStart_4345869 := by decide
  rcases family_descends (prefixWord ++ tailWord_4345869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4345876 : List Nat := [2, 4, 3, 2, 1, 1, 3, 2, 1, 1, 3]
def baseStart_4345876 : Nat := 118140960795 + 4345876 * 2 ^ 59
def prefixEnd_4345876 : Nat := 4983230072969 + 3 ^ 40 * 4345876 * 2
def baseEnd_4345876 : Nat := 2231523252838943973863687

theorem tailTrace_4345876 : CollatzResearch.WordTrace tailWord_4345876 prefixEnd_4345876 2231523252838943973863687 := by
  unfold tailWord_4345876
  simp only [CollatzResearch.WordTrace]
  refine ⟨79253559801820471687516741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105671413069093962250022321 79253559801820471687516741)
  ·
    refine ⟨14860042462841338441409389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 79253559801820471687516741 14860042462841338441409389)
    ·
      refine ⟨5572515923565501915528521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14860042462841338441409389 5572515923565501915528521)
      ·
        refine ⟨4179386942674126436646391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5572515923565501915528521 4179386942674126436646391)
        ·
          refine ⟨6269080414011189654969587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4179386942674126436646391 6269080414011189654969587)
          ·
            refine ⟨9403620621016784482454381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6269080414011189654969587 9403620621016784482454381)
            ·
              refine ⟨3526357732881294180920393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9403620621016784482454381 3526357732881294180920393)
              ·
                refine ⟨2644768299660970635690295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3526357732881294180920393 2644768299660970635690295)
                ·
                  refine ⟨3967152449491455953535443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2644768299660970635690295 3967152449491455953535443)
                  ·
                    refine ⟨5950728674237183930303165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3967152449491455953535443 5950728674237183930303165)
                    ·
                      refine ⟨2231523252838943973863687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5950728674237183930303165 2231523252838943973863687)
                      ·
                        rfl

theorem cell23_4345876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 3, 2, 1, 1, 3].length) (baseStart_4345876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4345876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4345876 prefixEnd_4345876 := by exact prefixLift 4345876
  have htrace : WordTrace (prefixWord ++ tailWord_4345876) baseStart_4345876 baseEnd_4345876 := by
    simpa [prefixWord, tailWord_4345876, baseEnd_4345876] using wordTrace_append hprefix tailTrace_4345876
  have hstable : (prefixWord ++ tailWord_4345876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4345876).length < 2 ^ (prefixWord ++ tailWord_4345876).sum := by decide
  have hdescent : baseEnd_4345876 < baseStart_4345876 := by decide
  rcases family_descends (prefixWord ++ tailWord_4345876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4345892 : List Nat := [2, 3, 1, 4, 2, 2, 2, 1, 2, 4]
def baseStart_4345892 : Nat := 118140960795 + 4345892 * 2 ^ 59
def prefixEnd_4345892 : Nat := 4983230072969 + 3 ^ 40 * 4345892 * 2
def baseEnd_4345892 : Nat := 743843822843138637087871

theorem tailTrace_4345892 : CollatzResearch.WordTrace tailWord_4345892 prefixEnd_4345892 743843822843138637087871 := by
  unfold tailWord_4345892
  simp only [CollatzResearch.WordTrace]
  refine ⟨79253851585791489053807965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105671802114388652071743953 79253851585791489053807965)
  ·
    refine ⟨29720194344671808395177987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79253851585791489053807965 29720194344671808395177987)
    ·
      refine ⟨44580291517007712592766981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29720194344671808395177987 44580291517007712592766981)
      ·
        refine ⟨8358804659438946111143809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 44580291517007712592766981 8358804659438946111143809)
        ·
          refine ⟨6269103494579209583357857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8358804659438946111143809 6269103494579209583357857)
          ·
            refine ⟨4701827620934407187518393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6269103494579209583357857 4701827620934407187518393)
            ·
              refine ⟨3526370715700805390638795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4701827620934407187518393 3526370715700805390638795)
              ·
                refine ⟨5289556073551208085958193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3526370715700805390638795 5289556073551208085958193)
                ·
                  refine ⟨3967167055163406064468645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5289556073551208085958193 3967167055163406064468645)
                  ·
                    refine ⟨743843822843138637087871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3967167055163406064468645 743843822843138637087871)
                    ·
                      rfl

theorem cell23_4345892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 2, 2, 1, 2, 4].length) (baseStart_4345892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4345892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4345892 prefixEnd_4345892 := by exact prefixLift 4345892
  have htrace : WordTrace (prefixWord ++ tailWord_4345892) baseStart_4345892 baseEnd_4345892 := by
    simpa [prefixWord, tailWord_4345892, baseEnd_4345892] using wordTrace_append hprefix tailTrace_4345892
  have hstable : (prefixWord ++ tailWord_4345892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4345892).length < 2 ^ (prefixWord ++ tailWord_4345892).sum := by decide
  have hdescent : baseEnd_4345892 < baseStart_4345892 := by decide
  rcases family_descends (prefixWord ++ tailWord_4345892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4345914 : List Nat := [3, 1, 1, 1, 3, 1, 1, 2, 4, 6]
def baseStart_4345914 : Nat := 118140960795 + 4345914 * 2 ^ 59
def prefixEnd_4345914 : Nat := 4983230072969 + 3 ^ 40 * 4345914 * 2
def baseEnd_4345914 : Nat := 743847588367938275062837

theorem tailTrace_4345914 : CollatzResearch.WordTrace tailWord_4345914 prefixEnd_4345914 743847588367938275062837 := by
  unfold tailWord_4345914
  simp only [CollatzResearch.WordTrace]
  refine ⟨39627126394375818966229199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105672337051668850576611197 39627126394375818966229199)
  ·
    refine ⟨59440689591563728449343799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39627126394375818966229199 59440689591563728449343799)
    ·
      refine ⟨89161034387345592674015699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59440689591563728449343799 89161034387345592674015699)
      ·
        refine ⟨133741551581018389011023549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89161034387345592674015699 133741551581018389011023549)
        ·
          refine ⟨50153081842881895879133831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 133741551581018389011023549 50153081842881895879133831)
          ·
            refine ⟨75229622764322843818700747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50153081842881895879133831 75229622764322843818700747)
            ·
              refine ⟨112844434146484265728051121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75229622764322843818700747 112844434146484265728051121)
              ·
                refine ⟨84633325609863199296038341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 112844434146484265728051121 84633325609863199296038341)
                ·
                  refine ⟨15868748551849349868007189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 84633325609863199296038341 15868748551849349868007189)
                  ·
                    refine ⟨743847588367938275062837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15868748551849349868007189 743847588367938275062837)
                    ·
                      rfl

theorem cell23_4345914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 2, 4, 6].length) (baseStart_4345914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4345914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4345914 prefixEnd_4345914 := by exact prefixLift 4345914
  have htrace : WordTrace (prefixWord ++ tailWord_4345914) baseStart_4345914 baseEnd_4345914 := by
    simpa [prefixWord, tailWord_4345914, baseEnd_4345914] using wordTrace_append hprefix tailTrace_4345914
  have hstable : (prefixWord ++ tailWord_4345914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4345914).length < 2 ^ (prefixWord ++ tailWord_4345914).sum := by decide
  have hdescent : baseEnd_4345914 < baseStart_4345914 := by decide
  rcases family_descends (prefixWord ++ tailWord_4345914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4345941 : List Nat := [1, 3, 2, 2, 1, 3, 1, 1, 2, 4, 3]
def baseStart_4345941 : Nat := 118140960795 + 4345941 * 2 ^ 59
def prefixEnd_4345941 : Nat := 4983230072969 + 3 ^ 40 * 4345941 * 2
def baseEnd_4345941 : Nat := 2231556629081486219550887

theorem tailTrace_4345941 : CollatzResearch.WordTrace tailWord_4345941 prefixEnd_4345941 2231556629081486219550887 := by
  unfold tailWord_4345941
  simp only [CollatzResearch.WordTrace]
  refine ⟨158509490348405459476149677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105672993565603639650766451 158509490348405459476149677)
  ·
    refine ⟨59441058880652047303556129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 158509490348405459476149677 59441058880652047303556129)
    ·
      refine ⟨44580794160489035477667097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59441058880652047303556129 44580794160489035477667097)
      ·
        refine ⟨33435595620366776608250323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44580794160489035477667097 33435595620366776608250323)
        ·
          refine ⟨50153393430550164912375485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33435595620366776608250323 50153393430550164912375485)
          ·
            refine ⟨18807522536456311842140807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50153393430550164912375485 18807522536456311842140807)
            ·
              refine ⟨28211283804684467763211211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18807522536456311842140807 28211283804684467763211211)
              ·
                refine ⟨42316925707026701644816817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28211283804684467763211211 42316925707026701644816817)
                ·
                  refine ⟨31737694280270026233612613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 42316925707026701644816817 31737694280270026233612613)
                  ·
                    refine ⟨5950817677550629918802365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 31737694280270026233612613 5950817677550629918802365)
                    ·
                      refine ⟨2231556629081486219550887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5950817677550629918802365 2231556629081486219550887)
                      ·
                        rfl

theorem cell23_4345941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 1, 1, 2, 4, 3].length) (baseStart_4345941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4345941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4345941 prefixEnd_4345941 := by exact prefixLift 4345941
  have htrace : WordTrace (prefixWord ++ tailWord_4345941) baseStart_4345941 baseEnd_4345941 := by
    simpa [prefixWord, tailWord_4345941, baseEnd_4345941] using wordTrace_append hprefix tailTrace_4345941
  have hstable : (prefixWord ++ tailWord_4345941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4345941).length < 2 ^ (prefixWord ++ tailWord_4345941).sum := by decide
  have hdescent : baseEnd_4345941 < baseStart_4345941 := by decide
  rcases family_descends (prefixWord ++ tailWord_4345941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4345942 : List Nat := [5, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2]
def baseStart_4345942 : Nat := 118140960795 + 4345942 * 2 ^ 59
def prefixEnd_4345942 : Nat := 4983230072969 + 3 ^ 40 * 4345942 * 2
def baseEnd_4345942 : Nat := 2231557142562140715638383

theorem tailTrace_4345942 : CollatzResearch.WordTrace tailWord_4345942 prefixEnd_4345942 2231557142562140715638383 := by
  unfold tailWord_4345942
  simp only [CollatzResearch.WordTrace]
  refine ⟨9906845426337614790433505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 105673017880934557764624053 9906845426337614790433505)
  ·
    refine ⟨7430134069753211092825129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9906845426337614790433505 7430134069753211092825129)
    ·
      refine ⟨5572600552314908319618847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7430134069753211092825129 5572600552314908319618847)
      ·
        refine ⟨8358900828472362479428271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5572600552314908319618847 8358900828472362479428271)
        ·
          refine ⟨12538351242708543719142407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8358900828472362479428271 12538351242708543719142407)
          ·
            refine ⟨18807526864062815578713611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12538351242708543719142407 18807526864062815578713611)
            ·
              refine ⟨28211290296094223368070417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18807526864062815578713611 28211290296094223368070417)
              ·
                refine ⟨21158467722070667526052813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28211290296094223368070417 21158467722070667526052813)
                ·
                  refine ⟨7934425395776500322269805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21158467722070667526052813 7934425395776500322269805)
                  ·
                    refine ⟨2975409523416187620851177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7934425395776500322269805 2975409523416187620851177)
                    ·
                      refine ⟨2231557142562140715638383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2975409523416187620851177 2231557142562140715638383)
                      ·
                        rfl

theorem cell23_4345942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2].length) (baseStart_4345942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4345942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4345942 prefixEnd_4345942 := by exact prefixLift 4345942
  have htrace : WordTrace (prefixWord ++ tailWord_4345942) baseStart_4345942 baseEnd_4345942 := by
    simpa [prefixWord, tailWord_4345942, baseEnd_4345942] using wordTrace_append hprefix tailTrace_4345942
  have hstable : (prefixWord ++ tailWord_4345942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4345942).length < 2 ^ (prefixWord ++ tailWord_4345942).sum := by decide
  have hdescent : baseEnd_4345942 < baseStart_4345942 := by decide
  rcases family_descends (prefixWord ++ tailWord_4345942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4345955 : List Nat := [1, 1, 1, 5, 1, 1, 4, 3, 2, 2, 2]
def baseStart_4345955 : Nat := 118140960795 + 4345955 * 2 ^ 59
def prefixEnd_4345955 : Nat := 4983230072969 + 3 ^ 40 * 4345955 * 2
def baseEnd_4345955 : Nat := 2231563817810649164775823

theorem tailTrace_4345955 : CollatzResearch.WordTrace tailWord_4345955 prefixEnd_4345955 2231563817810649164775823 := by
  unfold tailWord_4345955
  simp only [CollatzResearch.WordTrace]
  refine ⟨158510000970354739867159319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105673333980236493244772879 158510000970354739867159319)
  ·
    refine ⟨237765001455532109800738979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158510000970354739867159319 237765001455532109800738979)
    ·
      refine ⟨356647502183298164701108469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 237765001455532109800738979 356647502183298164701108469)
      ·
        refine ⟨33435703329684202940728919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 356647502183298164701108469 33435703329684202940728919)
        ·
          refine ⟨50153554994526304411093379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33435703329684202940728919 50153554994526304411093379)
          ·
            refine ⟨75230332491789456616640069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50153554994526304411093379 75230332491789456616640069)
            ·
              refine ⟨14105687342210523115620013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 75230332491789456616640069 14105687342210523115620013)
              ·
                refine ⟨5289632753328946168357505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14105687342210523115620013 5289632753328946168357505)
                ·
                  refine ⟨3967224564996709626268129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5289632753328946168357505 3967224564996709626268129)
                  ·
                    refine ⟨2975418423747532219701097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3967224564996709626268129 2975418423747532219701097)
                    ·
                      refine ⟨2231563817810649164775823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2975418423747532219701097 2231563817810649164775823)
                      ·
                        rfl

theorem cell23_4345955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 4, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 4, 3, 2, 2, 2].length) (baseStart_4345955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4345955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4345955 prefixEnd_4345955 := by exact prefixLift 4345955
  have htrace : WordTrace (prefixWord ++ tailWord_4345955) baseStart_4345955 baseEnd_4345955 := by
    simpa [prefixWord, tailWord_4345955, baseEnd_4345955] using wordTrace_append hprefix tailTrace_4345955
  have hstable : (prefixWord ++ tailWord_4345955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4345955).length < 2 ^ (prefixWord ++ tailWord_4345955).sum := by decide
  have hdescent : baseEnd_4345955 < baseStart_4345955 := by decide
  rcases family_descends (prefixWord ++ tailWord_4345955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4345991 : List Nat := [1, 1, 4, 2, 1, 1, 2, 4, 2, 5]
def baseStart_4345991 : Nat := 118140960795 + 4345991 * 2 ^ 59
def prefixEnd_4345991 : Nat := 4983230072969 + 3 ^ 40 * 4345991 * 2
def baseEnd_4345991 : Nat := 743860767704737007975219

theorem tailTrace_4345991 : CollatzResearch.WordTrace tailWord_4345991 prefixEnd_4345991 743860767704737007975219 := by
  unfold tailWord_4345991
  simp only [CollatzResearch.WordTrace]
  refine ⟨158511313998224318015469827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105674209332149545343646551 158511313998224318015469827)
  ·
    refine ⟨237766970997336477023204741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158511313998224318015469827 237766970997336477023204741)
    ·
      refine ⟨44581307062000589441850889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 237766970997336477023204741 44581307062000589441850889)
      ·
        refine ⟨33435980296500442081388167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44581307062000589441850889 33435980296500442081388167)
        ·
          refine ⟨50153970444750663122082251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33435980296500442081388167 50153970444750663122082251)
          ·
            refine ⟨75230955667125994683123377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50153970444750663122082251 75230955667125994683123377)
            ·
              refine ⟨56423216750344496012342533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 75230955667125994683123377 56423216750344496012342533)
              ·
                refine ⟨10579353140689593002314225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 56423216750344496012342533 10579353140689593002314225)
                ·
                  refine ⟨7934514855517194751735669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10579353140689593002314225 7934514855517194751735669)
                  ·
                    refine ⟨743860767704737007975219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7934514855517194751735669 743860767704737007975219)
                    ·
                      rfl

theorem cell23_4345991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 4, 2, 5].length) (baseStart_4345991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4345991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4345991 prefixEnd_4345991 := by exact prefixLift 4345991
  have htrace : WordTrace (prefixWord ++ tailWord_4345991) baseStart_4345991 baseEnd_4345991 := by
    simpa [prefixWord, tailWord_4345991, baseEnd_4345991] using wordTrace_append hprefix tailTrace_4345991
  have hstable : (prefixWord ++ tailWord_4345991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4345991).length < 2 ^ (prefixWord ++ tailWord_4345991).sum := by decide
  have hdescent : baseEnd_4345991 < baseStart_4345991 := by decide
  rcases family_descends (prefixWord ++ tailWord_4345991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4346048 : List Nat := [2, 1, 1, 2, 5, 1, 1, 1, 4, 2, 3]
def baseStart_4346048 : Nat := 118140960795 + 4346048 * 2 ^ 59
def prefixEnd_4346048 : Nat := 4983230072969 + 3 ^ 40 * 4346048 * 2
def baseEnd_4346048 : Nat := 2231611571511517300912895

theorem tailTrace_4346048 : CollatzResearch.WordTrace tailWord_4346048 prefixEnd_4346048 2231611571511517300912895 := by
  unfold tailWord_4346048
  simp only [CollatzResearch.WordTrace]
  refine ⟨79256696479508908375147399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105675595306011877833529865 79256696479508908375147399)
  ·
    refine ⟨118885044719263362562721099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79256696479508908375147399 118885044719263362562721099)
    ·
      refine ⟨178327567078895043844081649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118885044719263362562721099 178327567078895043844081649)
      ·
        refine ⟨133745675309171282883061237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 178327567078895043844081649 133745675309171282883061237)
        ·
          refine ⟨12538657060234807770286991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 133745675309171282883061237 12538657060234807770286991)
          ·
            refine ⟨18807985590352211655430487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12538657060234807770286991 18807985590352211655430487)
            ·
              refine ⟨28211978385528317483145731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18807985590352211655430487 28211978385528317483145731)
              ·
                refine ⟨42317967578292476224718597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28211978385528317483145731 42317967578292476224718597)
                ·
                  refine ⟨7934618920929839292134737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 42317967578292476224718597 7934618920929839292134737)
                  ·
                    refine ⟨5950964190697379469101053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7934618920929839292134737 5950964190697379469101053)
                    ·
                      refine ⟨2231611571511517300912895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5950964190697379469101053 2231611571511517300912895)
                      ·
                        rfl

theorem cell23_4346048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 1, 1, 4, 2, 3].length) (baseStart_4346048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4346048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4346048 prefixEnd_4346048 := by exact prefixLift 4346048
  have htrace : WordTrace (prefixWord ++ tailWord_4346048) baseStart_4346048 baseEnd_4346048 := by
    simpa [prefixWord, tailWord_4346048, baseEnd_4346048] using wordTrace_append hprefix tailTrace_4346048
  have hstable : (prefixWord ++ tailWord_4346048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4346048).length < 2 ^ (prefixWord ++ tailWord_4346048).sum := by decide
  have hdescent : baseEnd_4346048 < baseStart_4346048 := by decide
  rcases family_descends (prefixWord ++ tailWord_4346048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4346111 : List Nat := [1, 1, 2, 2, 1, 4, 1, 2, 3, 6]
def baseStart_4346111 : Nat := 118140960795 + 4346111 * 2 ^ 59
def prefixEnd_4346111 : Nat := 4983230072969 + 3 ^ 40 * 4346111 * 2
def baseEnd_4346111 : Nat := 743881306930916851475035

theorem tailTrace_4346111 : CollatzResearch.WordTrace tailWord_4346111 prefixEnd_4346111 743881306930916851475035 := by
  unfold tailWord_4346111
  simp only [CollatzResearch.WordTrace]
  refine ⟨158515690757789578509838187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105677127171859719006558791 158515690757789578509838187)
  ·
    refine ⟨237773536136684367764757281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158515690757789578509838187 237773536136684367764757281)
    ·
      refine ⟨178330152102513275823567961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 237773536136684367764757281 178330152102513275823567961)
      ·
        refine ⟨133747614076884956867675971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 178330152102513275823567961 133747614076884956867675971)
        ·
          refine ⟨200621421115327435301513957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 133747614076884956867675971 200621421115327435301513957)
          ·
            refine ⟨37616516459123894119033867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 200621421115327435301513957 37616516459123894119033867)
            ·
              refine ⟨56424774688685841178550801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37616516459123894119033867 56424774688685841178550801)
              ·
                refine ⟨42318581016514380883913101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 56424774688685841178550801 42318581016514380883913101)
                ·
                  refine ⟨15869467881192892831467413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 42318581016514380883913101 15869467881192892831467413)
                  ·
                    refine ⟨743881306930916851475035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15869467881192892831467413 743881306930916851475035)
                    ·
                      rfl

theorem cell23_4346111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 2, 3, 6].length) (baseStart_4346111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4346111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4346111 prefixEnd_4346111 := by exact prefixLift 4346111
  have htrace : WordTrace (prefixWord ++ tailWord_4346111) baseStart_4346111 baseEnd_4346111 := by
    simpa [prefixWord, tailWord_4346111, baseEnd_4346111] using wordTrace_append hprefix tailTrace_4346111
  have hstable : (prefixWord ++ tailWord_4346111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4346111).length < 2 ^ (prefixWord ++ tailWord_4346111).sum := by decide
  have hdescent : baseEnd_4346111 < baseStart_4346111 := by decide
  rcases family_descends (prefixWord ++ tailWord_4346111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4346131 : List Nat := [1, 1, 1, 2, 1, 3, 1, 5, 1, 1, 6]
def baseStart_4346131 : Nat := 118140960795 + 4346131 * 2 ^ 59
def prefixEnd_4346131 : Nat := 4983230072969 + 3 ^ 40 * 4346131 * 2
def baseEnd_4346131 : Nat := 2231654190405840476175013

theorem tailTrace_4346131 : CollatzResearch.WordTrace tailWord_4346131 prefixEnd_4346131 2231654190405840476175013 := by
  unfold tailWord_4346131
  simp only [CollatzResearch.WordTrace]
  refine ⟨158516420217717121925566247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105677613478478081283710831 158516420217717121925566247)
  ·
    refine ⟨237774630326575682888349371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158516420217717121925566247 237774630326575682888349371)
    ·
      refine ⟨356661945489863524332524057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 237774630326575682888349371 356661945489863524332524057)
      ·
        refine ⟨267496459117397643249393043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 356661945489863524332524057 267496459117397643249393043)
        ·
          refine ⟨401244688676096464874089565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 267496459117397643249393043 401244688676096464874089565)
          ·
            refine ⟨150466758253536174327783587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 401244688676096464874089565 150466758253536174327783587)
            ·
              refine ⟨225700137380304261491675381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 150466758253536174327783587 225700137380304261491675381)
              ·
                refine ⟨21159387879403524514844567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 225700137380304261491675381 21159387879403524514844567)
                ·
                  refine ⟨31739081819105286772266851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21159387879403524514844567 31739081819105286772266851)
                  ·
                    refine ⟨47608622728657930158400277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 31739081819105286772266851 47608622728657930158400277)
                    ·
                      refine ⟨2231654190405840476175013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 47608622728657930158400277 2231654190405840476175013)
                      ·
                        rfl

theorem cell23_4346131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 5, 1, 1, 6].length) (baseStart_4346131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4346131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4346131 prefixEnd_4346131 := by exact prefixLift 4346131
  have htrace : WordTrace (prefixWord ++ tailWord_4346131) baseStart_4346131 baseEnd_4346131 := by
    simpa [prefixWord, tailWord_4346131, baseEnd_4346131] using wordTrace_append hprefix tailTrace_4346131
  have hstable : (prefixWord ++ tailWord_4346131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4346131).length < 2 ^ (prefixWord ++ tailWord_4346131).sum := by decide
  have hdescent : baseEnd_4346131 < baseStart_4346131 := by decide
  rcases family_descends (prefixWord ++ tailWord_4346131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4346149 : List Nat := [1, 3, 1, 2, 6, 1, 2, 1, 1, 5]
def baseStart_4346149 : Nat := 118140960795 + 4346149 * 2 ^ 59
def prefixEnd_4346149 : Nat := 4983230072969 + 3 ^ 40 * 4346149 * 2
def baseEnd_4346149 : Nat := 743887811019207135249977

theorem tailTrace_4346149 : CollatzResearch.WordTrace tailWord_4346149 prefixEnd_4346149 743887811019207135249977 := by
  unfold tailWord_4346149
  simp only [CollatzResearch.WordTrace]
  refine ⟨158517076731651910999721501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105678051154434607333147667 158517076731651910999721501)
  ·
    refine ⟨59443903774369466624895563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 158517076731651910999721501 59443903774369466624895563)
    ·
      refine ⟨89165855661554199937343345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59443903774369466624895563 89165855661554199937343345)
      ·
        refine ⟨66874391746165649953007509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89165855661554199937343345 66874391746165649953007509)
        ·
          refine ⟨3134737113101514841547227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 66874391746165649953007509 3134737113101514841547227)
          ·
            refine ⟨4702105669652272262320841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3134737113101514841547227 4702105669652272262320841)
            ·
              refine ⟨3526579252239204196740631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4702105669652272262320841 3526579252239204196740631)
              ·
                refine ⟨5289868878358806295110947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3526579252239204196740631 5289868878358806295110947)
                ·
                  refine ⟨7934803317538209442666421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5289868878358806295110947 7934803317538209442666421)
                  ·
                    refine ⟨743887811019207135249977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7934803317538209442666421 743887811019207135249977)
                    ·
                      rfl

theorem cell23_4346149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 6, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 6, 1, 2, 1, 1, 5].length) (baseStart_4346149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4346149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4346149 prefixEnd_4346149 := by exact prefixLift 4346149
  have htrace : WordTrace (prefixWord ++ tailWord_4346149) baseStart_4346149 baseEnd_4346149 := by
    simpa [prefixWord, tailWord_4346149, baseEnd_4346149] using wordTrace_append hprefix tailTrace_4346149
  have hstable : (prefixWord ++ tailWord_4346149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4346149).length < 2 ^ (prefixWord ++ tailWord_4346149).sum := by decide
  have hdescent : baseEnd_4346149 < baseStart_4346149 := by decide
  rcases family_descends (prefixWord ++ tailWord_4346149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4346152 : List Nat := [2, 1, 5, 1, 3, 1, 1, 3, 1, 1, 4]
def baseStart_4346152 : Nat := 118140960795 + 4346152 * 2 ^ 59
def prefixEnd_4346152 : Nat := 4983230072969 + 3 ^ 40 * 4346152 * 2
def baseEnd_4346152 : Nat := 2231664973499584894012417

theorem tailTrace_4346152 : CollatzResearch.WordTrace tailWord_4346152 prefixEnd_4346152 2231664973499584894012417 := by
  unfold tailWord_4346152
  simp only [CollatzResearch.WordTrace]
  refine ⟨79258593075320521256040355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105678124100427361674720473 79258593075320521256040355)
  ·
    refine ⟨118887889612980781884060533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79258593075320521256040355 118887889612980781884060533)
    ·
      refine ⟨11145739651216948301630675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 118887889612980781884060533 11145739651216948301630675)
      ·
        refine ⟨16718609476825422452446013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11145739651216948301630675 16718609476825422452446013)
        ·
          refine ⟨6269478553809533419667255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16718609476825422452446013 6269478553809533419667255)
          ·
            refine ⟨9404217830714300129500883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6269478553809533419667255 9404217830714300129500883)
            ·
              refine ⟨14106326746071450194251325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9404217830714300129500883 14106326746071450194251325)
              ·
                refine ⟨5289872529776793822844247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14106326746071450194251325 5289872529776793822844247)
                ·
                  refine ⟨7934808794665190734266371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5289872529776793822844247 7934808794665190734266371)
                  ·
                    refine ⟨11902213191997786101399557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7934808794665190734266371 11902213191997786101399557)
                    ·
                      refine ⟨2231664973499584894012417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11902213191997786101399557 2231664973499584894012417)
                      ·
                        rfl

theorem cell23_4346152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 1, 3, 1, 1, 4].length) (baseStart_4346152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4346152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4346152 prefixEnd_4346152 := by exact prefixLift 4346152
  have htrace : WordTrace (prefixWord ++ tailWord_4346152) baseStart_4346152 baseEnd_4346152 := by
    simpa [prefixWord, tailWord_4346152, baseEnd_4346152] using wordTrace_append hprefix tailTrace_4346152
  have hstable : (prefixWord ++ tailWord_4346152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4346152).length < 2 ^ (prefixWord ++ tailWord_4346152).sum := by decide
  have hdescent : baseEnd_4346152 < baseStart_4346152 := by decide
  rcases family_descends (prefixWord ++ tailWord_4346152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4346168 : List Nat := [2, 1, 2, 1, 3, 1, 2, 2, 3, 3, 3]
def baseStart_4346168 : Nat := 118140960795 + 4346168 * 2 ^ 59
def prefixEnd_4346168 : Nat := 4983230072969 + 3 ^ 40 * 4346168 * 2
def baseEnd_4346168 : Nat := 2231673189190056831412343

theorem tailTrace_4346168 : CollatzResearch.WordTrace tailWord_4346168 prefixEnd_4346168 2231673189190056831412343 := by
  unfold tailWord_4346168
  simp only [CollatzResearch.WordTrace]
  refine ⟨79258884859291538622331579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105678513145722051496442105 79258884859291538622331579)
  ·
    refine ⟨118888327288937307933497369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79258884859291538622331579 118888327288937307933497369)
    ·
      refine ⟨89166245466702980950123027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 118888327288937307933497369 89166245466702980950123027)
      ·
        refine ⟨133749368200054471425184541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89166245466702980950123027 133749368200054471425184541)
        ·
          refine ⟨50156013075020426784444203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 133749368200054471425184541 50156013075020426784444203)
          ·
            refine ⟨75234019612530640176666305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50156013075020426784444203 75234019612530640176666305)
            ·
              refine ⟨56425514709397980132499729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 75234019612530640176666305 56425514709397980132499729)
              ·
                refine ⟨42319136032048485099374797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 56425514709397980132499729 42319136032048485099374797)
                ·
                  refine ⟨15869676012018181912265549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 42319136032048485099374797 15869676012018181912265549)
                  ·
                    refine ⟨5951128504506818217099581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15869676012018181912265549 5951128504506818217099581)
                    ·
                      refine ⟨2231673189190056831412343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5951128504506818217099581 2231673189190056831412343)
                      ·
                        rfl

theorem cell23_4346168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 2, 3, 3, 3].length) (baseStart_4346168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4346168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4346168 prefixEnd_4346168 := by exact prefixLift 4346168
  have htrace : WordTrace (prefixWord ++ tailWord_4346168) baseStart_4346168 baseEnd_4346168 := by
    simpa [prefixWord, tailWord_4346168, baseEnd_4346168] using wordTrace_append hprefix tailTrace_4346168
  have hstable : (prefixWord ++ tailWord_4346168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4346168).length < 2 ^ (prefixWord ++ tailWord_4346168).sum := by decide
  have hdescent : baseEnd_4346168 < baseStart_4346168 := by decide
  rcases family_descends (prefixWord ++ tailWord_4346168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4346169 : List Nat := [1, 2, 1, 6, 1, 2, 2, 1, 3, 2, 2]
def baseStart_4346169 : Nat := 118140960795 + 4346169 * 2 ^ 59
def prefixEnd_4346169 : Nat := 4983230072969 + 3 ^ 40 * 4346169 * 2
def baseEnd_4346169 : Nat := 2231673702670711327499839

theorem tailTrace_4346169 : CollatzResearch.WordTrace tailWord_4346169 prefixEnd_4346169 2231673702670711327499839 := by
  unfold tailWord_4346169
  simp only [CollatzResearch.WordTrace]
  refine ⟨158517806191579454415449561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105678537461052969610299707 158517806191579454415449561)
  ·
    refine ⟨118888354643684590811587171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 158517806191579454415449561 118888354643684590811587171)
    ·
      refine ⟨178332531965526886217380757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118888354643684590811587171 178332531965526886217380757)
      ·
        refine ⟨8359337435884072791439723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 178332531965526886217380757 8359337435884072791439723)
        ·
          refine ⟨12539006153826109187159585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8359337435884072791439723 12539006153826109187159585)
          ·
            refine ⟨9404254615369581890369689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12539006153826109187159585 9404254615369581890369689)
            ·
              refine ⟨7053190961527186417777267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9404254615369581890369689 7053190961527186417777267)
              ·
                refine ⟨10579786442290779626665901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7053190961527186417777267 10579786442290779626665901)
                ·
                  refine ⟨3967419915859042359999713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10579786442290779626665901 3967419915859042359999713)
                  ·
                    refine ⟨2975564936894281769999785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3967419915859042359999713 2975564936894281769999785)
                    ·
                      refine ⟨2231673702670711327499839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2975564936894281769999785 2231673702670711327499839)
                      ·
                        rfl

theorem cell23_4346169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 2, 1, 3, 2, 2].length) (baseStart_4346169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4346169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4346169 prefixEnd_4346169 := by exact prefixLift 4346169
  have htrace : WordTrace (prefixWord ++ tailWord_4346169) baseStart_4346169 baseEnd_4346169 := by
    simpa [prefixWord, tailWord_4346169, baseEnd_4346169] using wordTrace_append hprefix tailTrace_4346169
  have hstable : (prefixWord ++ tailWord_4346169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4346169).length < 2 ^ (prefixWord ++ tailWord_4346169).sum := by decide
  have hdescent : baseEnd_4346169 < baseStart_4346169 := by decide
  rcases family_descends (prefixWord ++ tailWord_4346169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4346191 : List Nat := [1, 1, 2, 1, 1, 2, 1, 3, 1, 2, 8]
def baseStart_4346191 : Nat := 118140960795 + 4346191 * 2 ^ 59
def prefixEnd_4346191 : Nat := 4983230072969 + 3 ^ 40 * 4346191 * 2
def baseEnd_4346191 : Nat := 2231684999245110241424737

theorem tailTrace_4346191 : CollatzResearch.WordTrace tailWord_4346191 prefixEnd_4346191 2231684999245110241424737 := by
  unfold tailWord_4346191
  simp only [CollatzResearch.WordTrace]
  refine ⟨158518608597499752172750427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105679072398333168115166951 158518608597499752172750427)
  ·
    refine ⟨237777912896249628259125641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158518608597499752172750427 237777912896249628259125641)
    ·
      refine ⟨178333434672187221194344231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 237777912896249628259125641 178333434672187221194344231)
      ·
        refine ⟨267500152008280831791516347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 178333434672187221194344231 267500152008280831791516347)
        ·
          refine ⟨401250228012421247687274521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 267500152008280831791516347 401250228012421247687274521)
          ·
            refine ⟨300937671009315935765455891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 401250228012421247687274521 300937671009315935765455891)
            ·
              refine ⟨451406506513973903648183837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 300937671009315935765455891 451406506513973903648183837)
              ·
                refine ⟨169277439942740213868068939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 451406506513973903648183837 169277439942740213868068939)
                ·
                  refine ⟨253916159914110320802103409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 169277439942740213868068939 253916159914110320802103409)
                  ·
                    refine ⟨190437119935582740601577557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 253916159914110320802103409 190437119935582740601577557)
                    ·
                      refine ⟨2231684999245110241424737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 190437119935582740601577557 2231684999245110241424737)
                      ·
                        rfl

theorem cell23_4346191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 3, 1, 2, 8].length) (baseStart_4346191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4346191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4346191 prefixEnd_4346191 := by exact prefixLift 4346191
  have htrace : WordTrace (prefixWord ++ tailWord_4346191) baseStart_4346191 baseEnd_4346191 := by
    simpa [prefixWord, tailWord_4346191, baseEnd_4346191] using wordTrace_append hprefix tailTrace_4346191
  have hstable : (prefixWord ++ tailWord_4346191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4346191).length < 2 ^ (prefixWord ++ tailWord_4346191).sum := by decide
  have hdescent : baseEnd_4346191 < baseStart_4346191 := by decide
  rcases family_descends (prefixWord ++ tailWord_4346191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4346212 : List Nat := [2, 3, 1, 1, 3, 1, 1, 5, 1, 3, 2]
def baseStart_4346212 : Nat := 118140960795 + 4346212 * 2 ^ 59
def prefixEnd_4346212 : Nat := 4983230072969 + 3 ^ 40 * 4346212 * 2
def baseEnd_4346212 : Nat := 2231695782338854659262141

theorem tailTrace_4346212 : CollatzResearch.WordTrace tailWord_4346212 prefixEnd_4346212 2231695782338854659262141 := by
  unfold tailWord_4346212
  simp only [CollatzResearch.WordTrace]
  refine ⟨79259687265211836379632445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105679583020282448506176593 79259687265211836379632445)
  ·
    refine ⟨29722382724454438642362167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79259687265211836379632445 29722382724454438642362167)
    ·
      refine ⟨44583574086681657963543251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29722382724454438642362167 44583574086681657963543251)
      ·
        refine ⟨66875361130022486945314877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44583574086681657963543251 66875361130022486945314877)
        ·
          refine ⟨25078260423758432604493079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 66875361130022486945314877 25078260423758432604493079)
          ·
            refine ⟨37617390635637648906739619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25078260423758432604493079 37617390635637648906739619)
            ·
              refine ⟨56426085953456473360109429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37617390635637648906739619 56426085953456473360109429)
              ·
                refine ⟨5289945558136544377510259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 56426085953456473360109429 5289945558136544377510259)
                ·
                  refine ⟨7934918337204816566265389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5289945558136544377510259 7934918337204816566265389)
                  ·
                    refine ⟨2975594376451806212349521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7934918337204816566265389 2975594376451806212349521)
                    ·
                      refine ⟨2231695782338854659262141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2975594376451806212349521 2231695782338854659262141)
                      ·
                        rfl

theorem cell23_4346212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 5, 1, 3, 2].length) (baseStart_4346212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4346212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4346212 prefixEnd_4346212 := by exact prefixLift 4346212
  have htrace : WordTrace (prefixWord ++ tailWord_4346212) baseStart_4346212 baseEnd_4346212 := by
    simpa [prefixWord, tailWord_4346212, baseEnd_4346212] using wordTrace_append hprefix tailTrace_4346212
  have hstable : (prefixWord ++ tailWord_4346212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4346212).length < 2 ^ (prefixWord ++ tailWord_4346212).sum := by decide
  have hdescent : baseEnd_4346212 < baseStart_4346212 := by decide
  rcases family_descends (prefixWord ++ tailWord_4346212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4346248 : List Nat := [2, 1, 3, 3, 1, 1, 2, 1, 9]
def baseStart_4346248 : Nat := 118140960795 + 4346248 * 2 ^ 59
def prefixEnd_4346248 : Nat := 4983230072969 + 3 ^ 40 * 4346248 * 2
def baseEnd_4346248 : Nat := 247968251960268502045775

theorem tailTrace_4346248 : CollatzResearch.WordTrace tailWord_4346248 prefixEnd_4346248 247968251960268502045775 := by
  unfold tailWord_4346248
  simp only [CollatzResearch.WordTrace]
  refine ⟨79260343779146625453787699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105680458372195500605050265 79260343779146625453787699)
  ·
    refine ⟨118890515668719938180681549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79260343779146625453787699 118890515668719938180681549)
    ·
      refine ⟨44583943375769976817755581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 118890515668719938180681549 44583943375769976817755581)
      ·
        refine ⟨16718978765913741306658343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44583943375769976817755581 16718978765913741306658343)
        ·
          refine ⟨25078468148870611959987515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16718978765913741306658343 25078468148870611959987515)
          ·
            refine ⟨37617702223305917939981273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25078468148870611959987515 37617702223305917939981273)
            ·
              refine ⟨28213276667479438454985955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37617702223305917939981273 28213276667479438454985955)
              ·
                refine ⟨42319915001219157682478933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28213276667479438454985955 42319915001219157682478933)
                ·
                  refine ⟨247968251960268502045775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 42319915001219157682478933 247968251960268502045775)
                  ·
                    rfl

theorem cell23_4346248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 2, 1, 9].length) (baseStart_4346248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4346248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4346248 prefixEnd_4346248 := by exact prefixLift 4346248
  have htrace : WordTrace (prefixWord ++ tailWord_4346248) baseStart_4346248 baseEnd_4346248 := by
    simpa [prefixWord, tailWord_4346248, baseEnd_4346248] using wordTrace_append hprefix tailTrace_4346248
  have hstable : (prefixWord ++ tailWord_4346248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4346248).length < 2 ^ (prefixWord ++ tailWord_4346248).sum := by decide
  have hdescent : baseEnd_4346248 < baseStart_4346248 := by decide
  rcases family_descends (prefixWord ++ tailWord_4346248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4346265 : List Nat := [1, 2, 1, 2, 1, 4, 2, 5, 5]
def baseStart_4346265 : Nat := 118140960795 + 4346265 * 2 ^ 59
def prefixEnd_4346265 : Nat := 4983230072969 + 3 ^ 40 * 4346265 * 2
def baseEnd_4346265 : Nat := 247969221868171439099933

theorem tailTrace_4346265 : CollatzResearch.WordTrace tailWord_4346265 prefixEnd_4346265 247969221868171439099933 := by
  unfold tailWord_4346265
  simp only [CollatzResearch.WordTrace]
  refine ⟨158521307599231662810944249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105680871732821108540629499 158521307599231662810944249)
  ·
    refine ⟨118890980699423747108208187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 158521307599231662810944249 118890980699423747108208187)
    ·
      refine ⟨178336471049135620662312281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118890980699423747108208187 178336471049135620662312281)
      ·
        refine ⟨133752353286851715496734211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 178336471049135620662312281 133752353286851715496734211)
        ·
          refine ⟨200628529930277573245101317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 133752353286851715496734211 200628529930277573245101317)
          ·
            refine ⟨37617849361927044983456497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 200628529930277573245101317 37617849361927044983456497)
            ·
              refine ⟨28213387021445283737592373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37617849361927044983456497 28213387021445283737592373)
              ·
                refine ⟨2645005033260495350399285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 28213387021445283737592373 2645005033260495350399285)
                ·
                  refine ⟨247969221868171439099933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2645005033260495350399285 247969221868171439099933)
                  ·
                    rfl

theorem cell23_4346265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 2, 5, 5].length) (baseStart_4346265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4346265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4346265 prefixEnd_4346265 := by exact prefixLift 4346265
  have htrace : WordTrace (prefixWord ++ tailWord_4346265) baseStart_4346265 baseEnd_4346265 := by
    simpa [prefixWord, tailWord_4346265, baseEnd_4346265] using wordTrace_append hprefix tailTrace_4346265
  have hstable : (prefixWord ++ tailWord_4346265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4346265).length < 2 ^ (prefixWord ++ tailWord_4346265).sum := by decide
  have hdescent : baseEnd_4346265 < baseStart_4346265 := by decide
  rcases family_descends (prefixWord ++ tailWord_4346265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
