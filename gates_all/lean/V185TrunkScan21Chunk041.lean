import V185TrunkScan21Chunk040

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental

namespace V185TrunkScan21Incremental

def tailWord_496415 : List Nat := [1, 1, 2, 4, 2, 4, 2, 2, 3]
def baseStart_496415 : Nat := 118140960795 + 496415 * 2 ^ 59
def prefixEnd_496415 : Nat := 4983230072969 + 3 ^ 40 * 496415 * 2
def baseEnd_496415 : Nat := 113288666267458003435349

theorem tailTrace_496415 : CollatzResearch.WordTrace tailWord_496415 prefixEnd_496415 113288666267458003435349 := by
  unfold tailWord_496415
  simp only [CollatzResearch.WordTrace]
  refine ⟨18105742496580710777354699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12070494997720473851569799 18105742496580710777354699)
  ·
    refine ⟨27158613744871066166032049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18105742496580710777354699 27158613744871066166032049)
    ·
      refine ⟨20368960308653299624524037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27158613744871066166032049 20368960308653299624524037)
      ·
        refine ⟨3819180057872493679598257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20368960308653299624524037 3819180057872493679598257)
        ·
          refine ⟨2864385043404370259698693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3819180057872493679598257 2864385043404370259698693)
          ·
            refine ⟨537072195638319423693505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2864385043404370259698693 537072195638319423693505)
            ·
              refine ⟨402804146728739567770129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 537072195638319423693505 402804146728739567770129)
              ·
                refine ⟨302103110046554675827597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 402804146728739567770129 302103110046554675827597)
                ·
                  refine ⟨113288666267458003435349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 302103110046554675827597 113288666267458003435349)
                  ·
                    rfl

theorem cell21_496415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 4, 2, 2, 3].length) (baseStart_496415 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_496415 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_496415 prefixEnd_496415 := by exact prefixLift 496415
  have htrace : WordTrace (prefixWord ++ tailWord_496415) baseStart_496415 baseEnd_496415 := by
    simpa [prefixWord, tailWord_496415, baseEnd_496415] using wordTrace_append hprefix tailTrace_496415
  have hstable : (prefixWord ++ tailWord_496415).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_496415).length < 2 ^ (prefixWord ++ tailWord_496415).sum := by decide
  have hdescent : baseEnd_496415 < baseStart_496415 := by decide
  rcases family_descends (prefixWord ++ tailWord_496415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_496440 : List Nat := [2, 1, 2, 1, 3, 2, 3, 2, 5]
def baseStart_496440 : Nat := 118140960795 + 496440 * 2 ^ 59
def prefixEnd_496440 : Nat := 4983230072969 + 3 ^ 40 * 496440 * 2
def baseEnd_496440 : Nat := 113294371608063515518631

theorem tailTrace_496440 : CollatzResearch.WordTrace tailWord_496440 prefixEnd_496440 113294371608063515518631 := by
  unfold tailWord_496440
  simp only [CollatzResearch.WordTrace]
  refine ⟨9053327160745070023507387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12071102880993426698009849 9053327160745070023507387)
  ·
    refine ⟨13579990741117605035261081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9053327160745070023507387 13579990741117605035261081)
    ·
      refine ⟨10184993055838203776445811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13579990741117605035261081 10184993055838203776445811)
      ·
        refine ⟨15277489583757305664668717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10184993055838203776445811 15277489583757305664668717)
        ·
          refine ⟨5729058593908989624250769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15277489583757305664668717 5729058593908989624250769)
          ·
            refine ⟨4296793945431742218188077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5729058593908989624250769 4296793945431742218188077)
            ·
              refine ⟨1611297729536903331820529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4296793945431742218188077 1611297729536903331820529)
              ·
                refine ⟨1208473297152677498865397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1611297729536903331820529 1208473297152677498865397)
                ·
                  refine ⟨113294371608063515518631, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1208473297152677498865397 113294371608063515518631)
                  ·
                    rfl

theorem cell21_496440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 3, 2, 5].length) (baseStart_496440 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_496440 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_496440 prefixEnd_496440 := by exact prefixLift 496440
  have htrace : WordTrace (prefixWord ++ tailWord_496440) baseStart_496440 baseEnd_496440 := by
    simpa [prefixWord, tailWord_496440, baseEnd_496440] using wordTrace_append hprefix tailTrace_496440
  have hstable : (prefixWord ++ tailWord_496440).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_496440).length < 2 ^ (prefixWord ++ tailWord_496440).sum := by decide
  have hdescent : baseEnd_496440 < baseStart_496440 := by decide
  rcases family_descends (prefixWord ++ tailWord_496440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_496457 : List Nat := [1, 2, 1, 1, 2, 5, 1, 5, 3]
def baseStart_496457 : Nat := 118140960795 + 496457 * 2 ^ 59
def prefixEnd_496457 : Nat := 4983230072969 + 3 ^ 40 * 496457 * 2
def baseEnd_496457 : Nat := 113298251239675263735263

theorem tailTrace_496457 : CollatzResearch.WordTrace tailWord_496457 prefixEnd_496457 113298251239675263735263 := by
  unfold tailWord_496457
  simp only [CollatzResearch.WordTrace]
  refine ⟨18107274362428551950383625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12071516241619034633589083 18107274362428551950383625)
  ·
    refine ⟨13580455771821413962787719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18107274362428551950383625 13580455771821413962787719)
    ·
      refine ⟨20370683657732120944181579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13580455771821413962787719 20370683657732120944181579)
      ·
        refine ⟨30556025486598181416272369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20370683657732120944181579 30556025486598181416272369)
        ·
          refine ⟨22917019114948636062204277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30556025486598181416272369 22917019114948636062204277)
          ·
            refine ⟨2148470542026434630831651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 22917019114948636062204277 2148470542026434630831651)
            ·
              refine ⟨3222705813039651946247477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2148470542026434630831651 3222705813039651946247477)
              ·
                refine ⟨302128669972467369960701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3222705813039651946247477 302128669972467369960701)
                ·
                  refine ⟨113298251239675263735263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 302128669972467369960701 113298251239675263735263)
                  ·
                    rfl

theorem cell21_496457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 1, 5, 3].length) (baseStart_496457 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_496457 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_496457 prefixEnd_496457 := by exact prefixLift 496457
  have htrace : WordTrace (prefixWord ++ tailWord_496457) baseStart_496457 baseEnd_496457 := by
    simpa [prefixWord, tailWord_496457, baseEnd_496457] using wordTrace_append hprefix tailTrace_496457
  have hstable : (prefixWord ++ tailWord_496457).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_496457).length < 2 ^ (prefixWord ++ tailWord_496457).sum := by decide
  have hdescent : baseEnd_496457 < baseStart_496457 := by decide
  rcases family_descends (prefixWord ++ tailWord_496457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_496471 : List Nat := [1, 1, 3, 2, 4, 2, 1, 1, 6]
def baseStart_496471 : Nat := 118140960795 + 496471 * 2 ^ 59
def prefixEnd_496471 : Nat := 4983230072969 + 3 ^ 40 * 496471 * 2
def baseEnd_496471 : Nat := 113301446230414350501901

theorem tailTrace_496471 : CollatzResearch.WordTrace tailWord_496471 prefixEnd_496471 113301446230414350501901 := by
  unfold tailWord_496471
  simp only [CollatzResearch.WordTrace]
  refine ⟨18107784984377832341393267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12071856656251888227595511 18107784984377832341393267)
  ·
    refine ⟨27161677476566748512089901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18107784984377832341393267 27161677476566748512089901)
    ·
      refine ⟨10185629053712530692033713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27161677476566748512089901 10185629053712530692033713)
      ·
        refine ⟨7639221790284398019025285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10185629053712530692033713 7639221790284398019025285)
        ·
          refine ⟨1432354085678324628567241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7639221790284398019025285 1432354085678324628567241)
          ·
            refine ⟨1074265564258743471425431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1432354085678324628567241 1074265564258743471425431)
            ·
              refine ⟨1611398346388115207138147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1074265564258743471425431 1611398346388115207138147)
              ·
                refine ⟨2417097519582172810707221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1611398346388115207138147 2417097519582172810707221)
                ·
                  refine ⟨113301446230414350501901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2417097519582172810707221 113301446230414350501901)
                  ·
                    rfl

theorem cell21_496471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 1, 1, 6].length) (baseStart_496471 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_496471 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_496471 prefixEnd_496471 := by exact prefixLift 496471
  have htrace : WordTrace (prefixWord ++ tailWord_496471) baseStart_496471 baseEnd_496471 := by
    simpa [prefixWord, tailWord_496471, baseEnd_496471] using wordTrace_append hprefix tailTrace_496471
  have hstable : (prefixWord ++ tailWord_496471).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_496471).length < 2 ^ (prefixWord ++ tailWord_496471).sum := by decide
  have hdescent : baseEnd_496471 < baseStart_496471 := by decide
  rcases family_descends (prefixWord ++ tailWord_496471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_496533 : List Nat := [1, 3, 2, 1, 1, 6, 1, 1, 5]
def baseStart_496533 : Nat := 118140960795 + 496533 * 2 ^ 59
def prefixEnd_496533 : Nat := 4983230072969 + 3 ^ 40 * 496533 * 2
def baseEnd_496533 : Nat := 113315595475116020468441

theorem tailTrace_496533 : CollatzResearch.WordTrace tailWord_496533 prefixEnd_496533 113315595475116020468441 := by
  unfold tailWord_496533
  simp only [CollatzResearch.WordTrace]
  refine ⟨18110046310153216930150253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12073364206768811286766835 18110046310153216930150253)
  ·
    refine ⟨6791267366307456348806345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18110046310153216930150253 6791267366307456348806345)
    ·
      refine ⟨5093450524730592261604759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6791267366307456348806345 5093450524730592261604759)
      ·
        refine ⟨7640175787095888392407139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5093450524730592261604759 7640175787095888392407139)
        ·
          refine ⟨11460263680643832588610709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7640175787095888392407139 11460263680643832588610709)
          ·
            refine ⟨537199860030179652591127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 11460263680643832588610709 537199860030179652591127)
            ·
              refine ⟨805799790045269478886691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 537199860030179652591127 805799790045269478886691)
              ·
                refine ⟨1208699685067904218330037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 805799790045269478886691 1208699685067904218330037)
                ·
                  refine ⟨113315595475116020468441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1208699685067904218330037 113315595475116020468441)
                  ·
                    rfl

theorem cell21_496533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 6, 1, 1, 5].length) (baseStart_496533 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_496533 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_496533 prefixEnd_496533 := by exact prefixLift 496533
  have htrace : WordTrace (prefixWord ++ tailWord_496533) baseStart_496533 baseEnd_496533 := by
    simpa [prefixWord, tailWord_496533, baseEnd_496533] using wordTrace_append hprefix tailTrace_496533
  have hstable : (prefixWord ++ tailWord_496533).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_496533).length < 2 ^ (prefixWord ++ tailWord_496533).sum := by decide
  have hdescent : baseEnd_496533 < baseStart_496533 := by decide
  rcases family_descends (prefixWord ++ tailWord_496533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_496575 : List Nat := [1, 1, 2, 2, 2, 1, 2, 1, 9]
def baseStart_496575 : Nat := 118140960795 + 496575 * 2 ^ 59
def prefixEnd_496575 : Nat := 4983230072969 + 3 ^ 40 * 496575 * 2
def baseEnd_496575 : Nat := 113325180447333280768355

theorem tailTrace_496575 : CollatzResearch.WordTrace tailWord_496575 prefixEnd_496575 113325180447333280768355 := by
  unfold tailWord_496575
  simp only [CollatzResearch.WordTrace]
  refine ⟨18111578176001058103179179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12074385450667372068786119 18111578176001058103179179)
  ·
    refine ⟨27167367264001587154768769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18111578176001058103179179 27167367264001587154768769)
    ·
      refine ⟨20375525448001190366076577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27167367264001587154768769 20375525448001190366076577)
      ·
        refine ⟨15281644086000892774557433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20375525448001190366076577 15281644086000892774557433)
        ·
          refine ⟨11461233064500669580918075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15281644086000892774557433 11461233064500669580918075)
          ·
            refine ⟨17191849596751004371377113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11461233064500669580918075 17191849596751004371377113)
            ·
              refine ⟨12893887197563253278532835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17191849596751004371377113 12893887197563253278532835)
              ·
                refine ⟨19340830796344879917799253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12893887197563253278532835 19340830796344879917799253)
                ·
                  refine ⟨113325180447333280768355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 19340830796344879917799253 113325180447333280768355)
                  ·
                    rfl

theorem cell21_496575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 1, 9].length) (baseStart_496575 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_496575 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_496575 prefixEnd_496575 := by exact prefixLift 496575
  have htrace : WordTrace (prefixWord ++ tailWord_496575) baseStart_496575 baseEnd_496575 := by
    simpa [prefixWord, tailWord_496575, baseEnd_496575] using wordTrace_append hprefix tailTrace_496575
  have hstable : (prefixWord ++ tailWord_496575).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_496575).length < 2 ^ (prefixWord ++ tailWord_496575).sum := by decide
  have hdescent : baseEnd_496575 < baseStart_496575 := by decide
  rcases family_descends (prefixWord ++ tailWord_496575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_496584 : List Nat := [2, 1, 3, 1, 6, 1, 2, 2, 3]
def baseStart_496584 : Nat := 118140960795 + 496584 * 2 ^ 59
def prefixEnd_496584 : Nat := 4983230072969 + 3 ^ 40 * 496584 * 2
def baseEnd_496584 : Nat := 113327234369951265118337

theorem tailTrace_496584 : CollatzResearch.WordTrace tailWord_496584 prefixEnd_496584 113327234369951265118337 := by
  unfold tailWord_496584
  simp only [CollatzResearch.WordTrace]
  refine ⟨9055953216484226320128403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12074604288645635093504537 9055953216484226320128403)
  ·
    refine ⟨13583929824726339480192605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9055953216484226320128403 13583929824726339480192605)
    ·
      refine ⟨5093973684272377305072227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13583929824726339480192605 5093973684272377305072227)
      ·
        refine ⟨7640960526408565957608341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5093973684272377305072227 7640960526408565957608341)
        ·
          refine ⟨358170024675401529262891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 7640960526408565957608341 358170024675401529262891)
          ·
            refine ⟨537255037013102293894337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 358170024675401529262891 537255037013102293894337)
            ·
              refine ⟨402941277759826720420753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 537255037013102293894337 402941277759826720420753)
              ·
                refine ⟨302205958319870040315565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 402941277759826720420753 302205958319870040315565)
                ·
                  refine ⟨113327234369951265118337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 302205958319870040315565 113327234369951265118337)
                  ·
                    rfl

theorem cell21_496584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 6, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 6, 1, 2, 2, 3].length) (baseStart_496584 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_496584 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_496584 prefixEnd_496584 := by exact prefixLift 496584
  have htrace : WordTrace (prefixWord ++ tailWord_496584) baseStart_496584 baseEnd_496584 := by
    simpa [prefixWord, tailWord_496584, baseEnd_496584] using wordTrace_append hprefix tailTrace_496584
  have hstable : (prefixWord ++ tailWord_496584).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_496584).length < 2 ^ (prefixWord ++ tailWord_496584).sum := by decide
  have hdescent : baseEnd_496584 < baseStart_496584 := by decide
  rcases family_descends (prefixWord ++ tailWord_496584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_496702 : List Nat := [4, 2, 1, 3, 1, 3, 1, 1, 5]
def baseStart_496702 : Nat := 118140960795 + 496702 * 2 ^ 59
def prefixEnd_496702 : Nat := 4983230072969 + 3 ^ 40 * 496702 * 2
def baseEnd_496702 : Nat := 113354163577609282151429

theorem tailTrace_496702 : CollatzResearch.WordTrace tailWord_496702 prefixEnd_496702 113354163577609282151429 := by
  unfold tailWord_496702
  simp only [CollatzResearch.WordTrace]
  refine ⟨2264526280817619849131545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12077473497693972528701573 2264526280817619849131545)
  ·
    refine ⟨1698394710613214886848659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2264526280817619849131545 1698394710613214886848659)
    ·
      refine ⟨2547592065919822330272989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1698394710613214886848659 2547592065919822330272989)
      ·
        refine ⟨955347024719933373852371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2547592065919822330272989 955347024719933373852371)
        ·
          refine ⟨1433020537079900060778557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 955347024719933373852371 1433020537079900060778557)
          ·
            refine ⟨537382701404962522791959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1433020537079900060778557 537382701404962522791959)
            ·
              refine ⟨806074052107443784187939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 537382701404962522791959 806074052107443784187939)
              ·
                refine ⟨1209111078161165676281909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 806074052107443784187939 1209111078161165676281909)
                ·
                  refine ⟨113354163577609282151429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1209111078161165676281909 113354163577609282151429)
                  ·
                    rfl

theorem cell21_496702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 3, 1, 1, 5].length) (baseStart_496702 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_496702 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_496702 prefixEnd_496702 := by exact prefixLift 496702
  have htrace : WordTrace (prefixWord ++ tailWord_496702) baseStart_496702 baseEnd_496702 := by
    simpa [prefixWord, tailWord_496702, baseEnd_496702] using wordTrace_append hprefix tailTrace_496702
  have hstable : (prefixWord ++ tailWord_496702).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_496702).length < 2 ^ (prefixWord ++ tailWord_496702).sum := by decide
  have hdescent : baseEnd_496702 < baseStart_496702 := by decide
  rcases family_descends (prefixWord ++ tailWord_496702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_496727 : List Nat := [1, 1, 3, 2, 2, 1, 1, 3, 7]
def baseStart_496727 : Nat := 118140960795 + 496727 * 2 ^ 59
def prefixEnd_496727 : Nat := 4983230072969 + 3 ^ 40 * 496727 * 2
def baseEnd_496727 : Nat := 113359868918214794234711

theorem tailTrace_496727 : CollatzResearch.WordTrace tailWord_496727 prefixEnd_496727 113359868918214794234711 := by
  unfold tailWord_496727
  simp only [CollatzResearch.WordTrace]
  refine ⟨18117122071450388062712435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12078081380966925375141623 18117122071450388062712435)
  ·
    refine ⟨27175683107175582094068653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18117122071450388062712435 27175683107175582094068653)
    ·
      refine ⟨10190881165190843285275745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27175683107175582094068653 10190881165190843285275745)
      ·
        refine ⟨7643160873893132463956809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10190881165190843285275745 7643160873893132463956809)
        ·
          refine ⟨5732370655419849347967607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7643160873893132463956809 5732370655419849347967607)
          ·
            refine ⟨8598555983129774021951411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5732370655419849347967607 8598555983129774021951411)
            ·
              refine ⟨12897833974694661032927117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8598555983129774021951411 12897833974694661032927117)
              ·
                refine ⟨4836687740510497887347669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12897833974694661032927117 4836687740510497887347669)
                ·
                  refine ⟨113359868918214794234711, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4836687740510497887347669 113359868918214794234711)
                  ·
                    rfl

theorem cell21_496727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 3, 7].length) (baseStart_496727 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_496727 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_496727 prefixEnd_496727 := by exact prefixLift 496727
  have htrace : WordTrace (prefixWord ++ tailWord_496727) baseStart_496727 baseEnd_496727 := by
    simpa [prefixWord, tailWord_496727, baseEnd_496727] using wordTrace_append hprefix tailTrace_496727
  have hstable : (prefixWord ++ tailWord_496727).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_496727).length < 2 ^ (prefixWord ++ tailWord_496727).sum := by decide
  have hdescent : baseEnd_496727 < baseStart_496727 := by decide
  rcases family_descends (prefixWord ++ tailWord_496727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_496865 : List Nat := [1, 2, 3, 1, 3, 4, 7]
def baseStart_496865 : Nat := 118140960795 + 496865 * 2 ^ 59
def prefixEnd_496865 : Nat := 4983230072969 + 3 ^ 40 * 496865 * 2
def baseEnd_496865 : Nat := 12599040266484135659381

theorem tailTrace_496865 : CollatzResearch.WordTrace tailWord_496865 prefixEnd_496865 12599040266484135659381 := by
  unfold tailWord_496865
  simp only [CollatzResearch.WordTrace]
  refine ⟨18122155344950437631236049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12081436896633625087490699 18122155344950437631236049)
  ·
    refine ⟨13591616508712828223427037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18122155344950437631236049 13591616508712828223427037)
    ·
      refine ⟨5096856190767310583785139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13591616508712828223427037 5096856190767310583785139)
      ·
        refine ⟨7645284286150965875677709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5096856190767310583785139 7645284286150965875677709)
        ·
          refine ⟨2866981607306612203379141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7645284286150965875677709 2866981607306612203379141)
          ·
            refine ⟨537559051369989788133589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2866981607306612203379141 537559051369989788133589)
            ·
              refine ⟨12599040266484135659381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 537559051369989788133589 12599040266484135659381)
              ·
                rfl

theorem cell21_496865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 4, 7].length) (baseStart_496865 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_496865 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_496865 prefixEnd_496865 := by exact prefixLift 496865
  have htrace : WordTrace (prefixWord ++ tailWord_496865) baseStart_496865 baseEnd_496865 := by
    simpa [prefixWord, tailWord_496865, baseEnd_496865] using wordTrace_append hprefix tailTrace_496865
  have hstable : (prefixWord ++ tailWord_496865).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_496865).length < 2 ^ (prefixWord ++ tailWord_496865).sum := by decide
  have hdescent : baseEnd_496865 < baseStart_496865 := by decide
  rcases family_descends (prefixWord ++ tailWord_496865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_496871 : List Nat := [1, 1, 5, 3, 2, 1, 3, 2, 3]
def baseStart_496871 : Nat := 118140960795 + 496871 * 2 ^ 59
def prefixEnd_496871 : Nat := 4983230072969 + 3 ^ 40 * 496871 * 2
def baseEnd_496871 : Nat := 113392731680102543834417

theorem tailTrace_496871 : CollatzResearch.WordTrace tailWord_496871 prefixEnd_496871 113392731680102543834417 := by
  unfold tailWord_496871
  simp only [CollatzResearch.WordTrace]
  refine ⟨18122374182928700655954467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12081582788619133770636311 18122374182928700655954467)
  ·
    refine ⟨27183561274393050983931701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18122374182928700655954467 27183561274393050983931701)
    ·
      refine ⟨2548458869474348529743597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 27183561274393050983931701 2548458869474348529743597)
      ·
        refine ⟨955672076052880698653849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2548458869474348529743597 955672076052880698653849)
        ·
          refine ⟨716754057039660523990387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 955672076052880698653849 716754057039660523990387)
          ·
            refine ⟨1075131085559490785985581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 716754057039660523990387 1075131085559490785985581)
            ·
              refine ⟨403174157084809044744593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1075131085559490785985581 403174157084809044744593)
              ·
                refine ⟨302380617813606783558445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 403174157084809044744593 302380617813606783558445)
                ·
                  refine ⟨113392731680102543834417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 302380617813606783558445 113392731680102543834417)
                  ·
                    rfl

theorem cell21_496871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 3, 2, 3].length) (baseStart_496871 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_496871 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_496871 prefixEnd_496871 := by exact prefixLift 496871
  have htrace : WordTrace (prefixWord ++ tailWord_496871) baseStart_496871 baseEnd_496871 := by
    simpa [prefixWord, tailWord_496871, baseEnd_496871] using wordTrace_append hprefix tailTrace_496871
  have hstable : (prefixWord ++ tailWord_496871).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_496871).length < 2 ^ (prefixWord ++ tailWord_496871).sum := by decide
  have hdescent : baseEnd_496871 < baseStart_496871 := by decide
  rcases family_descends (prefixWord ++ tailWord_496871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_496882 : List Nat := [3, 2, 1, 3, 3, 1, 2, 6]
def baseStart_496882 : Nat := 118140960795 + 496882 * 2 ^ 59
def prefixEnd_496882 : Nat := 4983230072969 + 3 ^ 40 * 496882 * 2
def baseEnd_496882 : Nat := 37798414009989656383687

theorem tailTrace_496882 : CollatzResearch.WordTrace tailWord_496882 prefixEnd_496882 37798414009989656383687 := by
  unfold tailWord_496882
  simp only [CollatzResearch.WordTrace]
  refine ⟨4530693846472212383651225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12081850257259233023069933 4530693846472212383651225)
  ·
    refine ⟨3398020384854159287738419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4530693846472212383651225 3398020384854159287738419)
    ·
      refine ⟨5097030577281238931607629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3398020384854159287738419 5097030577281238931607629)
      ·
        refine ⟨1911386466480464599352861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5097030577281238931607629 1911386466480464599352861)
        ·
          refine ⟨716769924930174224757323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1911386466480464599352861 716769924930174224757323)
          ·
            refine ⟨1075154887395261337135985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 716769924930174224757323 1075154887395261337135985)
            ·
              refine ⟨806366165546446002851989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1075154887395261337135985 806366165546446002851989)
              ·
                refine ⟨37798414009989656383687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 806366165546446002851989 37798414009989656383687)
                ·
                  rfl

theorem cell21_496882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 2, 6].length) (baseStart_496882 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_496882 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_496882 prefixEnd_496882 := by exact prefixLift 496882
  have htrace : WordTrace (prefixWord ++ tailWord_496882) baseStart_496882 baseEnd_496882 := by
    simpa [prefixWord, tailWord_496882, baseEnd_496882] using wordTrace_append hprefix tailTrace_496882
  have hstable : (prefixWord ++ tailWord_496882).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_496882).length < 2 ^ (prefixWord ++ tailWord_496882).sum := by decide
  have hdescent : baseEnd_496882 < baseStart_496882 := by decide
  rcases family_descends (prefixWord ++ tailWord_496882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_496930 : List Nat := [3, 3, 1, 1, 4, 1, 1, 4, 3]
def baseStart_496930 : Nat := 118140960795 + 496930 * 2 ^ 59
def prefixEnd_496930 : Nat := 4983230072969 + 3 ^ 40 * 496930 * 2
def baseEnd_496930 : Nat := 113406196283931552350963

theorem tailTrace_496930 : CollatzResearch.WordTrace tailWord_496930 prefixEnd_496930 113406196283931552350963 := by
  unfold tailWord_496930
  simp only [CollatzResearch.WordTrace]
  refine ⟨4531131522428738433088061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12083017393143302488234829 4531131522428738433088061)
  ·
    refine ⟨1699174320910776912408023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4531131522428738433088061 1699174320910776912408023)
    ·
      refine ⟨2548761481366165368612035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1699174320910776912408023 2548761481366165368612035)
      ·
        refine ⟨3823142222049248052918053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2548761481366165368612035 3823142222049248052918053)
        ·
          refine ⟨716839166634234009922135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3823142222049248052918053 716839166634234009922135)
          ·
            refine ⟨1075258749951351014883203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 716839166634234009922135 1075258749951351014883203)
            ·
              refine ⟨1612888124927026522324805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1075258749951351014883203 1612888124927026522324805)
              ·
                refine ⟨302416523423817472935901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1612888124927026522324805 302416523423817472935901)
                ·
                  refine ⟨113406196283931552350963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 302416523423817472935901 113406196283931552350963)
                  ·
                    rfl

theorem cell21_496930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 1, 4, 3].length) (baseStart_496930 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_496930 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_496930 prefixEnd_496930 := by exact prefixLift 496930
  have htrace : WordTrace (prefixWord ++ tailWord_496930) baseStart_496930 baseEnd_496930 := by
    simpa [prefixWord, tailWord_496930, baseEnd_496930] using wordTrace_append hprefix tailTrace_496930
  have hstable : (prefixWord ++ tailWord_496930).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_496930).length < 2 ^ (prefixWord ++ tailWord_496930).sum := by decide
  have hdescent : baseEnd_496930 < baseStart_496930 := by decide
  rcases family_descends (prefixWord ++ tailWord_496930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_496958 : List Nat := [4, 2, 1, 2, 1, 1, 5, 5]
def baseStart_496958 : Nat := 118140960795 + 496958 * 2 ^ 59
def prefixEnd_496958 : Nat := 4983230072969 + 3 ^ 40 * 496958 * 2
def baseEnd_496958 : Nat := 37804195421803241961413

theorem tailTrace_496958 : CollatzResearch.WordTrace tailWord_496958 prefixEnd_496958 37804195421803241961413 := by
  unfold tailWord_496958
  simp only [CollatzResearch.WordTrace]
  refine ⟨2265693416701689314296441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12083698222409009676247685 2265693416701689314296441)
  ·
    refine ⟨1699270062526266985722331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2265693416701689314296441 1699270062526266985722331)
    ·
      refine ⟨2548905093789400478583497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1699270062526266985722331 2548905093789400478583497)
      ·
        refine ⟨1911678820342050358937623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2548905093789400478583497 1911678820342050358937623)
        ·
          refine ⟨2867518230513075538406435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1911678820342050358937623 2867518230513075538406435)
          ·
            refine ⟨4301277345769613307609653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2867518230513075538406435 4301277345769613307609653)
            ·
              refine ⟨403244751165901247588405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4301277345769613307609653 403244751165901247588405)
              ·
                refine ⟨37804195421803241961413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 403244751165901247588405 37804195421803241961413)
                ·
                  rfl

theorem cell21_496958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 5, 5].length) (baseStart_496958 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_496958 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_496958 prefixEnd_496958 := by exact prefixLift 496958
  have htrace : WordTrace (prefixWord ++ tailWord_496958) baseStart_496958 baseEnd_496958 := by
    simpa [prefixWord, tailWord_496958, baseEnd_496958] using wordTrace_append hprefix tailTrace_496958
  have hstable : (prefixWord ++ tailWord_496958).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_496958).length < 2 ^ (prefixWord ++ tailWord_496958).sum := by decide
  have hdescent : baseEnd_496958 < baseStart_496958 := by decide
  rcases family_descends (prefixWord ++ tailWord_496958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_497017 : List Nat := [1, 2, 1, 3, 2, 1, 6, 5]
def baseStart_497017 : Nat := 118140960795 + 497017 * 2 ^ 59
def prefixEnd_497017 : Nat := 4983230072969 + 3 ^ 40 * 497017 * 2
def baseEnd_497017 : Nat := 37808683623079578133595

theorem tailTrace_497017 : CollatzResearch.WordTrace tailWord_497017 prefixEnd_497017 37808683623079578133595 := by
  unfold tailWord_497017
  simp only [CollatzResearch.WordTrace]
  refine ⟨18127699240399767590769305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12085132826933178393846203 18127699240399767590769305)
  ·
    refine ⟨13595774430299825693076979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18127699240399767590769305 13595774430299825693076979)
    ·
      refine ⟨20393661645449738539615469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13595774430299825693076979 20393661645449738539615469)
      ·
        refine ⟨7647623117043651952355801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20393661645449738539615469 7647623117043651952355801)
        ·
          refine ⟨5735717337782738964266851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7647623117043651952355801 5735717337782738964266851)
          ·
            refine ⟨8603576006674108446400277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5735717337782738964266851 8603576006674108446400277)
            ·
              refine ⟨403292625312848833425013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 8603576006674108446400277 403292625312848833425013)
              ·
                refine ⟨37808683623079578133595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 403292625312848833425013 37808683623079578133595)
                ·
                  rfl

theorem cell21_497017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 6, 5].length) (baseStart_497017 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_497017 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_497017 prefixEnd_497017 := by exact prefixLift 497017
  have htrace : WordTrace (prefixWord ++ tailWord_497017) baseStart_497017 baseEnd_497017 := by
    simpa [prefixWord, tailWord_497017, baseEnd_497017] using wordTrace_append hprefix tailTrace_497017
  have hstable : (prefixWord ++ tailWord_497017).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_497017).length < 2 ^ (prefixWord ++ tailWord_497017).sum := by decide
  have hdescent : baseEnd_497017 < baseStart_497017 := by decide
  rcases family_descends (prefixWord ++ tailWord_497017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_497054 : List Nat := [4, 3, 1, 2, 2, 2, 2, 1, 4]
def baseStart_497054 : Nat := 118140960795 + 497054 * 2 ^ 59
def prefixEnd_497054 : Nat := 4983230072969 + 3 ^ 40 * 497054 * 2
def baseEnd_497054 : Nat := 113434494773334892284043

theorem tailTrace_497054 : CollatzResearch.WordTrace tailWord_497054 prefixEnd_497054 113434494773334892284043 := by
  unfold tailWord_497054
  simp only [CollatzResearch.WordTrace]
  refine ⟨2266131092658215363733277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12086032494177148606577477 2266131092658215363733277)
  ·
    refine ⟨849799159746830761399979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2266131092658215363733277 849799159746830761399979)
    ·
      refine ⟨1274698739620246142099969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 849799159746830761399979 1274698739620246142099969)
      ·
        refine ⟨956024054715184606574977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1274698739620246142099969 956024054715184606574977)
        ·
          refine ⟨717018041036388454931233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 956024054715184606574977 717018041036388454931233)
          ·
            refine ⟨537763530777291341198425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 717018041036388454931233 537763530777291341198425)
            ·
              refine ⟨403322648082968505898819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 537763530777291341198425 403322648082968505898819)
              ·
                refine ⟨604983972124452758848229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 403322648082968505898819 604983972124452758848229)
                ·
                  refine ⟨113434494773334892284043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 604983972124452758848229 113434494773334892284043)
                  ·
                    rfl

theorem cell21_497054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 2, 2, 1, 4].length) (baseStart_497054 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_497054 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_497054 prefixEnd_497054 := by exact prefixLift 497054
  have htrace : WordTrace (prefixWord ++ tailWord_497054) baseStart_497054 baseEnd_497054 := by
    simpa [prefixWord, tailWord_497054, baseEnd_497054] using wordTrace_append hprefix tailTrace_497054
  have hstable : (prefixWord ++ tailWord_497054).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_497054).length < 2 ^ (prefixWord ++ tailWord_497054).sum := by decide
  have hdescent : baseEnd_497054 < baseStart_497054 := by decide
  rcases family_descends (prefixWord ++ tailWord_497054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_497110 : List Nat := [5, 2, 1, 1, 1, 2, 3, 6]
def baseStart_497110 : Nat := 118140960795 + 497110 * 2 ^ 59
def prefixEnd_497110 : Nat := 4983230072969 + 3 ^ 40 * 497110 * 2
def baseEnd_497110 : Nat := 37815758245430413116865

theorem tailTrace_497110 : CollatzResearch.WordTrace tailWord_497110 prefixEnd_497110 37815758245430413116865 := by
  unfold tailWord_497110
  simp only [CollatzResearch.WordTrace]
  refine ⟨1133193201816427779619049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 12087394152708562982603189 1133193201816427779619049)
  ·
    refine ⟨849894901362320834714287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1133193201816427779619049 849894901362320834714287)
    ·
      refine ⟨1274842352043481252071431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 849894901362320834714287 1274842352043481252071431)
      ·
        refine ⟨1912263528065221878107147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1274842352043481252071431 1912263528065221878107147)
        ·
          refine ⟨2868395292097832817160721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1912263528065221878107147 2868395292097832817160721)
          ·
            refine ⟨2151296469073374612870541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2868395292097832817160721 2151296469073374612870541)
            ·
              refine ⟨806736175902515479826453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2151296469073374612870541 806736175902515479826453)
              ·
                refine ⟨37815758245430413116865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 806736175902515479826453 37815758245430413116865)
                ·
                  rfl

theorem cell21_497110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 3, 6].length) (baseStart_497110 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_497110 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_497110 prefixEnd_497110 := by exact prefixLift 497110
  have htrace : WordTrace (prefixWord ++ tailWord_497110) baseStart_497110 baseEnd_497110 := by
    simpa [prefixWord, tailWord_497110, baseEnd_497110] using wordTrace_append hprefix tailTrace_497110
  have hstable : (prefixWord ++ tailWord_497110).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_497110).length < 2 ^ (prefixWord ++ tailWord_497110).sum := by decide
  have hdescent : baseEnd_497110 < baseStart_497110 := by decide
  rcases family_descends (prefixWord ++ tailWord_497110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_497183 : List Nat := [1, 1, 2, 4, 1, 1, 4, 2, 5]
def baseStart_497183 : Nat := 118140960795 + 497183 * 2 ^ 59
def prefixEnd_497183 : Nat := 4983230072969 + 3 ^ 40 * 497183 * 2
def baseEnd_497183 : Nat := 113463934330859334633779

theorem tailTrace_497183 : CollatzResearch.WordTrace tailWord_497183 prefixEnd_497183 113463934330859334633779 := by
  unfold tailWord_497183
  simp only [CollatzResearch.WordTrace]
  refine ⟨18133753757798377941312203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12089169171865585294208135 18133753757798377941312203)
  ·
    refine ⟨27200630636697566911968305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18133753757798377941312203 27200630636697566911968305)
    ·
      refine ⟨20400472977523175183976229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27200630636697566911968305 20400472977523175183976229)
      ·
        refine ⟨3825088683285595346995543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20400472977523175183976229 3825088683285595346995543)
        ·
          refine ⟨5737633024928393020493315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3825088683285595346995543 5737633024928393020493315)
          ·
            refine ⟨8606449537392589530739973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5737633024928393020493315 8606449537392589530739973)
            ·
              refine ⟨1613709288261110537013745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8606449537392589530739973 1613709288261110537013745)
              ·
                refine ⟨1210281966195832902760309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1613709288261110537013745 1210281966195832902760309)
                ·
                  refine ⟨113463934330859334633779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1210281966195832902760309 113463934330859334633779)
                  ·
                    rfl

theorem cell21_497183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 4, 2, 5].length) (baseStart_497183 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_497183 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_497183 prefixEnd_497183 := by exact prefixLift 497183
  have htrace : WordTrace (prefixWord ++ tailWord_497183) baseStart_497183 baseEnd_497183 := by
    simpa [prefixWord, tailWord_497183, baseEnd_497183] using wordTrace_append hprefix tailTrace_497183
  have hstable : (prefixWord ++ tailWord_497183).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_497183).length < 2 ^ (prefixWord ++ tailWord_497183).sum := by decide
  have hdescent : baseEnd_497183 < baseStart_497183 := by decide
  rcases family_descends (prefixWord ++ tailWord_497183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_497228 : List Nat := [2, 2, 1, 3, 1, 3, 1, 8]
def baseStart_497228 : Nat := 118140960795 + 497228 * 2 ^ 59
def prefixEnd_497228 : Nat := 4983230072969 + 3 ^ 40 * 497228 * 2
def baseEnd_497228 : Nat := 37824734647983085461229

theorem tailTrace_497228 : CollatzResearch.WordTrace tailWord_497228 prefixEnd_497228 37824734647983085461229 := by
  unfold tailWord_497228
  simp only [CollatzResearch.WordTrace]
  refine ⟨9067697521317675313350169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12090263361756900417800225 9067697521317675313350169)
  ·
    refine ⟨6800773140988256485012627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9067697521317675313350169 6800773140988256485012627)
    ·
      refine ⟨10201159711482384727518941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6800773140988256485012627 10201159711482384727518941)
      ·
        refine ⟨3825434891805894272819603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10201159711482384727518941 3825434891805894272819603)
        ·
          refine ⟨5738152337708841409229405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3825434891805894272819603 5738152337708841409229405)
          ·
            refine ⟨2151807126640815528461027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5738152337708841409229405 2151807126640815528461027)
            ·
              refine ⟨3227710689961223292691541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2151807126640815528461027 3227710689961223292691541)
              ·
                refine ⟨37824734647983085461229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3227710689961223292691541 37824734647983085461229)
                ·
                  rfl

theorem cell21_497228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 1, 8].length) (baseStart_497228 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_497228 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_497228 prefixEnd_497228 := by exact prefixLift 497228
  have htrace : WordTrace (prefixWord ++ tailWord_497228) baseStart_497228 baseEnd_497228 := by
    simpa [prefixWord, tailWord_497228, baseEnd_497228] using wordTrace_append hprefix tailTrace_497228
  have hstable : (prefixWord ++ tailWord_497228).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_497228).length < 2 ^ (prefixWord ++ tailWord_497228).sum := by decide
  have hdescent : baseEnd_497228 < baseStart_497228 := by decide
  rcases family_descends (prefixWord ++ tailWord_497228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_497310 : List Nat := [4, 3, 1, 1, 1, 3, 2, 3, 3]
def baseStart_497310 : Nat := 118140960795 + 497310 * 2 ^ 59
def prefixEnd_497310 : Nat := 4983230072969 + 3 ^ 40 * 497310 * 2
def baseEnd_497310 : Nat := 113492917461135336016853

theorem tailTrace_497310 : CollatzResearch.WordTrace tailWord_497310 prefixEnd_497310 113492917461135336016853 := by
  unfold tailWord_497310
  simp only [CollatzResearch.WordTrace]
  refine ⟨2267298228542284828898173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12092257218892185754123589 2267298228542284828898173)
  ·
    refine ⟨850236835703356810836815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2267298228542284828898173 850236835703356810836815)
    ·
      refine ⟨1275355253555035216255223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 850236835703356810836815 1275355253555035216255223)
      ·
        refine ⟨1913032880332552824382835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1275355253555035216255223 1913032880332552824382835)
        ·
          refine ⟨2869549320498829236574253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1913032880332552824382835 2869549320498829236574253)
          ·
            refine ⟨1076080995187060963715345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2869549320498829236574253 1076080995187060963715345)
            ·
              refine ⟨807060746390295722786509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1076080995187060963715345 807060746390295722786509)
              ·
                refine ⟨302647779896360896044941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 807060746390295722786509 302647779896360896044941)
                ·
                  refine ⟨113492917461135336016853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 302647779896360896044941 113492917461135336016853)
                  ·
                    rfl

theorem cell21_497310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 2, 3, 3].length) (baseStart_497310 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_497310 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_497310 prefixEnd_497310 := by exact prefixLift 497310
  have htrace : WordTrace (prefixWord ++ tailWord_497310) baseStart_497310 baseEnd_497310 := by
    simpa [prefixWord, tailWord_497310, baseEnd_497310] using wordTrace_append hprefix tailTrace_497310
  have hstable : (prefixWord ++ tailWord_497310).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_497310).length < 2 ^ (prefixWord ++ tailWord_497310).sum := by decide
  have hdescent : baseEnd_497310 < baseStart_497310 := by decide
  rcases family_descends (prefixWord ++ tailWord_497310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_497335 : List Nat := [1, 1, 3, 1, 5, 1, 1, 3, 5]
def baseStart_497335 : Nat := 118140960795 + 497335 * 2 ^ 59
def prefixEnd_497335 : Nat := 4983230072969 + 3 ^ 40 * 497335 * 2
def baseEnd_497335 : Nat := 113498622801740848100135

theorem tailTrace_497335 : CollatzResearch.WordTrace tailWord_497335 prefixEnd_497335 113498622801740848100135 := by
  unfold tailWord_497335
  simp only [CollatzResearch.WordTrace]
  refine ⟨18139297653247707900845459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12092865102165138600563639 18139297653247707900845459)
  ·
    refine ⟨27208946479871561851268189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18139297653247707900845459 27208946479871561851268189)
    ·
      refine ⟨10203354929951835694225571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27208946479871561851268189 10203354929951835694225571)
      ·
        refine ⟨15305032394927753541338357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10203354929951835694225571 15305032394927753541338357)
        ·
          refine ⟨1434846787024476894500471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 15305032394927753541338357 1434846787024476894500471)
          ·
            refine ⟨2152270180536715341750707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1434846787024476894500471 2152270180536715341750707)
            ·
              refine ⟨3228405270805073012626061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2152270180536715341750707 3228405270805073012626061)
              ·
                refine ⟨1210651976551902379734773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3228405270805073012626061 1210651976551902379734773)
                ·
                  refine ⟨113498622801740848100135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1210651976551902379734773 113498622801740848100135)
                  ·
                    rfl

theorem cell21_497335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 1, 3, 5].length) (baseStart_497335 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_497335 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_497335 prefixEnd_497335 := by exact prefixLift 497335
  have htrace : WordTrace (prefixWord ++ tailWord_497335) baseStart_497335 baseEnd_497335 := by
    simpa [prefixWord, tailWord_497335, baseEnd_497335] using wordTrace_append hprefix tailTrace_497335
  have hstable : (prefixWord ++ tailWord_497335).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_497335).length < 2 ^ (prefixWord ++ tailWord_497335).sum := by decide
  have hdescent : baseEnd_497335 < baseStart_497335 := by decide
  rcases family_descends (prefixWord ++ tailWord_497335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_497369 : List Nat := [1, 2, 1, 2, 3, 5, 1, 3, 3]
def baseStart_497369 : Nat := 118140960795 + 497369 * 2 ^ 59
def prefixEnd_497369 : Nat := 4983230072969 + 3 ^ 40 * 497369 * 2
def baseEnd_497369 : Nat := 113506382064964344533399

theorem tailTrace_497369 : CollatzResearch.WordTrace tailWord_497369 prefixEnd_497369 113506382064964344533399 := by
  unfold tailWord_497369
  simp only [CollatzResearch.WordTrace]
  refine ⟨18140537735124531707583161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12093691823416354471722107 18140537735124531707583161)
  ·
    refine ⟨13605403301343398780687371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18140537735124531707583161 13605403301343398780687371)
    ·
      refine ⟨20408104952015098171031057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13605403301343398780687371 20408104952015098171031057)
      ·
        refine ⟨15306078714011323628273293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20408104952015098171031057 15306078714011323628273293)
        ·
          refine ⟨5739779517754246360602485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15306078714011323628273293 5739779517754246360602485)
          ·
            refine ⟨538104329789460596306483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5739779517754246360602485 538104329789460596306483)
            ·
              refine ⟨807156494684190894459725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 538104329789460596306483 807156494684190894459725)
              ·
                refine ⟨302683685506571585422397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 807156494684190894459725 302683685506571585422397)
                ·
                  refine ⟨113506382064964344533399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 302683685506571585422397 113506382064964344533399)
                  ·
                    rfl

theorem cell21_497369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 5, 1, 3, 3].length) (baseStart_497369 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_497369 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_497369 prefixEnd_497369 := by exact prefixLift 497369
  have htrace : WordTrace (prefixWord ++ tailWord_497369) baseStart_497369 baseEnd_497369 := by
    simpa [prefixWord, tailWord_497369, baseEnd_497369] using wordTrace_append hprefix tailTrace_497369
  have hstable : (prefixWord ++ tailWord_497369).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_497369).length < 2 ^ (prefixWord ++ tailWord_497369).sum := by decide
  have hdescent : baseEnd_497369 < baseStart_497369 := by decide
  rcases family_descends (prefixWord ++ tailWord_497369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_497445 : List Nat := [1, 3, 1, 2, 3, 2, 4, 2, 3]
def baseStart_497445 : Nat := 118140960795 + 497445 * 2 ^ 59
def prefixEnd_497445 : Nat := 4983230072969 + 3 ^ 40 * 497445 * 2
def baseEnd_497445 : Nat := 113523726300405101266577

theorem tailTrace_497445 : CollatzResearch.WordTrace tailWord_497445 prefixEnd_497445 113523726300405101266577 := by
  unfold tailWord_497445
  simp only [CollatzResearch.WordTrace]
  refine ⟨18143309682849196687349789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12095539788566131124899859 18143309682849196687349789)
  ·
    refine ⟨6803741131068448757756171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18143309682849196687349789 6803741131068448757756171)
    ·
      refine ⟨10205611696602673136634257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6803741131068448757756171 10205611696602673136634257)
      ·
        refine ⟨7654208772452004852475693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10205611696602673136634257 7654208772452004852475693)
        ·
          refine ⟨2870328289669501819678385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7654208772452004852475693 2870328289669501819678385)
          ·
            refine ⟨2152746217252126364758789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2870328289669501819678385 2152746217252126364758789)
            ·
              refine ⟨403639915734773693392273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2152746217252126364758789 403639915734773693392273)
              ·
                refine ⟨302729936801080270044205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 403639915734773693392273 302729936801080270044205)
                ·
                  refine ⟨113523726300405101266577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 302729936801080270044205 113523726300405101266577)
                  ·
                    rfl

theorem cell21_497445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 4, 2, 3].length) (baseStart_497445 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_497445 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_497445 prefixEnd_497445 := by exact prefixLift 497445
  have htrace : WordTrace (prefixWord ++ tailWord_497445) baseStart_497445 baseEnd_497445 := by
    simpa [prefixWord, tailWord_497445, baseEnd_497445] using wordTrace_append hprefix tailTrace_497445
  have hstable : (prefixWord ++ tailWord_497445).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_497445).length < 2 ^ (prefixWord ++ tailWord_497445).sum := by decide
  have hdescent : baseEnd_497445 < baseStart_497445 := by decide
  rcases family_descends (prefixWord ++ tailWord_497445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_497504 : List Nat := [2, 1, 1, 3, 3, 2, 2, 4, 3]
def baseStart_497504 : Nat := 118140960795 + 497504 * 2 ^ 59
def prefixEnd_497504 : Nat := 4983230072969 + 3 ^ 40 * 497504 * 2
def baseEnd_497504 : Nat := 113537190904234109783123

theorem tailTrace_497504 : CollatzResearch.WordTrace tailWord_497504 prefixEnd_497504 113537190904234109783123 := by
  unfold tailWord_497504
  simp only [CollatzResearch.WordTrace]
  refine ⟨9072730794817724881873783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12096974393090299842498377 9072730794817724881873783)
  ·
    refine ⟨13609096192226587322810675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9072730794817724881873783 13609096192226587322810675)
    ·
      refine ⟨20413644288339880984216013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13609096192226587322810675 20413644288339880984216013)
      ·
        refine ⟨7655116608127455369081005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20413644288339880984216013 7655116608127455369081005)
        ·
          refine ⟨2870668728047795763405377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7655116608127455369081005 2870668728047795763405377)
          ·
            refine ⟨2153001546035846822554033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2870668728047795763405377 2153001546035846822554033)
            ·
              refine ⟨1614751159526885116915525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2153001546035846822554033 1614751159526885116915525)
              ·
                refine ⟨302765842411290959421661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1614751159526885116915525 302765842411290959421661)
                ·
                  refine ⟨113537190904234109783123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 302765842411290959421661 113537190904234109783123)
                  ·
                    rfl

theorem cell21_497504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 2, 4, 3].length) (baseStart_497504 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_497504 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_497504 prefixEnd_497504 := by exact prefixLift 497504
  have htrace : WordTrace (prefixWord ++ tailWord_497504) baseStart_497504 baseEnd_497504 := by
    simpa [prefixWord, tailWord_497504, baseEnd_497504] using wordTrace_append hprefix tailTrace_497504
  have hstable : (prefixWord ++ tailWord_497504).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_497504).length < 2 ^ (prefixWord ++ tailWord_497504).sum := by decide
  have hdescent : baseEnd_497504 < baseStart_497504 := by decide
  rcases family_descends (prefixWord ++ tailWord_497504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_497515 : List Nat := [1, 1, 1, 1, 2, 2, 3, 10]
def baseStart_497515 : Nat := 118140960795 + 497515 * 2 ^ 59
def prefixEnd_497515 : Nat := 4983230072969 + 3 ^ 40 * 497515 * 2
def baseEnd_497515 : Nat := 37846567084700178366589

theorem tailTrace_497515 : CollatzResearch.WordTrace tailWord_497515 prefixEnd_497515 37846567084700178366589 := by
  unfold tailWord_497515
  simp only [CollatzResearch.WordTrace]
  refine ⟨18145862792595598642397999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12097241861730399094931999 18145862792595598642397999)
  ·
    refine ⟨27218794188893397963596999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18145862792595598642397999 27218794188893397963596999)
    ·
      refine ⟨40828191283340096945395499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27218794188893397963596999 40828191283340096945395499)
      ·
        refine ⟨61242286925010145418093249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40828191283340096945395499 61242286925010145418093249)
        ·
          refine ⟨45931715193757609063569937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61242286925010145418093249 45931715193757609063569937)
          ·
            refine ⟨34448786395318206797677453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45931715193757609063569937 34448786395318206797677453)
            ·
              refine ⟨12918294898244327549129045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34448786395318206797677453 12918294898244327549129045)
              ·
                refine ⟨37846567084700178366589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 12918294898244327549129045 37846567084700178366589)
                ·
                  rfl

theorem cell21_497515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 10].length) (baseStart_497515 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_497515 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_497515 prefixEnd_497515 := by exact prefixLift 497515
  have htrace : WordTrace (prefixWord ++ tailWord_497515) baseStart_497515 baseEnd_497515 := by
    simpa [prefixWord, tailWord_497515, baseEnd_497515] using wordTrace_append hprefix tailTrace_497515
  have hstable : (prefixWord ++ tailWord_497515).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_497515).length < 2 ^ (prefixWord ++ tailWord_497515).sum := by decide
  have hdescent : baseEnd_497515 < baseStart_497515 := by decide
  rcases family_descends (prefixWord ++ tailWord_497515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_497569 : List Nat := [1, 2, 3, 4, 3, 1, 2, 1, 4]
def baseStart_497569 : Nat := 118140960795 + 497569 * 2 ^ 59
def prefixEnd_497569 : Nat := 4983230072969 + 3 ^ 40 * 497569 * 2
def baseEnd_497569 : Nat := 113552024789808441199657

theorem tailTrace_497569 : CollatzResearch.WordTrace tailWord_497569 prefixEnd_497569 113552024789808441199657 := by
  unfold tailWord_497569
  simp only [CollatzResearch.WordTrace]
  refine ⟨18147832334399965864863761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12098554889599977243242507 18147832334399965864863761)
  ·
    refine ⟨13610874250799974398647821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18147832334399965864863761 13610874250799974398647821)
    ·
      refine ⟨5104077844049990399492933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13610874250799974398647821 5104077844049990399492933)
      ·
        refine ⟨957014595759373199904925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5104077844049990399492933 957014595759373199904925)
        ·
          refine ⟨358880473409764949964347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 957014595759373199904925 358880473409764949964347)
          ·
            refine ⟨538320710114647424946521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 358880473409764949964347 538320710114647424946521)
            ·
              refine ⟨403740532585985568709891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 538320710114647424946521 403740532585985568709891)
              ·
                refine ⟨605610798878978353064837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 403740532585985568709891 605610798878978353064837)
                ·
                  refine ⟨113552024789808441199657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 605610798878978353064837 113552024789808441199657)
                  ·
                    rfl

theorem cell21_497569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 3, 1, 2, 1, 4].length) (baseStart_497569 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_497569 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_497569 prefixEnd_497569 := by exact prefixLift 497569
  have htrace : WordTrace (prefixWord ++ tailWord_497569) baseStart_497569 baseEnd_497569 := by
    simpa [prefixWord, tailWord_497569, baseEnd_497569] using wordTrace_append hprefix tailTrace_497569
  have hstable : (prefixWord ++ tailWord_497569).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_497569).length < 2 ^ (prefixWord ++ tailWord_497569).sum := by decide
  have hdescent : baseEnd_497569 < baseStart_497569 := by decide
  rcases family_descends (prefixWord ++ tailWord_497569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_497625 : List Nat := [1, 2, 1, 2, 6, 2, 1, 6]
def baseStart_497625 : Nat := 118140960795 + 497625 * 2 ^ 59
def prefixEnd_497625 : Nat := 4983230072969 + 3 ^ 40 * 497625 * 2
def baseEnd_497625 : Nat := 37854934917588262755403

theorem tailTrace_497625 : CollatzResearch.WordTrace tailWord_497625 prefixEnd_497625 37854934917588262755403 := by
  unfold tailWord_497625
  simp only [CollatzResearch.WordTrace]
  refine ⟨18149874822197087428902329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12099916548131391619268219 18149874822197087428902329)
  ·
    refine ⟨13612406116647815571676747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18149874822197087428902329 13612406116647815571676747)
    ·
      refine ⟨20418609174971723357515121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13612406116647815571676747 20418609174971723357515121)
      ·
        refine ⟨15313956881228792518136341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20418609174971723357515121 15313956881228792518136341)
        ·
          refine ⟨717841728807599649287641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 15313956881228792518136341 717841728807599649287641)
          ·
            refine ⟨538381296605699736965731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 717841728807599649287641 538381296605699736965731)
            ·
              refine ⟨807571944908549605448597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 538381296605699736965731 807571944908549605448597)
              ·
                refine ⟨37854934917588262755403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 807571944908549605448597 37854934917588262755403)
                ·
                  rfl

theorem cell21_497625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 2, 1, 6].length) (baseStart_497625 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_497625 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_497625 prefixEnd_497625 := by exact prefixLift 497625
  have htrace : WordTrace (prefixWord ++ tailWord_497625) baseStart_497625 baseEnd_497625 := by
    simpa [prefixWord, tailWord_497625, baseEnd_497625] using wordTrace_append hprefix tailTrace_497625
  have hstable : (prefixWord ++ tailWord_497625).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_497625).length < 2 ^ (prefixWord ++ tailWord_497625).sum := by decide
  have hdescent : baseEnd_497625 < baseStart_497625 := by decide
  rcases family_descends (prefixWord ++ tailWord_497625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_497701 : List Nat := [1, 3, 1, 2, 2, 5, 2, 5]
def baseStart_497701 : Nat := 118140960795 + 497701 * 2 ^ 59
def prefixEnd_497701 : Nat := 4983230072969 + 3 ^ 40 * 497701 * 2
def baseEnd_497701 : Nat := 37860716329401848333129

theorem tailTrace_497701 : CollatzResearch.WordTrace tailWord_497701 prefixEnd_497701 37860716329401848333129 := by
  unfold tailWord_497701
  simp only [CollatzResearch.WordTrace]
  refine ⟨18152646769921752408668957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12101764513281168272445971 18152646769921752408668957)
  ·
    refine ⟨6807242538720657153250859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18152646769921752408668957 6807242538720657153250859)
    ·
      refine ⟨10210863808080985729876289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6807242538720657153250859 10210863808080985729876289)
      ·
        refine ⟨7658147856060739297407217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10210863808080985729876289 7658147856060739297407217)
        ·
          refine ⟨5743610892045554473055413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7658147856060739297407217 5743610892045554473055413)
          ·
            refine ⟨538463521129270731848945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5743610892045554473055413 538463521129270731848945)
            ·
              refine ⟨403847640846953048886709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 538463521129270731848945 403847640846953048886709)
              ·
                refine ⟨37860716329401848333129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 403847640846953048886709 37860716329401848333129)
                ·
                  rfl

theorem cell21_497701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 5, 2, 5].length) (baseStart_497701 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_497701 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_497701 prefixEnd_497701 := by exact prefixLift 497701
  have htrace : WordTrace (prefixWord ++ tailWord_497701) baseStart_497701 baseEnd_497701 := by
    simpa [prefixWord, tailWord_497701, baseEnd_497701] using wordTrace_append hprefix tailTrace_497701
  have hstable : (prefixWord ++ tailWord_497701).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_497701).length < 2 ^ (prefixWord ++ tailWord_497701).sum := by decide
  have hdescent : baseEnd_497701 < baseStart_497701 := by decide
  rcases family_descends (prefixWord ++ tailWord_497701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_497850 : List Nat := [3, 1, 1, 1, 2, 2, 3, 3, 5]
def baseStart_497850 : Nat := 118140960795 + 497850 * 2 ^ 59
def prefixEnd_497850 : Nat := 4983230072969 + 3 ^ 40 * 497850 * 2
def baseEnd_497850 : Nat := 113616152818214397015749

theorem tailTrace_497850 : CollatzResearch.WordTrace tailWord_497850 prefixEnd_497850 113616152818214397015749 := by
  unfold tailWord_497850
  simp only [CollatzResearch.WordTrace]
  refine ⟨4539520311595487713960751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12105387497587967237228669 4539520311595487713960751)
  ·
    refine ⟨6809280467393231570941127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4539520311595487713960751 6809280467393231570941127)
    ·
      refine ⟨10213920701089847356411691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6809280467393231570941127 10213920701089847356411691)
      ·
        refine ⟨15320881051634771034617537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10213920701089847356411691 15320881051634771034617537)
        ·
          refine ⟨11490660788726078275963153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15320881051634771034617537 11490660788726078275963153)
          ·
            refine ⟨8617995591544558706972365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11490660788726078275963153 8617995591544558706972365)
            ·
              refine ⟨3231748346829209515114637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8617995591544558706972365 3231748346829209515114637)
              ·
                refine ⟨1211905630060953568167989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3231748346829209515114637 1211905630060953568167989)
                ·
                  refine ⟨113616152818214397015749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1211905630060953568167989 113616152818214397015749)
                  ·
                    rfl

theorem cell21_497850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 3, 3, 5].length) (baseStart_497850 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_497850 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_497850 prefixEnd_497850 := by exact prefixLift 497850
  have htrace : WordTrace (prefixWord ++ tailWord_497850) baseStart_497850 baseEnd_497850 := by
    simpa [prefixWord, tailWord_497850, baseEnd_497850] using wordTrace_append hprefix tailTrace_497850
  have hstable : (prefixWord ++ tailWord_497850).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_497850).length < 2 ^ (prefixWord ++ tailWord_497850).sum := by decide
  have hdescent : baseEnd_497850 < baseStart_497850 := by decide
  rcases family_descends (prefixWord ++ tailWord_497850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_497901 : List Nat := [1, 5, 1, 2, 4, 1, 1, 1, 5]
def baseStart_497901 : Nat := 118140960795 + 497901 * 2 ^ 59
def prefixEnd_497901 : Nat := 4983230072969 + 3 ^ 40 * 497901 * 2
def baseEnd_497901 : Nat := 113627791713049641665645

theorem tailTrace_497901 : CollatzResearch.WordTrace tailWord_497901 prefixEnd_497901 113627791713049641665645 := by
  unfold tailWord_497901
  simp only [CollatzResearch.WordTrace]
  refine ⟨18159941369197186565949557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12106627579464791043966371 18159941369197186565949557)
  ·
    refine ⟨1702494503362236240557771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 18159941369197186565949557 1702494503362236240557771)
    ·
      refine ⟨2553741755043354360836657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1702494503362236240557771 2553741755043354360836657)
      ·
        refine ⟨1915306316282515770627493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2553741755043354360836657 1915306316282515770627493)
        ·
          refine ⟨359119934302971706992655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1915306316282515770627493 359119934302971706992655)
          ·
            refine ⟨538679901454457560488983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 359119934302971706992655 538679901454457560488983)
            ·
              refine ⟨808019852181686340733475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 538679901454457560488983 808019852181686340733475)
              ·
                refine ⟨1212029778272529511100213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 808019852181686340733475 1212029778272529511100213)
                ·
                  refine ⟨113627791713049641665645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1212029778272529511100213 113627791713049641665645)
                  ·
                    rfl

theorem cell21_497901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 4, 1, 1, 1, 5].length) (baseStart_497901 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_497901 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_497901 prefixEnd_497901 := by exact prefixLift 497901
  have htrace : WordTrace (prefixWord ++ tailWord_497901) baseStart_497901 baseEnd_497901 := by
    simpa [prefixWord, tailWord_497901, baseEnd_497901] using wordTrace_append hprefix tailTrace_497901
  have hstable : (prefixWord ++ tailWord_497901).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_497901).length < 2 ^ (prefixWord ++ tailWord_497901).sum := by decide
  have hdescent : baseEnd_497901 < baseStart_497901 := by decide
  rcases family_descends (prefixWord ++ tailWord_497901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_498019 : List Nat := [1, 1, 1, 5, 2, 1, 1, 6, 3]
def baseStart_498019 : Nat := 118140960795 + 498019 * 2 ^ 59
def prefixEnd_498019 : Nat := 4983230072969 + 3 ^ 40 * 498019 * 2
def baseEnd_498019 : Nat := 113654720920707658698737

theorem tailTrace_498019 : CollatzResearch.WordTrace tailWord_498019 prefixEnd_498019 113654720920707658698737 := by
  unfold tailWord_498019
  simp only [CollatzResearch.WordTrace]
  refine ⟨18164245182769692718745111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12109496788513128479163407 18164245182769692718745111)
  ·
    refine ⟨27246367774154539078117667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18164245182769692718745111 27246367774154539078117667)
    ·
      refine ⟨40869551661231808617176501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27246367774154539078117667 40869551661231808617176501)
      ·
        refine ⟨3831520468240482057860297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 40869551661231808617176501 3831520468240482057860297)
        ·
          refine ⟨2873640351180361543395223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3831520468240482057860297 2873640351180361543395223)
          ·
            refine ⟨4310460526770542315092835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2873640351180361543395223 4310460526770542315092835)
            ·
              refine ⟨6465690790155813472639253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4310460526770542315092835 6465690790155813472639253)
              ·
                refine ⟨303079255788553756529965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 6465690790155813472639253 303079255788553756529965)
                ·
                  refine ⟨113654720920707658698737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 303079255788553756529965 113654720920707658698737)
                  ·
                    rfl

theorem cell21_498019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 6, 3].length) (baseStart_498019 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_498019 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_498019 prefixEnd_498019 := by exact prefixLift 498019
  have htrace : WordTrace (prefixWord ++ tailWord_498019) baseStart_498019 baseEnd_498019 := by
    simpa [prefixWord, tailWord_498019, baseEnd_498019] using wordTrace_append hprefix tailTrace_498019
  have hstable : (prefixWord ++ tailWord_498019).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_498019).length < 2 ^ (prefixWord ++ tailWord_498019).sum := by decide
  have hdescent : baseEnd_498019 < baseStart_498019 := by decide
  rcases family_descends (prefixWord ++ tailWord_498019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_498081 : List Nat := [1, 2, 3, 5, 1, 1, 2, 6]
def baseStart_498081 : Nat := 118140960795 + 498081 * 2 ^ 59
def prefixEnd_498081 : Nat := 4983230072969 + 3 ^ 40 * 498081 * 2
def baseEnd_498081 : Nat := 37889623388469776221759

theorem tailTrace_498081 : CollatzResearch.WordTrace tailWord_498081 prefixEnd_498081 37889623388469776221759 := by
  unfold tailWord_498081
  simp only [CollatzResearch.WordTrace]
  refine ⟨18166506508545077307502097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12111004339030051538334731 18166506508545077307502097)
  ·
    refine ⟨13624879881408807980626573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18166506508545077307502097 13624879881408807980626573)
    ·
      refine ⟨5109329955528302992734965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13624879881408807980626573 5109329955528302992734965)
      ·
        refine ⟨478999683330778405568903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 5109329955528302992734965 478999683330778405568903)
        ·
          refine ⟨718499524996167608353355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 478999683330778405568903 718499524996167608353355)
          ·
            refine ⟨1077749287494251412530033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 718499524996167608353355 1077749287494251412530033)
            ·
              refine ⟨808311965620688559397525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1077749287494251412530033 808311965620688559397525)
              ·
                refine ⟨37889623388469776221759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 808311965620688559397525 37889623388469776221759)
                ·
                  rfl

theorem cell21_498081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 2, 6].length) (baseStart_498081 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_498081 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_498081 prefixEnd_498081 := by exact prefixLift 498081
  have htrace : WordTrace (prefixWord ++ tailWord_498081) baseStart_498081 baseEnd_498081 := by
    simpa [prefixWord, tailWord_498081, baseEnd_498081] using wordTrace_append hprefix tailTrace_498081
  have hstable : (prefixWord ++ tailWord_498081).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_498081).length < 2 ^ (prefixWord ++ tailWord_498081).sum := by decide
  have hdescent : baseEnd_498081 < baseStart_498081 := by decide
  rcases family_descends (prefixWord ++ tailWord_498081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_498154 : List Nat := [3, 1, 3, 1, 3, 1, 1, 1, 7]
def baseStart_498154 : Nat := 118140960795 + 498154 * 2 ^ 59
def prefixEnd_498154 : Nat := 4983230072969 + 3 ^ 40 * 498154 * 2
def baseEnd_498154 : Nat := 113685529759977423948461

theorem tailTrace_498154 : CollatzResearch.WordTrace tailWord_498154 prefixEnd_498154 113685529759977423948461 := by
  unfold tailWord_498154
  simp only [CollatzResearch.WordTrace]
  refine ⟨4542292259320152693727379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12112779358187073849939677 4542292259320152693727379)
  ·
    refine ⟨6813438388980229040591069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4542292259320152693727379 6813438388980229040591069)
    ·
      refine ⟨2555039395867585890221651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6813438388980229040591069 2555039395867585890221651)
      ·
        refine ⟨3832559093801378835332477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2555039395867585890221651 3832559093801378835332477)
        ·
          refine ⟨1437209660175517063249679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3832559093801378835332477 1437209660175517063249679)
          ·
            refine ⟨2155814490263275594874519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1437209660175517063249679 2155814490263275594874519)
            ·
              refine ⟨3233721735394913392311779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2155814490263275594874519 3233721735394913392311779)
              ·
                refine ⟨4850582603092370088467669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3233721735394913392311779 4850582603092370088467669)
                ·
                  refine ⟨113685529759977423948461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4850582603092370088467669 113685529759977423948461)
                  ·
                    rfl

theorem cell21_498154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 1, 1, 7].length) (baseStart_498154 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_498154 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_498154 prefixEnd_498154 := by exact prefixLift 498154
  have htrace : WordTrace (prefixWord ++ tailWord_498154) baseStart_498154 baseEnd_498154 := by
    simpa [prefixWord, tailWord_498154, baseEnd_498154] using wordTrace_append hprefix tailTrace_498154
  have hstable : (prefixWord ++ tailWord_498154).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_498154).length < 2 ^ (prefixWord ++ tailWord_498154).sum := by decide
  have hdescent : baseEnd_498154 < baseStart_498154 := by decide
  rcases family_descends (prefixWord ++ tailWord_498154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_498157 : List Nat := [1, 5, 1, 3, 1, 2, 3, 5]
def baseStart_498157 : Nat := 118140960795 + 498157 * 2 ^ 59
def prefixEnd_498157 : Nat := 4983230072969 + 3 ^ 40 * 498157 * 2
def baseEnd_498157 : Nat := 37895404800283361799485

theorem tailTrace_498157 : CollatzResearch.WordTrace tailWord_498157 prefixEnd_498157 37895404800283361799485 := by
  unfold tailWord_498157
  simp only [CollatzResearch.WordTrace]
  refine ⟨18169278456269742287268725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12112852304179828191512483 18169278456269742287268725)
  ·
    refine ⟨1703369855275288339431443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 18169278456269742287268725 1703369855275288339431443)
    ·
      refine ⟨2555054782912932509147165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1703369855275288339431443 2555054782912932509147165)
      ·
        refine ⟨958145543592349690930187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2555054782912932509147165 958145543592349690930187)
        ·
          refine ⟨1437218315388524536395281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 958145543592349690930187 1437218315388524536395281)
          ·
            refine ⟨1077913736541393402296461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1437218315388524536395281 1077913736541393402296461)
            ·
              refine ⟨404217651203022525861173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1077913736541393402296461 404217651203022525861173)
              ·
                refine ⟨37895404800283361799485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 404217651203022525861173 37895404800283361799485)
                ·
                  rfl

theorem cell21_498157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 3, 5].length) (baseStart_498157 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_498157 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_498157 prefixEnd_498157 := by exact prefixLift 498157
  have htrace : WordTrace (prefixWord ++ tailWord_498157) baseStart_498157 baseEnd_498157 := by
    simpa [prefixWord, tailWord_498157, baseEnd_498157] using wordTrace_append hprefix tailTrace_498157
  have hstable : (prefixWord ++ tailWord_498157).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_498157).length < 2 ^ (prefixWord ++ tailWord_498157).sum := by decide
  have hdescent : baseEnd_498157 < baseStart_498157 := by decide
  rcases family_descends (prefixWord ++ tailWord_498157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_498168 : List Nat := [2, 1, 2, 1, 1, 4, 2, 2, 6]
def baseStart_498168 : Nat := 118140960795 + 498168 * 2 ^ 59
def prefixEnd_498168 : Nat := 4983230072969 + 3 ^ 40 * 498168 * 2
def baseEnd_498168 : Nat := 113688724750716510715099

theorem tailTrace_498168 : CollatzResearch.WordTrace tailWord_498168 prefixEnd_498168 113688724750716510715099 := by
  unfold tailWord_498168
  simp only [CollatzResearch.WordTrace]
  refine ⟨9084839829614945582959579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12113119772819927443946105 9084839829614945582959579)
  ·
    refine ⟨13627259744422418374439369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9084839829614945582959579 13627259744422418374439369)
    ·
      refine ⟨10220444808316813780829527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13627259744422418374439369 10220444808316813780829527)
      ·
        refine ⟨15330667212475220671244291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10220444808316813780829527 15330667212475220671244291)
        ·
          refine ⟨22996000818712831006866437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15330667212475220671244291 22996000818712831006866437)
          ·
            refine ⟨4311750153508655813787457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22996000818712831006866437 4311750153508655813787457)
            ·
              refine ⟨3233812615131491860340593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4311750153508655813787457 3233812615131491860340593)
              ·
                refine ⟨2425359461348618895255445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3233812615131491860340593 2425359461348618895255445)
                ·
                  refine ⟨113688724750716510715099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2425359461348618895255445 113688724750716510715099)
                  ·
                    rfl

theorem cell21_498168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 2, 2, 6].length) (baseStart_498168 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_498168 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_498168 prefixEnd_498168 := by exact prefixLift 498168
  have htrace : WordTrace (prefixWord ++ tailWord_498168) baseStart_498168 baseEnd_498168 := by
    simpa [prefixWord, tailWord_498168, baseEnd_498168] using wordTrace_append hprefix tailTrace_498168
  have hstable : (prefixWord ++ tailWord_498168).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_498168).length < 2 ^ (prefixWord ++ tailWord_498168).sum := by decide
  have hdescent : baseEnd_498168 < baseStart_498168 := by decide
  rcases family_descends (prefixWord ++ tailWord_498168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_498216 : List Nat := [2, 1, 5, 2, 1, 2, 1, 7]
def baseStart_498216 : Nat := 118140960795 + 498216 * 2 ^ 59
def prefixEnd_498216 : Nat := 4983230072969 + 3 ^ 40 * 498216 * 2
def baseEnd_498216 : Nat := 37899893001559697971667

theorem tailTrace_498216 : CollatzResearch.WordTrace tailWord_498216 prefixEnd_498216 37899893001559697971667 := by
  unfold tailWord_498216
  simp only [CollatzResearch.WordTrace]
  refine ⟨9085715181527997681833251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12114286908703996909111001 9085715181527997681833251)
  ·
    refine ⟨13628572772291996522749877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9085715181527997681833251 13628572772291996522749877)
    ·
      refine ⟨1277678697402374674007801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 13628572772291996522749877 1277678697402374674007801)
      ·
        refine ⟨958259023051781005505851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1277678697402374674007801 958259023051781005505851)
        ·
          refine ⟨1437388534577671508258777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 958259023051781005505851 1437388534577671508258777)
          ·
            refine ⟨1078041400933253631194083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1437388534577671508258777 1078041400933253631194083)
            ·
              refine ⟨1617062101399880446791125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1078041400933253631194083 1617062101399880446791125)
              ·
                refine ⟨37899893001559697971667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1617062101399880446791125 37899893001559697971667)
                ·
                  rfl

theorem cell21_498216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 1, 7].length) (baseStart_498216 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_498216 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_498216 prefixEnd_498216 := by exact prefixLift 498216
  have htrace : WordTrace (prefixWord ++ tailWord_498216) baseStart_498216 baseEnd_498216 := by
    simpa [prefixWord, tailWord_498216, baseEnd_498216] using wordTrace_append hprefix tailTrace_498216
  have hstable : (prefixWord ++ tailWord_498216).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_498216).length < 2 ^ (prefixWord ++ tailWord_498216).sum := by decide
  have hdescent : baseEnd_498216 < baseStart_498216 := by decide
  rcases family_descends (prefixWord ++ tailWord_498216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_498222 : List Nat := [4, 1, 3, 1, 4, 1, 1, 3, 3]
def baseStart_498222 : Nat := 118140960795 + 498222 * 2 ^ 59
def prefixEnd_498222 : Nat := 4983230072969 + 3 ^ 40 * 498222 * 2
def baseEnd_498222 : Nat := 113701048286424416814989

theorem tailTrace_498222 : CollatzResearch.WordTrace tailWord_498222 prefixEnd_498222 113701048286424416814989 := by
  unfold tailWord_498222
  simp only [CollatzResearch.WordTrace]
  refine ⟨2271456150129282298548115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12114432800689505592256613 2271456150129282298548115)
  ·
    refine ⟨3407184225193923447822173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2271456150129282298548115 3407184225193923447822173)
    ·
      refine ⟨1277694084447721292933315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3407184225193923447822173 1277694084447721292933315)
      ·
        refine ⟨1916541126671581939399973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1277694084447721292933315 1916541126671581939399973)
        ·
          refine ⟨359351461250921613637495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1916541126671581939399973 359351461250921613637495)
          ·
            refine ⟨539027191876382420456243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 359351461250921613637495 539027191876382420456243)
            ·
              refine ⟨808540787814573630684365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 539027191876382420456243 808540787814573630684365)
              ·
                refine ⟨303202795430465111506637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 808540787814573630684365 303202795430465111506637)
                ·
                  refine ⟨113701048286424416814989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 303202795430465111506637 113701048286424416814989)
                  ·
                    rfl

theorem cell21_498222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 4, 1, 1, 3, 3].length) (baseStart_498222 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_498222 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_498222 prefixEnd_498222 := by exact prefixLift 498222
  have htrace : WordTrace (prefixWord ++ tailWord_498222) baseStart_498222 baseEnd_498222 := by
    simpa [prefixWord, tailWord_498222, baseEnd_498222] using wordTrace_append hprefix tailTrace_498222
  have hstable : (prefixWord ++ tailWord_498222).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_498222).length < 2 ^ (prefixWord ++ tailWord_498222).sum := by decide
  have hdescent : baseEnd_498222 < baseStart_498222 := by decide
  rcases family_descends (prefixWord ++ tailWord_498222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_498247 : List Nat := [1, 1, 4, 1, 4, 3, 1, 1, 5]
def baseStart_498247 : Nat := 118140960795 + 498247 * 2 ^ 59
def prefixEnd_498247 : Nat := 4983230072969 + 3 ^ 40 * 498247 * 2
def baseEnd_498247 : Nat := 113706753627029928898271

theorem tailTrace_498247 : CollatzResearch.WordTrace tailWord_498247 prefixEnd_498247 113706753627029928898271 := by
  unfold tailWord_498247
  simp only [CollatzResearch.WordTrace]
  refine ⟨18172561025943687658044995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12115040683962458438696663 18172561025943687658044995)
  ·
    refine ⟨27258841538915531487067493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18172561025943687658044995 27258841538915531487067493)
    ·
      refine ⟨5111032788546662153825155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27258841538915531487067493 5111032788546662153825155)
      ·
        refine ⟨7666549182819993230737733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5111032788546662153825155 7666549182819993230737733)
        ·
          refine ⟨1437477971778748730763325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7666549182819993230737733 1437477971778748730763325)
          ·
            refine ⟨539054239417030774036247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1437477971778748730763325 539054239417030774036247)
            ·
              refine ⟨808581359125546161054371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 539054239417030774036247 808581359125546161054371)
              ·
                refine ⟨1212872038688319241581557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 808581359125546161054371 1212872038688319241581557)
                ·
                  refine ⟨113706753627029928898271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1212872038688319241581557 113706753627029928898271)
                  ·
                    rfl

theorem cell21_498247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 3, 1, 1, 5].length) (baseStart_498247 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_498247 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_498247 prefixEnd_498247 := by exact prefixLift 498247
  have htrace : WordTrace (prefixWord ++ tailWord_498247) baseStart_498247 baseEnd_498247 := by
    simpa [prefixWord, tailWord_498247, baseEnd_498247] using wordTrace_append hprefix tailTrace_498247
  have hstable : (prefixWord ++ tailWord_498247).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_498247).length < 2 ^ (prefixWord ++ tailWord_498247).sum := by decide
  have hdescent : baseEnd_498247 < baseStart_498247 := by decide
  rcases family_descends (prefixWord ++ tailWord_498247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_498382 : List Nat := [4, 1, 1, 1, 3, 2, 2, 2, 5]
def baseStart_498382 : Nat := 118140960795 + 498382 * 2 ^ 59
def prefixEnd_498382 : Nat := 4983230072969 + 3 ^ 40 * 498382 * 2
def baseEnd_498382 : Nat := 113737562466299694147995

theorem tailTrace_498382 : CollatzResearch.WordTrace tailWord_498382 prefixEnd_498382 113737562466299694147995 := by
  unfold tailWord_498382
  simp only [CollatzResearch.WordTrace]
  refine ⟨2272185610056825714276175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12118323253636403809472933 2272185610056825714276175)
  ·
    refine ⟨3408278415085238571414263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2272185610056825714276175 3408278415085238571414263)
    ·
      refine ⟨5112417622627857857121395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3408278415085238571414263 5112417622627857857121395)
      ·
        refine ⟨7668626433941786785682093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5112417622627857857121395 7668626433941786785682093)
        ·
          refine ⟨2875734912728170044630785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7668626433941786785682093 2875734912728170044630785)
          ·
            refine ⟨2156801184546127533473089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2875734912728170044630785 2156801184546127533473089)
            ·
              refine ⟨1617600888409595650104817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2156801184546127533473089 1617600888409595650104817)
              ·
                refine ⟨1213200666307196737578613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1617600888409595650104817 1213200666307196737578613)
                ·
                  refine ⟨113737562466299694147995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1213200666307196737578613 113737562466299694147995)
                  ·
                    rfl

theorem cell21_498382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 2, 2, 5].length) (baseStart_498382 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_498382 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_498382 prefixEnd_498382 := by exact prefixLift 498382
  have htrace : WordTrace (prefixWord ++ tailWord_498382) baseStart_498382 baseEnd_498382 := by
    simpa [prefixWord, tailWord_498382, baseEnd_498382] using wordTrace_append hprefix tailTrace_498382
  have hstable : (prefixWord ++ tailWord_498382).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_498382).length < 2 ^ (prefixWord ++ tailWord_498382).sum := by decide
  have hdescent : baseEnd_498382 < baseStart_498382 := by decide
  rcases family_descends (prefixWord ++ tailWord_498382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_498399 : List Nat := [1, 1, 2, 3, 2, 3, 3, 3, 3]
def baseStart_498399 : Nat := 118140960795 + 498399 * 2 ^ 59
def prefixEnd_498399 : Nat := 4983230072969 + 3 ^ 40 * 498399 * 2
def baseEnd_498399 : Nat := 113741442097911442364627

theorem tailTrace_498399 : CollatzResearch.WordTrace tailWord_498399 prefixEnd_498399 113741442097911442364627 := by
  unfold tailWord_498399
  simp only [CollatzResearch.WordTrace]
  refine ⟨18178104921393017617578251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12118736614262011745052167 18178104921393017617578251)
  ·
    refine ⟨27267157382089526426367377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18178104921393017617578251 27267157382089526426367377)
    ·
      refine ⟨20450368036567144819775533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27267157382089526426367377 20450368036567144819775533)
      ·
        refine ⟨7668888013712679307415825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20450368036567144819775533 7668888013712679307415825)
        ·
          refine ⟨5751666010284509480561869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7668888013712679307415825 5751666010284509480561869)
          ·
            refine ⟨2156874753856691055210701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5751666010284509480561869 2156874753856691055210701)
            ·
              refine ⟨808828032696259145704013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2156874753856691055210701 808828032696259145704013)
              ·
                refine ⟨303310512261097179639005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 808828032696259145704013 303310512261097179639005)
                ·
                  refine ⟨113741442097911442364627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 303310512261097179639005 113741442097911442364627)
                  ·
                    rfl

theorem cell21_498399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 3, 3, 3].length) (baseStart_498399 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_498399 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_498399 prefixEnd_498399 := by exact prefixLift 498399
  have htrace : WordTrace (prefixWord ++ tailWord_498399) baseStart_498399 baseEnd_498399 := by
    simpa [prefixWord, tailWord_498399, baseEnd_498399] using wordTrace_append hprefix tailTrace_498399
  have hstable : (prefixWord ++ tailWord_498399).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_498399).length < 2 ^ (prefixWord ++ tailWord_498399).sum := by decide
  have hdescent : baseEnd_498399 < baseStart_498399 := by decide
  rcases family_descends (prefixWord ++ tailWord_498399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_498413 : List Nat := [1, 5, 1, 2, 1, 1, 2, 4, 4]
def baseStart_498413 : Nat := 118140960795 + 498413 * 2 ^ 59
def prefixEnd_498413 : Nat := 4983230072969 + 3 ^ 40 * 498413 * 2
def baseEnd_498413 : Nat := 113744637088650529131265

theorem tailTrace_498413 : CollatzResearch.WordTrace tailWord_498413 prefixEnd_498413 113744637088650529131265 := by
  unfold tailWord_498413
  simp only [CollatzResearch.WordTrace]
  refine ⟨18178615543342298008587893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12119077028894865339058595 18178615543342298008587893)
  ·
    refine ⟨1704245207188340438305115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 18178615543342298008587893 1704245207188340438305115)
    ·
      refine ⟨2556367810782510657457673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1704245207188340438305115 2556367810782510657457673)
      ·
        refine ⟨1917275858086882993093255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2556367810782510657457673 1917275858086882993093255)
        ·
          refine ⟨2875913787130324489639883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1917275858086882993093255 2875913787130324489639883)
          ·
            refine ⟨4313870680695486734459825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2875913787130324489639883 4313870680695486734459825)
            ·
              refine ⟨3235403010521615050844869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4313870680695486734459825 3235403010521615050844869)
              ·
                refine ⟨606638064472802822033413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3235403010521615050844869 606638064472802822033413)
                ·
                  refine ⟨113744637088650529131265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 606638064472802822033413 113744637088650529131265)
                  ·
                    rfl

theorem cell21_498413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 2, 4, 4].length) (baseStart_498413 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_498413 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_498413 prefixEnd_498413 := by exact prefixLift 498413
  have htrace : WordTrace (prefixWord ++ tailWord_498413) baseStart_498413 baseEnd_498413 := by
    simpa [prefixWord, tailWord_498413, baseEnd_498413] using wordTrace_append hprefix tailTrace_498413
  have hstable : (prefixWord ++ tailWord_498413).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_498413).length < 2 ^ (prefixWord ++ tailWord_498413).sum := by decide
  have hdescent : baseEnd_498413 < baseStart_498413 := by decide
  rcases family_descends (prefixWord ++ tailWord_498413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_498430 : List Nat := [4, 2, 2, 1, 2, 2, 1, 3, 4]
def baseStart_498430 : Nat := 118140960795 + 498430 * 2 ^ 59
def prefixEnd_498430 : Nat := 4983230072969 + 3 ^ 40 * 498430 * 2
def baseEnd_498430 : Nat := 113748516720262277347897

theorem tailTrace_498430 : CollatzResearch.WordTrace tailWord_498430 prefixEnd_498430 113748516720262277347897 := by
  unfold tailWord_498430
  simp only [CollatzResearch.WordTrace]
  refine ⟨2272404448035088738994593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12119490389520473274637829 2272404448035088738994593)
  ·
    refine ⟨1704303336026316554245945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2272404448035088738994593 1704303336026316554245945)
    ·
      refine ⟨1278227502019737415684459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1704303336026316554245945 1278227502019737415684459)
      ·
        refine ⟨1917341253029606123526689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1278227502019737415684459 1917341253029606123526689)
        ·
          refine ⟨1438005939772204592645017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1917341253029606123526689 1438005939772204592645017)
          ·
            refine ⟨1078504454829153444483763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1438005939772204592645017 1078504454829153444483763)
            ·
              refine ⟨1617756682243730166725645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1078504454829153444483763 1617756682243730166725645)
              ·
                refine ⟨606658755841398812522117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1617756682243730166725645 606658755841398812522117)
                ·
                  refine ⟨113748516720262277347897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 606658755841398812522117 113748516720262277347897)
                  ·
                    rfl

theorem cell21_498430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 1, 3, 4].length) (baseStart_498430 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_498430 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_498430 prefixEnd_498430 := by exact prefixLift 498430
  have htrace : WordTrace (prefixWord ++ tailWord_498430) baseStart_498430 baseEnd_498430 := by
    simpa [prefixWord, tailWord_498430, baseEnd_498430] using wordTrace_append hprefix tailTrace_498430
  have hstable : (prefixWord ++ tailWord_498430).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_498430).length < 2 ^ (prefixWord ++ tailWord_498430).sum := by decide
  have hdescent : baseEnd_498430 < baseStart_498430 := by decide
  rcases family_descends (prefixWord ++ tailWord_498430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_498441 : List Nat := [1, 2, 1, 1, 3, 2, 2, 4, 5]
def baseStart_498441 : Nat := 118140960795 + 498441 * 2 ^ 59
def prefixEnd_498441 : Nat := 4983230072969 + 3 ^ 40 * 498441 * 2
def baseEnd_498441 : Nat := 113751027070128702664541

theorem tailTrace_498441 : CollatzResearch.WordTrace tailWord_498441 prefixEnd_498441 113751027070128702664541 := by
  unfold tailWord_498441
  simp only [CollatzResearch.WordTrace]
  refine ⟨18179636787240858790607177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12119757858160572527071451 18179636787240858790607177)
  ·
    refine ⟨13634727590430644092955383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18179636787240858790607177 13634727590430644092955383)
    ·
      refine ⟨20452091385645966139433075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13634727590430644092955383 20452091385645966139433075)
      ·
        refine ⟨30678137078468949209149613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20452091385645966139433075 30678137078468949209149613)
        ·
          refine ⟨11504301404425855953431105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30678137078468949209149613 11504301404425855953431105)
          ·
            refine ⟨8628226053319391965073329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11504301404425855953431105 8628226053319391965073329)
            ·
              refine ⟨6471169539989543973804997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8628226053319391965073329 6471169539989543973804997)
              ·
                refine ⟨1213344288748039495088437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6471169539989543973804997 1213344288748039495088437)
                ·
                  refine ⟨113751027070128702664541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1213344288748039495088437 113751027070128702664541)
                  ·
                    rfl

theorem cell21_498441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 4, 5].length) (baseStart_498441 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_498441 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_498441 prefixEnd_498441 := by exact prefixLift 498441
  have htrace : WordTrace (prefixWord ++ tailWord_498441) baseStart_498441 baseEnd_498441 := by
    simpa [prefixWord, tailWord_498441, baseEnd_498441] using wordTrace_append hprefix tailTrace_498441
  have hstable : (prefixWord ++ tailWord_498441).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_498441).length < 2 ^ (prefixWord ++ tailWord_498441).sum := by decide
  have hdescent : baseEnd_498441 < baseStart_498441 := by decide
  rcases family_descends (prefixWord ++ tailWord_498441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_498509 : List Nat := [1, 6, 1, 2, 2, 1, 2, 3, 3]
def baseStart_498509 : Nat := 118140960795 + 498509 * 2 ^ 59
def prefixEnd_498509 : Nat := 4983230072969 + 3 ^ 40 * 498509 * 2
def baseEnd_498509 : Nat := 113766545596575695531069

theorem tailTrace_498509 : CollatzResearch.WordTrace tailWord_498509 prefixEnd_498509 113766545596575695531069 := by
  unfold tailWord_498509
  simp only [CollatzResearch.WordTrace]
  refine ⟨18182116950994506404082581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12121411300663004269388387 18182116950994506404082581)
  ·
    refine ⟨852286732077867487691371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 18182116950994506404082581 852286732077867487691371)
    ·
      refine ⟨1278430098116801231537057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 852286732077867487691371 1278430098116801231537057)
      ·
        refine ⟨958822573587600923652793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1278430098116801231537057 958822573587600923652793)
        ·
          refine ⟨719116930190700692739595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 958822573587600923652793 719116930190700692739595)
          ·
            refine ⟨1078675395286051039109393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 719116930190700692739595 1078675395286051039109393)
            ·
              refine ⟨809006546464538279332045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1078675395286051039109393 809006546464538279332045)
              ·
                refine ⟨303377454924201854749517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 809006546464538279332045 303377454924201854749517)
                ·
                  refine ⟨113766545596575695531069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 303377454924201854749517 113766545596575695531069)
                  ·
                    rfl

theorem cell21_498509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 2, 3, 3].length) (baseStart_498509 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_498509 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_498509 prefixEnd_498509 := by exact prefixLift 498509
  have htrace : WordTrace (prefixWord ++ tailWord_498509) baseStart_498509 baseEnd_498509 := by
    simpa [prefixWord, tailWord_498509, baseEnd_498509] using wordTrace_append hprefix tailTrace_498509
  have hstable : (prefixWord ++ tailWord_498509).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_498509).length < 2 ^ (prefixWord ++ tailWord_498509).sum := by decide
  have hdescent : baseEnd_498509 < baseStart_498509 := by decide
  rcases family_descends (prefixWord ++ tailWord_498509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_498517 : List Nat := [1, 3, 2, 2, 2, 1, 1, 2, 7]
def baseStart_498517 : Nat := 118140960795 + 498517 * 2 ^ 59
def prefixEnd_498517 : Nat := 4983230072969 + 3 ^ 40 * 498517 * 2
def baseEnd_498517 : Nat := 113768371305569459397719

theorem tailTrace_498517 : CollatzResearch.WordTrace tailWord_498517 prefixEnd_498517 113768371305569459397719 := by
  unfold tailWord_498517
  simp only [CollatzResearch.WordTrace]
  refine ⟨18182408734965523770373805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12121605823310349180249203 18182408734965523770373805)
  ·
    refine ⟨6818403275612071413890177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18182408734965523770373805 6818403275612071413890177)
    ·
      refine ⟨5113802456709053560417633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6818403275612071413890177 5113802456709053560417633)
      ·
        refine ⟨3835351842531790170313225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5113802456709053560417633 3835351842531790170313225)
        ·
          refine ⟨2876513881898842627734919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3835351842531790170313225 2876513881898842627734919)
          ·
            refine ⟨4314770822848263941602379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2876513881898842627734919 4314770822848263941602379)
            ·
              refine ⟨6472156234272395912403569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4314770822848263941602379 6472156234272395912403569)
              ·
                refine ⟨4854117175704296934302677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6472156234272395912403569 4854117175704296934302677)
                ·
                  refine ⟨113768371305569459397719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4854117175704296934302677 113768371305569459397719)
                  ·
                    rfl

theorem cell21_498517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 2, 7].length) (baseStart_498517 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_498517 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_498517 prefixEnd_498517 := by exact prefixLift 498517
  have htrace : WordTrace (prefixWord ++ tailWord_498517) baseStart_498517 baseEnd_498517 := by
    simpa [prefixWord, tailWord_498517, baseEnd_498517] using wordTrace_append hprefix tailTrace_498517
  have hstable : (prefixWord ++ tailWord_498517).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_498517).length < 2 ^ (prefixWord ++ tailWord_498517).sum := by decide
  have hdescent : baseEnd_498517 < baseStart_498517 := by decide
  rcases family_descends (prefixWord ++ tailWord_498517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_498568 : List Nat := [2, 1, 3, 3, 2, 3, 1, 3, 3]
def baseStart_498568 : Nat := 118140960795 + 498568 * 2 ^ 59
def prefixEnd_498568 : Nat := 4983230072969 + 3 ^ 40 * 498568 * 2
def baseEnd_498568 : Nat := 113780010200404704047615

theorem tailTrace_498568 : CollatzResearch.WordTrace tailWord_498568 prefixEnd_498568 113780010200404704047615 := by
  unfold tailWord_498568
  simp only [CollatzResearch.WordTrace]
  refine ⟨9092134428890379740240179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12122845905187172986986905 9092134428890379740240179)
  ·
    refine ⟨13638201643335569610360269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9092134428890379740240179 13638201643335569610360269)
    ·
      refine ⟨5114325616250838603885101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13638201643335569610360269 5114325616250838603885101)
      ·
        refine ⟨1917872106094064476456913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5114325616250838603885101 1917872106094064476456913)
        ·
          refine ⟨1438404079570548357342685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1917872106094064476456913 1438404079570548357342685)
          ·
            refine ⟨539401529838955634003507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1438404079570548357342685 539401529838955634003507)
            ·
              refine ⟨809102294758433451005261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 539401529838955634003507 809102294758433451005261)
              ·
                refine ⟨303413360534412544126973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 809102294758433451005261 303413360534412544126973)
                ·
                  refine ⟨113780010200404704047615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 303413360534412544126973 113780010200404704047615)
                  ·
                    rfl

theorem cell21_498568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 3, 1, 3, 3].length) (baseStart_498568 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_498568 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_498568 prefixEnd_498568 := by exact prefixLift 498568
  have htrace : WordTrace (prefixWord ++ tailWord_498568) baseStart_498568 baseEnd_498568 := by
    simpa [prefixWord, tailWord_498568, baseEnd_498568] using wordTrace_append hprefix tailTrace_498568
  have hstable : (prefixWord ++ tailWord_498568).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_498568).length < 2 ^ (prefixWord ++ tailWord_498568).sum := by decide
  have hdescent : baseEnd_498568 < baseStart_498568 := by decide
  rcases family_descends (prefixWord ++ tailWord_498568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_498599 : List Nat := [1, 1, 6, 1, 3, 2, 2, 1, 4]
def baseStart_498599 : Nat := 118140960795 + 498599 * 2 ^ 59
def prefixEnd_498599 : Nat := 4983230072969 + 3 ^ 40 * 498599 * 2
def baseEnd_498599 : Nat := 113787084822755539030885

theorem tailTrace_498599 : CollatzResearch.WordTrace tailWord_498599 prefixEnd_498599 113787084822755539030885 := by
  unfold tailWord_498599
  simp only [CollatzResearch.WordTrace]
  refine ⟨18185399520668451774858851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12123599680445634516572567 18185399520668451774858851)
  ·
    refine ⟨27278099281002677662288277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18185399520668451774858851 27278099281002677662288277)
    ·
      refine ⟨1278660903797000515419763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 27278099281002677662288277 1278660903797000515419763)
      ·
        refine ⟨1917991355695500773129645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1278660903797000515419763 1917991355695500773129645)
        ·
          refine ⟨719246758385812789923617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1917991355695500773129645 719246758385812789923617)
          ·
            refine ⟨539435068789359592442713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 719246758385812789923617 539435068789359592442713)
            ·
              refine ⟨404576301592019694332035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 539435068789359592442713 404576301592019694332035)
              ·
                refine ⟨606864452388029541498053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 404576301592019694332035 606864452388029541498053)
                ·
                  refine ⟨113787084822755539030885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 606864452388029541498053 113787084822755539030885)
                  ·
                    rfl

theorem cell21_498599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 2, 2, 1, 4].length) (baseStart_498599 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_498599 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_498599 prefixEnd_498599 := by exact prefixLift 498599
  have htrace : WordTrace (prefixWord ++ tailWord_498599) baseStart_498599 baseEnd_498599 := by
    simpa [prefixWord, tailWord_498599, baseEnd_498599] using wordTrace_append hprefix tailTrace_498599
  have hstable : (prefixWord ++ tailWord_498599).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_498599).length < 2 ^ (prefixWord ++ tailWord_498599).sum := by decide
  have hdescent : baseEnd_498599 < baseStart_498599 := by decide
  rcases family_descends (prefixWord ++ tailWord_498599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_498607 : List Nat := [1, 1, 2, 1, 2, 2, 2, 2, 8]
def baseStart_498607 : Nat := 118140960795 + 498607 * 2 ^ 59
def prefixEnd_498607 : Nat := 4983230072969 + 3 ^ 40 * 498607 * 2
def baseEnd_498607 : Nat := 113788910531749302897535

theorem tailTrace_498607 : CollatzResearch.WordTrace tailWord_498607 prefixEnd_498607 113788910531749302897535 := by
  unfold tailWord_498607
  simp only [CollatzResearch.WordTrace]
  refine ⟨18185691304639469141150075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12123794203092979427433383 18185691304639469141150075)
  ·
    refine ⟨27278536956959203711725113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18185691304639469141150075 27278536956959203711725113)
    ·
      refine ⟨20458902717719402783793835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27278536956959203711725113 20458902717719402783793835)
      ·
        refine ⟨30688354076579104175690753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20458902717719402783793835 30688354076579104175690753)
        ·
          refine ⟨23016265557434328131768065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30688354076579104175690753 23016265557434328131768065)
          ·
            refine ⟨17262199168075746098826049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23016265557434328131768065 17262199168075746098826049)
            ·
              refine ⟨12946649376056809574119537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17262199168075746098826049 12946649376056809574119537)
              ·
                refine ⟨9709987032042607180589653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12946649376056809574119537 9709987032042607180589653)
                ·
                  refine ⟨113788910531749302897535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 9709987032042607180589653 113788910531749302897535)
                  ·
                    rfl

theorem cell21_498607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 2, 8].length) (baseStart_498607 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_498607 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_498607 prefixEnd_498607 := by exact prefixLift 498607
  have htrace : WordTrace (prefixWord ++ tailWord_498607) baseStart_498607 baseEnd_498607 := by
    simpa [prefixWord, tailWord_498607, baseEnd_498607] using wordTrace_append hprefix tailTrace_498607
  have hstable : (prefixWord ++ tailWord_498607).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_498607).length < 2 ^ (prefixWord ++ tailWord_498607).sum := by decide
  have hdescent : baseEnd_498607 < baseStart_498607 := by decide
  rcases family_descends (prefixWord ++ tailWord_498607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_498630 : List Nat := [6, 1, 3, 1, 1, 9]
def baseStart_498630 : Nat := 118140960795 + 498630 * 2 ^ 59
def prefixEnd_498630 : Nat := 4983230072969 + 3 ^ 40 * 498630 * 2
def baseEnd_498630 : Nat := 4214598497966902741265

theorem tailTrace_498630 : CollatzResearch.WordTrace tailWord_498630 prefixEnd_498630 4214598497966902741265 := by
  unfold tailWord_498630
  simp only [CollatzResearch.WordTrace]
  refine ⟨568329068236129502163667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 12124353455704096046158229 568329068236129502163667)
  ·
    refine ⟨852493602354194253245501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 568329068236129502163667 852493602354194253245501)
    ·
      refine ⟨319685100882822844967063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 852493602354194253245501 319685100882822844967063)
      ·
        refine ⟨479527651324234267450595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 319685100882822844967063 479527651324234267450595)
        ·
          refine ⟨719291476986351401175893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 479527651324234267450595 719291476986351401175893)
          ·
            refine ⟨4214598497966902741265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 719291476986351401175893 4214598497966902741265)
            ·
              rfl

theorem cell21_498630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 9].length) (baseStart_498630 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_498630 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_498630 prefixEnd_498630 := by exact prefixLift 498630
  have htrace : WordTrace (prefixWord ++ tailWord_498630) baseStart_498630 baseEnd_498630 := by
    simpa [prefixWord, tailWord_498630, baseEnd_498630] using wordTrace_append hprefix tailTrace_498630
  have hstable : (prefixWord ++ tailWord_498630).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_498630).length < 2 ^ (prefixWord ++ tailWord_498630).sum := by decide
  have hdescent : baseEnd_498630 < baseStart_498630 := by decide
  rcases family_descends (prefixWord ++ tailWord_498630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_498638 : List Nat := [4, 1, 1, 1, 2, 12]
def baseStart_498638 : Nat := 118140960795 + 498638 * 2 ^ 59
def prefixEnd_498638 : Nat := 4983230072969 + 3 ^ 40 * 498638 * 2
def baseEnd_498638 : Nat := 4214666116818523625215

theorem tailTrace_498638 : CollatzResearch.WordTrace tailWord_498638 prefixEnd_498638 4214666116818523625215 := by
  unfold tailWord_498638
  simp only [CollatzResearch.WordTrace]
  refine ⟨2273352745940895179441071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12124547978351440957019045 2273352745940895179441071)
  ·
    refine ⟨3410029118911342769161607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2273352745940895179441071 3410029118911342769161607)
    ·
      refine ⟨5115043678367014153742411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3410029118911342769161607 5115043678367014153742411)
      ·
        refine ⟨7672565517550521230613617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5115043678367014153742411 7672565517550521230613617)
        ·
          refine ⟨5754424138162890922960213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7672565517550521230613617 5754424138162890922960213)
          ·
            refine ⟨4214666116818523625215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 5754424138162890922960213 4214666116818523625215)
            ·
              rfl

theorem cell21_498638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 12].length) (baseStart_498638 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_498638 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_498638 prefixEnd_498638 := by exact prefixLift 498638
  have htrace : WordTrace (prefixWord ++ tailWord_498638) baseStart_498638 baseEnd_498638 := by
    simpa [prefixWord, tailWord_498638, baseEnd_498638] using wordTrace_append hprefix tailTrace_498638
  have hstable : (prefixWord ++ tailWord_498638).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_498638).length < 2 ^ (prefixWord ++ tailWord_498638).sum := by decide
  have hdescent : baseEnd_498638 < baseStart_498638 := by decide
  rcases family_descends (prefixWord ++ tailWord_498638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_498644 : List Nat := [2, 4, 1, 2, 1, 2, 4, 2, 3]
def baseStart_498644 : Nat := 118140960795 + 498644 * 2 ^ 59
def prefixEnd_498644 : Nat := 4983230072969 + 3 ^ 40 * 498644 * 2
def baseEnd_498644 : Nat := 113797354435845460780793

theorem tailTrace_498644 : CollatzResearch.WordTrace tailWord_498644 prefixEnd_498644 113797354435845460780793 := by
  unfold tailWord_498644
  simp only [CollatzResearch.WordTrace]
  refine ⟨9093520402752712230123493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12124693870336949640164657 9093520402752712230123493)
  ·
    refine ⟨1705035075516133543148155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9093520402752712230123493 1705035075516133543148155)
    ·
      refine ⟨2557552613274200314722233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1705035075516133543148155 2557552613274200314722233)
      ·
        refine ⟨1918164459955650236041675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2557552613274200314722233 1918164459955650236041675)
        ·
          refine ⟨2877246689933475354062513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1918164459955650236041675 2877246689933475354062513)
          ·
            refine ⟨2157935017450106515546885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2877246689933475354062513 2157935017450106515546885)
            ·
              refine ⟨404612815771894971665041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2157935017450106515546885 404612815771894971665041)
              ·
                refine ⟨303459611828921228748781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 404612815771894971665041 303459611828921228748781)
                ·
                  refine ⟨113797354435845460780793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 303459611828921228748781 113797354435845460780793)
                  ·
                    rfl

theorem cell21_498644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 4, 2, 3].length) (baseStart_498644 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_498644 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_498644 prefixEnd_498644 := by exact prefixLift 498644
  have htrace : WordTrace (prefixWord ++ tailWord_498644) baseStart_498644 baseEnd_498644 := by
    simpa [prefixWord, tailWord_498644, baseEnd_498644] using wordTrace_append hprefix tailTrace_498644
  have hstable : (prefixWord ++ tailWord_498644).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_498644).length < 2 ^ (prefixWord ++ tailWord_498644).sum := by decide
  have hdescent : baseEnd_498644 < baseStart_498644 := by decide
  rcases family_descends (prefixWord ++ tailWord_498644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_498658 : List Nat := [3, 3, 3, 1, 1, 1, 2, 3, 4]
def baseStart_498658 : Nat := 118140960795 + 498658 * 2 ^ 59
def prefixEnd_498658 : Nat := 4983230072969 + 3 ^ 40 * 498658 * 2
def baseEnd_498658 : Nat := 113800549426584547547431

theorem tailTrace_498658 : CollatzResearch.WordTrace tailWord_498658 prefixEnd_498658 113800549426584547547431 := by
  unfold tailWord_498658
  simp only [CollatzResearch.WordTrace]
  refine ⟨4546887856863676212814157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12125034284969803234171085 4546887856863676212814157)
  ·
    refine ⟨1705082946323878579805309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4546887856863676212814157 1705082946323878579805309)
    ·
      refine ⟨639406104871454467426991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1705082946323878579805309 639406104871454467426991)
      ·
        refine ⟨959109157307181701140487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 639406104871454467426991 959109157307181701140487)
        ·
          refine ⟨1438663735960772551710731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 959109157307181701140487 1438663735960772551710731)
          ·
            refine ⟨2157995603941158827566097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1438663735960772551710731 2157995603941158827566097)
            ·
              refine ⟨1618496702955869120674573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2157995603941158827566097 1618496702955869120674573)
              ·
                refine ⟨606936263608450920252965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1618496702955869120674573 606936263608450920252965)
                ·
                  refine ⟨113800549426584547547431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 606936263608450920252965 113800549426584547547431)
                  ·
                    rfl

theorem cell21_498658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 2, 3, 4].length) (baseStart_498658 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_498658 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_498658 prefixEnd_498658 := by exact prefixLift 498658
  have htrace : WordTrace (prefixWord ++ tailWord_498658) baseStart_498658 baseEnd_498658 := by
    simpa [prefixWord, tailWord_498658, baseEnd_498658] using wordTrace_append hprefix tailTrace_498658
  have hstable : (prefixWord ++ tailWord_498658).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_498658).length < 2 ^ (prefixWord ++ tailWord_498658).sum := by decide
  have hdescent : baseEnd_498658 < baseStart_498658 := by decide
  rcases family_descends (prefixWord ++ tailWord_498658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_498683 : List Nat := [1, 1, 1, 1, 1, 3, 3, 4, 6]
def baseStart_498683 : Nat := 118140960795 + 498683 * 2 ^ 59
def prefixEnd_498683 : Nat := 4983230072969 + 3 ^ 40 * 498683 * 2
def baseEnd_498683 : Nat := 113806254767190059630713

theorem tailTrace_498683 : CollatzResearch.WordTrace tailWord_498683 prefixEnd_498683 113806254767190059630713 := by
  unfold tailWord_498683
  simp only [CollatzResearch.WordTrace]
  refine ⟨18188463252364134120916703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12125642168242756080611135 18188463252364134120916703)
  ·
    refine ⟨27282694878546201181375055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18188463252364134120916703 27282694878546201181375055)
    ·
      refine ⟨40924042317819301772062583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27282694878546201181375055 40924042317819301772062583)
      ·
        refine ⟨61386063476728952658093875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40924042317819301772062583 61386063476728952658093875)
        ·
          refine ⟨92079095215093428987140813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61386063476728952658093875 92079095215093428987140813)
          ·
            refine ⟨34529660705660035870177805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92079095215093428987140813 34529660705660035870177805)
            ·
              refine ⟨12948622764622513451316677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34529660705660035870177805 12948622764622513451316677)
              ·
                refine ⟨2427866768366721272121877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12948622764622513451316677 2427866768366721272121877)
                ·
                  refine ⟨113806254767190059630713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2427866768366721272121877 113806254767190059630713)
                  ·
                    rfl

theorem cell21_498683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 4, 6].length) (baseStart_498683 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_498683 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_498683 prefixEnd_498683 := by exact prefixLift 498683
  have htrace : WordTrace (prefixWord ++ tailWord_498683) baseStart_498683 baseEnd_498683 := by
    simpa [prefixWord, tailWord_498683, baseEnd_498683] using wordTrace_append hprefix tailTrace_498683
  have hstable : (prefixWord ++ tailWord_498683).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_498683).length < 2 ^ (prefixWord ++ tailWord_498683).sum := by decide
  have hdescent : baseEnd_498683 < baseStart_498683 := by decide
  rcases family_descends (prefixWord ++ tailWord_498683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_498700 : List Nat := [2, 2, 1, 2, 3, 3, 1, 1, 6]
def baseStart_498700 : Nat := 118140960795 + 498700 * 2 ^ 59
def prefixEnd_498700 : Nat := 4983230072969 + 3 ^ 40 * 498700 * 2
def baseEnd_498700 : Nat := 113810134398801807847345

theorem tailTrace_498700 : CollatzResearch.WordTrace tailWord_498700 prefixEnd_498700 113810134398801807847345 := by
  unfold tailWord_498700
  simp only [CollatzResearch.WordTrace]
  refine ⟨9094541646651273012142777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12126055528868364016190369 9094541646651273012142777)
  ·
    refine ⟨6820906234988454759107083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9094541646651273012142777 6820906234988454759107083)
    ·
      refine ⟨10231359352482682138660625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6820906234988454759107083 10231359352482682138660625)
      ·
        refine ⟨7673519514362011603995469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10231359352482682138660625 7673519514362011603995469)
        ·
          refine ⟨2877569817885754351498301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7673519514362011603995469 2877569817885754351498301)
          ·
            refine ⟨1079088681707157881811863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2877569817885754351498301 1079088681707157881811863)
            ·
              refine ⟨1618633022560736822717795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1079088681707157881811863 1618633022560736822717795)
              ·
                refine ⟨2427949533841105234076693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1618633022560736822717795 2427949533841105234076693)
                ·
                  refine ⟨113810134398801807847345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2427949533841105234076693 113810134398801807847345)
                  ·
                    rfl

theorem cell21_498700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 1, 1, 6].length) (baseStart_498700 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_498700 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_498700 prefixEnd_498700 := by exact prefixLift 498700
  have htrace : WordTrace (prefixWord ++ tailWord_498700) baseStart_498700 baseEnd_498700 := by
    simpa [prefixWord, tailWord_498700, baseEnd_498700] using wordTrace_append hprefix tailTrace_498700
  have hstable : (prefixWord ++ tailWord_498700).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_498700).length < 2 ^ (prefixWord ++ tailWord_498700).sum := by decide
  have hdescent : baseEnd_498700 < baseStart_498700 := by decide
  rcases family_descends (prefixWord ++ tailWord_498700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_498714 : List Nat := [3, 1, 1, 3, 1, 2, 2, 8]
def baseStart_498714 : Nat := 118140960795 + 498714 * 2 ^ 59
def prefixEnd_498714 : Nat := 4983230072969 + 3 ^ 40 * 498714 * 2
def baseEnd_498714 : Nat := 37937776463180298204661

theorem tailTrace_498714 : CollatzResearch.WordTrace tailWord_498714 prefixEnd_498714 37937776463180298204661 := by
  unfold tailWord_498714
  simp only [CollatzResearch.WordTrace]
  refine ⟨4547398478812956603823799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12126395943501217610196797 4547398478812956603823799)
  ·
    refine ⟨6821097718219434905735699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4547398478812956603823799 6821097718219434905735699)
    ·
      refine ⟨10231646577329152358603549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6821097718219434905735699 10231646577329152358603549)
      ·
        refine ⟨3836867466498432134476331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10231646577329152358603549 3836867466498432134476331)
        ·
          refine ⟨5755301199747648201714497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3836867466498432134476331 5755301199747648201714497)
          ·
            refine ⟨4316475899810736151285873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5755301199747648201714497 4316475899810736151285873)
            ·
              refine ⟨3237356924858052113464405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4316475899810736151285873 3237356924858052113464405)
              ·
                refine ⟨37937776463180298204661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3237356924858052113464405 37937776463180298204661)
                ·
                  rfl

theorem cell21_498714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 2, 8].length) (baseStart_498714 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_498714 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_498714 prefixEnd_498714 := by exact prefixLift 498714
  have htrace : WordTrace (prefixWord ++ tailWord_498714) baseStart_498714 baseEnd_498714 := by
    simpa [prefixWord, tailWord_498714, baseEnd_498714] using wordTrace_append hprefix tailTrace_498714
  have hstable : (prefixWord ++ tailWord_498714).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_498714).length < 2 ^ (prefixWord ++ tailWord_498714).sum := by decide
  have hdescent : baseEnd_498714 < baseStart_498714 := by decide
  rcases family_descends (prefixWord ++ tailWord_498714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_498762 : List Nat := [3, 1, 2, 1, 1, 2, 2, 6, 3]
def baseStart_498762 : Nat := 118140960795 + 498762 * 2 ^ 59
def prefixEnd_498762 : Nat := 4983230072969 + 3 ^ 40 * 498762 * 2
def baseEnd_498762 : Nat := 113824283643503477813885

theorem tailTrace_498762 : CollatzResearch.WordTrace tailWord_498762 prefixEnd_498762 113824283643503477813885 := by
  unfold tailWord_498762
  simp only [CollatzResearch.WordTrace]
  refine ⟨4547836154769482653260635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12127563079385287075361693 4547836154769482653260635)
  ·
    refine ⟨6821754232154223979890953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4547836154769482653260635 6821754232154223979890953)
    ·
      refine ⟨5116315674115667984918215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6821754232154223979890953 5116315674115667984918215)
      ·
        refine ⟨7674473511173501977377323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5116315674115667984918215 7674473511173501977377323)
        ·
          refine ⟨11511710266760252966065985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7674473511173501977377323 11511710266760252966065985)
          ·
            refine ⟨8633782700070189724549489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11511710266760252966065985 8633782700070189724549489)
            ·
              refine ⟨6475337025052642293412117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8633782700070189724549489 6475337025052642293412117)
              ·
                refine ⟨303531423049342607503693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 6475337025052642293412117 303531423049342607503693)
                ·
                  refine ⟨113824283643503477813885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 303531423049342607503693 113824283643503477813885)
                  ·
                    rfl

theorem cell21_498762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 6, 3].length) (baseStart_498762 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_498762 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_498762 prefixEnd_498762 := by exact prefixLift 498762
  have htrace : WordTrace (prefixWord ++ tailWord_498762) baseStart_498762 baseEnd_498762 := by
    simpa [prefixWord, tailWord_498762, baseEnd_498762] using wordTrace_append hprefix tailTrace_498762
  have hstable : (prefixWord ++ tailWord_498762).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_498762).length < 2 ^ (prefixWord ++ tailWord_498762).sum := by decide
  have hdescent : baseEnd_498762 < baseStart_498762 := by decide
  rcases family_descends (prefixWord ++ tailWord_498762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_498776 : List Nat := [2, 1, 2, 2, 1, 3, 3, 3, 4]
def baseStart_498776 : Nat := 118140960795 + 498776 * 2 ^ 59
def prefixEnd_498776 : Nat := 4983230072969 + 3 ^ 40 * 498776 * 2
def baseEnd_498776 : Nat := 113827478634242564580523

theorem tailTrace_498776 : CollatzResearch.WordTrace tailWord_498776 prefixEnd_498776 113827478634242564580523 := by
  unfold tailWord_498776
  simp only [CollatzResearch.WordTrace]
  refine ⟨9095927620513605502026091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12127903494018140669368121 9095927620513605502026091)
  ·
    refine ⟨13643891430770408253039137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9095927620513605502026091 13643891430770408253039137)
    ·
      refine ⟨10232918573077806189779353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13643891430770408253039137 10232918573077806189779353)
      ·
        refine ⟨7674688929808354642334515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10232918573077806189779353 7674688929808354642334515)
        ·
          refine ⟨11512033394712531963501773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7674688929808354642334515 11512033394712531963501773)
          ·
            refine ⟨4317012523017199486313165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11512033394712531963501773 4317012523017199486313165)
            ·
              refine ⟨1618879696131449807367437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4317012523017199486313165 1618879696131449807367437)
              ·
                refine ⟨607079886049293677762789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1618879696131449807367437 607079886049293677762789)
                ·
                  refine ⟨113827478634242564580523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 607079886049293677762789 113827478634242564580523)
                  ·
                    rfl

theorem cell21_498776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 3, 3, 4].length) (baseStart_498776 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_498776 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_498776 prefixEnd_498776 := by exact prefixLift 498776
  have htrace : WordTrace (prefixWord ++ tailWord_498776) baseStart_498776 baseEnd_498776 := by
    simpa [prefixWord, tailWord_498776, baseEnd_498776] using wordTrace_append hprefix tailTrace_498776
  have hstable : (prefixWord ++ tailWord_498776).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_498776).length < 2 ^ (prefixWord ++ tailWord_498776).sum := by decide
  have hdescent : baseEnd_498776 < baseStart_498776 := by decide
  rcases family_descends (prefixWord ++ tailWord_498776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_498824 : List Nat := [2, 1, 3, 4, 2, 2, 1, 6]
def baseStart_498824 : Nat := 118140960795 + 498824 * 2 ^ 59
def prefixEnd_498824 : Nat := 4983230072969 + 3 ^ 40 * 498824 * 2
def baseEnd_498824 : Nat := 37946144296068382593475

theorem tailTrace_498824 : CollatzResearch.WordTrace tailWord_498824 prefixEnd_498824 37946144296068382593475 := by
  unfold tailWord_498824
  simp only [CollatzResearch.WordTrace]
  refine ⟨9096802972426657600899763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12129070629902210134533017 9096802972426657600899763)
  ·
    refine ⟨13645204458639986401349645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9096802972426657600899763 13645204458639986401349645)
    ·
      refine ⟨5116951671989994900506117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13645204458639986401349645 5116951671989994900506117)
      ·
        refine ⟨959428438498124043844897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5116951671989994900506117 959428438498124043844897)
        ·
          refine ⟨719571328873593032883673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 959428438498124043844897 719571328873593032883673)
          ·
            refine ⟨539678496655194774662755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 719571328873593032883673 539678496655194774662755)
            ·
              refine ⟨809517744982792161994133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 539678496655194774662755 809517744982792161994133)
              ·
                refine ⟨37946144296068382593475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 809517744982792161994133 37946144296068382593475)
                ·
                  rfl

theorem cell21_498824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 2, 1, 6].length) (baseStart_498824 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_498824 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_498824 prefixEnd_498824 := by exact prefixLift 498824
  have htrace : WordTrace (prefixWord ++ tailWord_498824) baseStart_498824 baseEnd_498824 := by
    simpa [prefixWord, tailWord_498824, baseEnd_498824] using wordTrace_append hprefix tailTrace_498824
  have hstable : (prefixWord ++ tailWord_498824).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_498824).length < 2 ^ (prefixWord ++ tailWord_498824).sum := by decide
  have hdescent : baseEnd_498824 < baseStart_498824 := by decide
  rcases family_descends (prefixWord ++ tailWord_498824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_498855 : List Nat := [1, 1, 6, 2, 1, 1, 1, 5, 3]
def baseStart_498855 : Nat := 118140960795 + 498855 * 2 ^ 59
def prefixEnd_498855 : Nat := 4983230072969 + 3 ^ 40 * 498855 * 2
def baseEnd_498855 : Nat := 113845507510555982763695

theorem tailTrace_498855 : CollatzResearch.WordTrace tailWord_498855 prefixEnd_498855 113845507510555982763695 := by
  unfold tailWord_498855
  simp only [CollatzResearch.WordTrace]
  refine ⟨18194736607741007496178019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12129824405160671664118679 18194736607741007496178019)
  ·
    refine ⟨27292104911611511244267029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18194736607741007496178019 27292104911611511244267029)
    ·
      refine ⟨1279317417731789589575017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 27292104911611511244267029 1279317417731789589575017)
      ·
        refine ⟨959488063298842192181263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1279317417731789589575017 959488063298842192181263)
        ·
          refine ⟨1439232094948263288271895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 959488063298842192181263 1439232094948263288271895)
          ·
            refine ⟨2158848142422394932407843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1439232094948263288271895 2158848142422394932407843)
            ·
              refine ⟨3238272213633592398611765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2158848142422394932407843 3238272213633592398611765)
              ·
                refine ⟨303588020028149287369853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3238272213633592398611765 303588020028149287369853)
                ·
                  refine ⟨113845507510555982763695, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 303588020028149287369853 113845507510555982763695)
                  ·
                    rfl

theorem cell21_498855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 1, 5, 3].length) (baseStart_498855 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_498855 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_498855 prefixEnd_498855 := by exact prefixLift 498855
  have htrace : WordTrace (prefixWord ++ tailWord_498855) baseStart_498855 baseEnd_498855 := by
    simpa [prefixWord, tailWord_498855, baseEnd_498855] using wordTrace_append hprefix tailTrace_498855
  have hstable : (prefixWord ++ tailWord_498855).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_498855).length < 2 ^ (prefixWord ++ tailWord_498855).sum := by decide
  have hdescent : baseEnd_498855 < baseStart_498855 := by decide
  rcases family_descends (prefixWord ++ tailWord_498855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_498866 : List Nat := [3, 2, 1, 1, 1, 5, 8]
def baseStart_498866 : Nat := 118140960795 + 498866 * 2 ^ 59
def prefixEnd_498866 : Nat := 4983230072969 + 3 ^ 40 * 498866 * 2
def baseEnd_498866 : Nat := 12649779762269156453371

theorem tailTrace_498866 : CollatzResearch.WordTrace tailWord_498866 prefixEnd_498866 12649779762269156453371 := by
  unfold tailWord_498866
  simp only [CollatzResearch.WordTrace]
  refine ⟨4548784452675289093707113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12130091873800770916552301 4548784452675289093707113)
  ·
    refine ⟨3411588339506466820280335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4548784452675289093707113 3411588339506466820280335)
    ·
      refine ⟨5117382509259700230420503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3411588339506466820280335 5117382509259700230420503)
      ·
        refine ⟨7676073763889550345630755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5117382509259700230420503 7676073763889550345630755)
        ·
          refine ⟨11514110645834325518446133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7676073763889550345630755 11514110645834325518446133)
          ·
            refine ⟨1079447873046968017354325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11514110645834325518446133 1079447873046968017354325)
            ·
              refine ⟨12649779762269156453371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1079447873046968017354325 12649779762269156453371)
              ·
                rfl

theorem cell21_498866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 8].length) (baseStart_498866 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_498866 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_498866 prefixEnd_498866 := by exact prefixLift 498866
  have htrace : WordTrace (prefixWord ++ tailWord_498866) baseStart_498866 baseEnd_498866 := by
    simpa [prefixWord, tailWord_498866, baseEnd_498866] using wordTrace_append hprefix tailTrace_498866
  have hstable : (prefixWord ++ tailWord_498866).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_498866).length < 2 ^ (prefixWord ++ tailWord_498866).sum := by decide
  have hdescent : baseEnd_498866 < baseStart_498866 := by decide
  rcases family_descends (prefixWord ++ tailWord_498866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_498900 : List Nat := [2, 4, 1, 4, 1, 1, 1, 7]
def baseStart_498900 : Nat := 118140960795 + 498900 * 2 ^ 59
def prefixEnd_498900 : Nat := 4983230072969 + 3 ^ 40 * 498900 * 2
def baseEnd_498900 : Nat := 37951925707881968171201

theorem tailTrace_498900 : CollatzResearch.WordTrace tailWord_498900 prefixEnd_498900 37951925707881968171201 := by
  unfold tailWord_498900
  simp only [CollatzResearch.WordTrace]
  refine ⟨9098188946288990090783077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12130918595051986787710769 9098188946288990090783077)
  ·
    refine ⟨1705910427429185642021827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9098188946288990090783077 1705910427429185642021827)
    ·
      refine ⟨2558865641143778463032741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1705910427429185642021827 2558865641143778463032741)
      ·
        refine ⟨479787307714458461818639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2558865641143778463032741 479787307714458461818639)
        ·
          refine ⟨719680961571687692727959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 479787307714458461818639 719680961571687692727959)
          ·
            refine ⟨1079521442357531539091939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 719680961571687692727959 1079521442357531539091939)
            ·
              refine ⟨1619282163536297308637909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1079521442357531539091939 1619282163536297308637909)
              ·
                refine ⟨37951925707881968171201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1619282163536297308637909 37951925707881968171201)
                ·
                  rfl

theorem cell21_498900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 1, 7].length) (baseStart_498900 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_498900 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_498900 prefixEnd_498900 := by exact prefixLift 498900
  have htrace : WordTrace (prefixWord ++ tailWord_498900) baseStart_498900 baseEnd_498900 := by
    simpa [prefixWord, tailWord_498900, baseEnd_498900] using wordTrace_append hprefix tailTrace_498900
  have hstable : (prefixWord ++ tailWord_498900).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_498900).length < 2 ^ (prefixWord ++ tailWord_498900).sum := by decide
  have hdescent : baseEnd_498900 < baseStart_498900 := by decide
  rcases family_descends (prefixWord ++ tailWord_498900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_498911 : List Nat := [1, 1, 2, 3, 2, 1, 3, 2, 6]
def baseStart_498911 : Nat := 118140960795 + 498911 * 2 ^ 59
def prefixEnd_498911 : Nat := 4983230072969 + 3 ^ 40 * 498911 * 2
def baseEnd_498911 : Nat := 113858287473512329830247

theorem tailTrace_498911 : CollatzResearch.WordTrace tailWord_498911 prefixEnd_498911 113858287473512329830247 := by
  unfold tailWord_498911
  simp only [CollatzResearch.WordTrace]
  refine ⟨18196779095538129060216587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12131186063692086040144391 18196779095538129060216587)
  ·
    refine ⟨27295168643307193590324881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18196779095538129060216587 27295168643307193590324881)
    ·
      refine ⟨20471376482480395192743661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27295168643307193590324881 20471376482480395192743661)
      ·
        refine ⟨7676766180930148197278873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20471376482480395192743661 7676766180930148197278873)
        ·
          refine ⟨5757574635697611147959155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7676766180930148197278873 5757574635697611147959155)
          ·
            refine ⟨8636361953546416721938733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5757574635697611147959155 8636361953546416721938733)
            ·
              refine ⟨3238635732579906270727025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8636361953546416721938733 3238635732579906270727025)
              ·
                refine ⟨2428976799434929703045269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3238635732579906270727025 2428976799434929703045269)
                ·
                  refine ⟨113858287473512329830247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2428976799434929703045269 113858287473512329830247)
                  ·
                    rfl

theorem cell21_498911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 3, 2, 6].length) (baseStart_498911 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_498911 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_498911 prefixEnd_498911 := by exact prefixLift 498911
  have htrace : WordTrace (prefixWord ++ tailWord_498911) baseStart_498911 baseEnd_498911 := by
    simpa [prefixWord, tailWord_498911, baseEnd_498911] using wordTrace_append hprefix tailTrace_498911
  have hstable : (prefixWord ++ tailWord_498911).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_498911).length < 2 ^ (prefixWord ++ tailWord_498911).sum := by decide
  have hdescent : baseEnd_498911 < baseStart_498911 := by decide
  rcases family_descends (prefixWord ++ tailWord_498911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_498931 : List Nat := [1, 1, 1, 2, 2, 6, 3, 2, 3]
def baseStart_498931 : Nat := 118140960795 + 498931 * 2 ^ 59
def prefixEnd_498931 : Nat := 4983230072969 + 3 ^ 40 * 498931 * 2
def baseEnd_498931 : Nat := 113862851745996739496873

theorem tailTrace_498931 : CollatzResearch.WordTrace tailWord_498931 prefixEnd_498931 113862851745996739496873 := by
  unfold tailWord_498931
  simp only [CollatzResearch.WordTrace]
  refine ⟨18197508555465672475944647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12131672370310448317296431 18197508555465672475944647)
  ·
    refine ⟨27296262833198508713916971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18197508555465672475944647 27296262833198508713916971)
    ·
      refine ⟨40944394249797763070875457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27296262833198508713916971 40944394249797763070875457)
      ·
        refine ⟨30708295687348322303156593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40944394249797763070875457 30708295687348322303156593)
        ·
          refine ⟨23031221765511241727367445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30708295687348322303156593 23031221765511241727367445)
          ·
            refine ⟨1079588520258339455970349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 23031221765511241727367445 1079588520258339455970349)
            ·
              refine ⟨404845695096877295988881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1079588520258339455970349 404845695096877295988881)
              ·
                refine ⟨303634271322657971991661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 404845695096877295988881 303634271322657971991661)
                ·
                  refine ⟨113862851745996739496873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 303634271322657971991661 113862851745996739496873)
                  ·
                    rfl

theorem cell21_498931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 3, 2, 3].length) (baseStart_498931 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_498931 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_498931 prefixEnd_498931 := by exact prefixLift 498931
  have htrace : WordTrace (prefixWord ++ tailWord_498931) baseStart_498931 baseEnd_498931 := by
    simpa [prefixWord, tailWord_498931, baseEnd_498931] using wordTrace_append hprefix tailTrace_498931
  have hstable : (prefixWord ++ tailWord_498931).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_498931).length < 2 ^ (prefixWord ++ tailWord_498931).sum := by decide
  have hdescent : baseEnd_498931 < baseStart_498931 := by decide
  rcases family_descends (prefixWord ++ tailWord_498931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_498945 : List Nat := [1, 2, 4, 1, 1, 3, 4, 1, 4]
def baseStart_498945 : Nat := 118140960795 + 498945 * 2 ^ 59
def prefixEnd_498945 : Nat := 4983230072969 + 3 ^ 40 * 498945 * 2
def baseEnd_498945 : Nat := 113866046736735826263511

theorem tailTrace_498945 : CollatzResearch.WordTrace tailWord_498945 prefixEnd_498945 113866046736735826263511 := by
  unfold tailWord_498945
  simp only [CollatzResearch.WordTrace]
  refine ⟨18198019177414952866954289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12132012784943301911302859 18198019177414952866954289)
  ·
    refine ⟨13648514383061214650215717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18198019177414952866954289 13648514383061214650215717)
    ·
      refine ⟨2559096446823977746915447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13648514383061214650215717 2559096446823977746915447)
      ·
        refine ⟨3838644670235966620373171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2559096446823977746915447 3838644670235966620373171)
        ·
          refine ⟨5757967005353949930559757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3838644670235966620373171 5757967005353949930559757)
          ·
            refine ⟨2159237627007731223959909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5757967005353949930559757 2159237627007731223959909)
            ·
              refine ⟨404857055063949604492483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2159237627007731223959909 404857055063949604492483)
              ·
                refine ⟨607285582595924406738725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 404857055063949604492483 607285582595924406738725)
                ·
                  refine ⟨113866046736735826263511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 607285582595924406738725 113866046736735826263511)
                  ·
                    rfl

theorem cell21_498945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 4, 1, 4].length) (baseStart_498945 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_498945 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_498945 prefixEnd_498945 := by exact prefixLift 498945
  have htrace : WordTrace (prefixWord ++ tailWord_498945) baseStart_498945 baseEnd_498945 := by
    simpa [prefixWord, tailWord_498945, baseEnd_498945] using wordTrace_append hprefix tailTrace_498945
  have hstable : (prefixWord ++ tailWord_498945).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_498945).length < 2 ^ (prefixWord ++ tailWord_498945).sum := by decide
  have hdescent : baseEnd_498945 < baseStart_498945 := by decide
  rcases family_descends (prefixWord ++ tailWord_498945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_499004 : List Nat := [2, 2, 2, 2, 1, 3, 2, 3, 4]
def baseStart_499004 : Nat := 118140960795 + 499004 * 2 ^ 59
def prefixEnd_499004 : Nat := 4983230072969 + 3 ^ 40 * 499004 * 2
def baseEnd_499004 : Nat := 113879511340564834780057

theorem tailTrace_499004 : CollatzResearch.WordTrace tailWord_499004 prefixEnd_499004 113879511340564834780057 := by
  unfold tailWord_499004
  simp only [CollatzResearch.WordTrace]
  refine ⟨9100085542100602971676033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12133447389467470628901377 9100085542100602971676033)
  ·
    refine ⟨6825064156575452228757025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9100085542100602971676033 6825064156575452228757025)
    ·
      refine ⟨5118798117431589171567769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6825064156575452228757025 5118798117431589171567769)
      ·
        refine ⟨3839098588073691878675827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5118798117431589171567769 3839098588073691878675827)
        ·
          refine ⟨5758647882110537818013741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3839098588073691878675827 5758647882110537818013741)
          ·
            refine ⟨2159492955791451681755153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5758647882110537818013741 2159492955791451681755153)
            ·
              refine ⟨1619619716843588761316365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2159492955791451681755153 1619619716843588761316365)
              ·
                refine ⟨607357393816345785493637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1619619716843588761316365 607357393816345785493637)
                ·
                  refine ⟨113879511340564834780057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 607357393816345785493637 113879511340564834780057)
                  ·
                    rfl

theorem cell21_499004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 2, 3, 4].length) (baseStart_499004 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_499004 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_499004 prefixEnd_499004 := by exact prefixLift 499004
  have htrace : WordTrace (prefixWord ++ tailWord_499004) baseStart_499004 baseEnd_499004 := by
    simpa [prefixWord, tailWord_499004, baseEnd_499004] using wordTrace_append hprefix tailTrace_499004
  have hstable : (prefixWord ++ tailWord_499004).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_499004).length < 2 ^ (prefixWord ++ tailWord_499004).sum := by decide
  have hdescent : baseEnd_499004 < baseStart_499004 := by decide
  rcases family_descends (prefixWord ++ tailWord_499004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_499032 : List Nat := [2, 1, 2, 2, 1, 1, 3, 2, 7]
def baseStart_499032 : Nat := 118140960795 + 499032 * 2 ^ 59
def prefixEnd_499032 : Nat := 4983230072969 + 3 ^ 40 * 499032 * 2
def baseEnd_499032 : Nat := 113885901322043008313333

theorem tailTrace_499032 : CollatzResearch.WordTrace tailWord_499032 prefixEnd_499032 113885901322043008313333 := by
  unfold tailWord_499032
  simp only [CollatzResearch.WordTrace]
  refine ⟨9100596164049883362685675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12134128218733177816914233 9100596164049883362685675)
  ·
    refine ⟨13650894246074825044028513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9100596164049883362685675 13650894246074825044028513)
    ·
      refine ⟨10238170684556118783021385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13650894246074825044028513 10238170684556118783021385)
      ·
        refine ⟨7678628013417089087266039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10238170684556118783021385 7678628013417089087266039)
        ·
          refine ⟨11517942020125633630899059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7678628013417089087266039 11517942020125633630899059)
          ·
            refine ⟨17276913030188450446348589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11517942020125633630899059 17276913030188450446348589)
            ·
              refine ⟨6478842386320668917380721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17276913030188450446348589 6478842386320668917380721)
              ·
                refine ⟨4859131789740501688035541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6478842386320668917380721 4859131789740501688035541)
                ·
                  refine ⟨113885901322043008313333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4859131789740501688035541 113885901322043008313333)
                  ·
                    rfl

theorem cell21_499032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 2, 7].length) (baseStart_499032 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_499032 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_499032 prefixEnd_499032 := by exact prefixLift 499032
  have htrace : WordTrace (prefixWord ++ tailWord_499032) baseStart_499032 baseEnd_499032 := by
    simpa [prefixWord, tailWord_499032, baseEnd_499032] using wordTrace_append hprefix tailTrace_499032
  have hstable : (prefixWord ++ tailWord_499032).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_499032).length < 2 ^ (prefixWord ++ tailWord_499032).sum := by decide
  have hdescent : baseEnd_499032 < baseStart_499032 := by decide
  rcases family_descends (prefixWord ++ tailWord_499032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_499100 : List Nat := [2, 2, 3, 4, 2, 1, 1, 1, 5]
def baseStart_499100 : Nat := 118140960795 + 499100 * 2 ^ 59
def prefixEnd_499100 : Nat := 4983230072969 + 3 ^ 40 * 499100 * 2
def baseEnd_499100 : Nat := 113901419848490001179861

theorem tailTrace_499100 : CollatzResearch.WordTrace tailWord_499100 prefixEnd_499100 113901419848490001179861 := by
  unfold tailWord_499100
  simp only [CollatzResearch.WordTrace]
  refine ⟨9101836245926707169423377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12135781661235609559231169 9101836245926707169423377)
  ·
    refine ⟨6826377184445030377067533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9101836245926707169423377 6826377184445030377067533)
    ·
      refine ⟨2559891444166886391400325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6826377184445030377067533 2559891444166886391400325)
      ·
        refine ⟨479979645781291198387561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2559891444166886391400325 479979645781291198387561)
        ·
          refine ⟨359984734335968398790671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 479979645781291198387561 359984734335968398790671)
          ·
            refine ⟨539977101503952598186007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 359984734335968398790671 539977101503952598186007)
            ·
              refine ⟨809965652255928897279011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 539977101503952598186007 809965652255928897279011)
              ·
                refine ⟨1214948478383893345918517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 809965652255928897279011 1214948478383893345918517)
                ·
                  refine ⟨113901419848490001179861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1214948478383893345918517 113901419848490001179861)
                  ·
                    rfl

theorem cell21_499100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 2, 1, 1, 1, 5].length) (baseStart_499100 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_499100 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_499100 prefixEnd_499100 := by exact prefixLift 499100
  have htrace : WordTrace (prefixWord ++ tailWord_499100) baseStart_499100 baseEnd_499100 := by
    simpa [prefixWord, tailWord_499100, baseEnd_499100] using wordTrace_append hprefix tailTrace_499100
  have hstable : (prefixWord ++ tailWord_499100).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_499100).length < 2 ^ (prefixWord ++ tailWord_499100).sum := by decide
  have hdescent : baseEnd_499100 < baseStart_499100 := by decide
  rcases family_descends (prefixWord ++ tailWord_499100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_499184 : List Nat := [2, 1, 1, 1, 3, 4, 1, 1, 7]
def baseStart_499184 : Nat := 118140960795 + 499184 * 2 ^ 59
def prefixEnd_499184 : Nat := 4983230072969 + 3 ^ 40 * 499184 * 2
def baseEnd_499184 : Nat := 113920589792924521779689

theorem tailTrace_499184 : CollatzResearch.WordTrace tailWord_499184 prefixEnd_499184 113920589792924521779689 := by
  unfold tailWord_499184
  simp only [CollatzResearch.WordTrace]
  refine ⟨9103368111774548342452303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12137824149032731123269737 9103368111774548342452303)
  ·
    refine ⟨13655052167661822513678455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9103368111774548342452303 13655052167661822513678455)
    ·
      refine ⟨20482578251492733770517683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13655052167661822513678455 20482578251492733770517683)
      ·
        refine ⟨30723867377239100655776525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20482578251492733770517683 30723867377239100655776525)
        ·
          refine ⟨11521450266464662745916197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30723867377239100655776525 11521450266464662745916197)
          ·
            refine ⟨2160271924962124264859287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11521450266464662745916197 2160271924962124264859287)
            ·
              refine ⟨3240407887443186397288931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2160271924962124264859287 3240407887443186397288931)
              ·
                refine ⟨4860611831164779595933397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3240407887443186397288931 4860611831164779595933397)
                ·
                  refine ⟨113920589792924521779689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4860611831164779595933397 113920589792924521779689)
                  ·
                    rfl

theorem cell21_499184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 1, 1, 7].length) (baseStart_499184 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_499184 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_499184 prefixEnd_499184 := by exact prefixLift 499184
  have htrace : WordTrace (prefixWord ++ tailWord_499184) baseStart_499184 baseEnd_499184 := by
    simpa [prefixWord, tailWord_499184, baseEnd_499184] using wordTrace_append hprefix tailTrace_499184
  have hstable : (prefixWord ++ tailWord_499184).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_499184).length < 2 ^ (prefixWord ++ tailWord_499184).sum := by decide
  have hdescent : baseEnd_499184 < baseStart_499184 := by decide
  rcases family_descends (prefixWord ++ tailWord_499184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_499305 : List Nat := [1, 2, 1, 1, 1, 4, 4, 7]
def baseStart_499305 : Nat := 118140960795 + 499305 * 2 ^ 59
def prefixEnd_499305 : Nat := 4983230072969 + 3 ^ 40 * 499305 * 2
def baseEnd_499305 : Nat := 37982734547151733420925

theorem tailTrace_499305 : CollatzResearch.WordTrace tailWord_499305 prefixEnd_499305 37982734547151733420925 := by
  unfold tailWord_499305
  simp only [CollatzResearch.WordTrace]
  refine ⟨18211149456110734350059369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12140766304073822900039579 18211149456110734350059369)
  ·
    refine ⟨13658362092083050762544527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18211149456110734350059369 13658362092083050762544527)
    ·
      refine ⟨20487543138124576143816791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13658362092083050762544527 20487543138124576143816791)
      ·
        refine ⟨30731314707186864215725187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20487543138124576143816791 30731314707186864215725187)
        ·
          refine ⟨46096972060780296323587781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30731314707186864215725187 46096972060780296323587781)
          ·
            refine ⟨8643182261396305560672709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46096972060780296323587781 8643182261396305560672709)
            ·
              refine ⟨1620596674011807292626133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8643182261396305560672709 1620596674011807292626133)
              ·
                refine ⟨37982734547151733420925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1620596674011807292626133 37982734547151733420925)
                ·
                  rfl

theorem cell21_499305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 4, 7].length) (baseStart_499305 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_499305 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_499305 prefixEnd_499305 := by exact prefixLift 499305
  have htrace : WordTrace (prefixWord ++ tailWord_499305) baseStart_499305 baseEnd_499305 := by
    simpa [prefixWord, tailWord_499305, baseEnd_499305] using wordTrace_append hprefix tailTrace_499305
  have hstable : (prefixWord ++ tailWord_499305).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_499305).length < 2 ^ (prefixWord ++ tailWord_499305).sum := by decide
  have hdescent : baseEnd_499305 < baseStart_499305 := by decide
  rcases family_descends (prefixWord ++ tailWord_499305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_499421 : List Nat := [1, 4, 3, 3, 2, 1, 1, 3, 3]
def baseStart_499421 : Nat := 118140960795 + 499421 * 2 ^ 59
def prefixEnd_499421 : Nat := 4983230072969 + 3 ^ 40 * 499421 * 2
def baseEnd_499421 : Nat := 113974676421864776329205

theorem tailTrace_499421 : CollatzResearch.WordTrace tailWord_499421 prefixEnd_499421 113974676421864776329205 := by
  unfold tailWord_499421
  simp only [CollatzResearch.WordTrace]
  refine ⟨18215380323690486161282117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12143586882460324107521411 18215380323690486161282117)
  ·
    refine ⟨3415383810691966155240397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18215380323690486161282117 3415383810691966155240397)
    ·
      refine ⟨1280768929009487308215149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3415383810691966155240397 1280768929009487308215149)
      ·
        refine ⟨480288348378557740580681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1280768929009487308215149 480288348378557740580681)
        ·
          refine ⟨360216261283918305435511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 480288348378557740580681 360216261283918305435511)
          ·
            refine ⟨540324391925877458153267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 360216261283918305435511 540324391925877458153267)
            ·
              refine ⟨810486587888816187229901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 540324391925877458153267 810486587888816187229901)
              ·
                refine ⟨303932470458306070211213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 810486587888816187229901 303932470458306070211213)
                ·
                  refine ⟨113974676421864776329205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 303932470458306070211213 113974676421864776329205)
                  ·
                    rfl

theorem cell21_499421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 2, 1, 1, 3, 3].length) (baseStart_499421 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_499421 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_499421 prefixEnd_499421 := by exact prefixLift 499421
  have htrace : WordTrace (prefixWord ++ tailWord_499421) baseStart_499421 baseEnd_499421 := by
    simpa [prefixWord, tailWord_499421, baseEnd_499421] using wordTrace_append hprefix tailTrace_499421
  have hstable : (prefixWord ++ tailWord_499421).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_499421).length < 2 ^ (prefixWord ++ tailWord_499421).sum := by decide
  have hdescent : baseEnd_499421 < baseStart_499421 := by decide
  rcases family_descends (prefixWord ++ tailWord_499421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_499446 : List Nat := [5, 1, 1, 1, 1, 5, 1, 1, 5]
def baseStart_499446 : Nat := 118140960795 + 499446 * 2 ^ 59
def prefixEnd_499446 : Nat := 4983230072969 + 3 ^ 40 * 499446 * 2
def baseEnd_499446 : Nat := 113980381762470288412487

theorem tailTrace_499446 : CollatzResearch.WordTrace tailWord_499446 prefixEnd_499446 113980381762470288412487 := by
  unfold tailWord_499446
  simp only [CollatzResearch.WordTrace]
  refine ⟨1138518259287494714433887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 12144194765733276953961461 1138518259287494714433887)
  ·
    refine ⟨1707777388931242071650831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1138518259287494714433887 1707777388931242071650831)
    ·
      refine ⟨2561666083396863107476247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1707777388931242071650831 2561666083396863107476247)
      ·
        refine ⟨3842499125095294661214371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2561666083396863107476247 3842499125095294661214371)
        ·
          refine ⟨5763748687642941991821557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3842499125095294661214371 5763748687642941991821557)
          ·
            refine ⟨540351439466525811733271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5763748687642941991821557 540351439466525811733271)
            ·
              refine ⟨810527159199788717599907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 540351439466525811733271 810527159199788717599907)
              ·
                refine ⟨1215790738799683076399861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 810527159199788717599907 1215790738799683076399861)
                ·
                  refine ⟨113980381762470288412487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1215790738799683076399861 113980381762470288412487)
                  ·
                    rfl

theorem cell21_499446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 5, 1, 1, 5].length) (baseStart_499446 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_499446 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_499446 prefixEnd_499446 := by exact prefixLift 499446
  have htrace : WordTrace (prefixWord ++ tailWord_499446) baseStart_499446 baseEnd_499446 := by
    simpa [prefixWord, tailWord_499446, baseEnd_499446] using wordTrace_append hprefix tailTrace_499446
  have hstable : (prefixWord ++ tailWord_499446).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_499446).length < 2 ^ (prefixWord ++ tailWord_499446).sum := by decide
  have hdescent : baseEnd_499446 < baseStart_499446 := by decide
  rcases family_descends (prefixWord ++ tailWord_499446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_499457 : List Nat := [1, 2, 4, 1, 1, 1, 3, 8]
def baseStart_499457 : Nat := 118140960795 + 499457 * 2 ^ 59
def prefixEnd_499457 : Nat := 4983230072969 + 3 ^ 40 * 499457 * 2
def baseEnd_499457 : Nat := 37994297370778904576377

theorem tailTrace_499457 : CollatzResearch.WordTrace tailWord_499457 prefixEnd_499457 37994297370778904576377 := by
  unfold tailWord_499457
  simp only [CollatzResearch.WordTrace]
  refine ⟨18216693351560064309592625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12144462234373376206395083 18216693351560064309592625)
  ·
    refine ⟨13662520013670048232194469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18216693351560064309592625 13662520013670048232194469)
    ·
      refine ⟨2561722502563134043536463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13662520013670048232194469 2561722502563134043536463)
      ·
        refine ⟨3842583753844701065304695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2561722502563134043536463 3842583753844701065304695)
        ·
          refine ⟨5763875630767051597957043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3842583753844701065304695 5763875630767051597957043)
          ·
            refine ⟨8645813446150577396935565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5763875630767051597957043 8645813446150577396935565)
            ·
              refine ⟨3242180042306466523850837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8645813446150577396935565 3242180042306466523850837)
              ·
                refine ⟨37994297370778904576377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3242180042306466523850837 37994297370778904576377)
                ·
                  rfl

theorem cell21_499457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 3, 8].length) (baseStart_499457 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_499457 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_499457 prefixEnd_499457 := by exact prefixLift 499457
  have htrace : WordTrace (prefixWord ++ tailWord_499457) baseStart_499457 baseEnd_499457 := by
    simpa [prefixWord, tailWord_499457, baseEnd_499457] using wordTrace_append hprefix tailTrace_499457
  have hstable : (prefixWord ++ tailWord_499457).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_499457).length < 2 ^ (prefixWord ++ tailWord_499457).sum := by decide
  have hdescent : baseEnd_499457 < baseStart_499457 := by decide
  rcases family_descends (prefixWord ++ tailWord_499457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_499460 : List Nat := [2, 3, 2, 2, 1, 3, 1, 3, 4]
def baseStart_499460 : Nat := 118140960795 + 499460 * 2 ^ 59
def prefixEnd_499460 : Nat := 4983230072969 + 3 ^ 40 * 499460 * 2
def baseEnd_499460 : Nat := 113983576753209375179125

theorem tailTrace_499460 : CollatzResearch.WordTrace tailWord_499460 prefixEnd_499460 113983576753209375179125 := by
  unfold tailWord_499460
  simp only [CollatzResearch.WordTrace]
  refine ⟨9108401385274597910975917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12144535180366130547967889 9108401385274597910975917)
  ·
    refine ⟨3415650519477974216615969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9108401385274597910975917 3415650519477974216615969)
    ·
      refine ⟨2561737889608480662461977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3415650519477974216615969 2561737889608480662461977)
      ·
        refine ⟨1921303417206360496846483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2561737889608480662461977 1921303417206360496846483)
        ·
          refine ⟨2881955125809540745269725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1921303417206360496846483 2881955125809540745269725)
          ·
            refine ⟨1080733172178577779476147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2881955125809540745269725 1080733172178577779476147)
            ·
              refine ⟨1621099758267866669214221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1080733172178577779476147 1621099758267866669214221)
              ·
                refine ⟨607912409350450000955333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1621099758267866669214221 607912409350450000955333)
                ·
                  refine ⟨113983576753209375179125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 607912409350450000955333 113983576753209375179125)
                  ·
                    rfl

theorem cell21_499460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 1, 3, 4].length) (baseStart_499460 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_499460 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_499460 prefixEnd_499460 := by exact prefixLift 499460
  have htrace : WordTrace (prefixWord ++ tailWord_499460) baseStart_499460 baseEnd_499460 := by
    simpa [prefixWord, tailWord_499460, baseEnd_499460] using wordTrace_append hprefix tailTrace_499460
  have hstable : (prefixWord ++ tailWord_499460).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_499460).length < 2 ^ (prefixWord ++ tailWord_499460).sum := by decide
  have hdescent : baseEnd_499460 < baseStart_499460 := by decide
  rcases family_descends (prefixWord ++ tailWord_499460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_499564 : List Nat := [2, 2, 1, 1, 4, 2, 1, 3, 5]
def baseStart_499564 : Nat := 118140960795 + 499564 * 2 ^ 59
def prefixEnd_499564 : Nat := 4983230072969 + 3 ^ 40 * 499564 * 2
def baseEnd_499564 : Nat := 114007310970128305445579

theorem tailTrace_499564 : CollatzResearch.WordTrace tailWord_499564 prefixEnd_499564 114007310970128305445579 := by
  unfold tailWord_499564
  simp only [CollatzResearch.WordTrace]
  refine ⟨9110297981086210791868873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12147063974781614389158497 9110297981086210791868873)
  ·
    refine ⟨6832723485814658093901655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9110297981086210791868873 6832723485814658093901655)
    ·
      refine ⟨10249085228721987140852483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6832723485814658093901655 10249085228721987140852483)
      ·
        refine ⟨15373627843082980711278725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10249085228721987140852483 15373627843082980711278725)
        ·
          refine ⟨2882555220578058883364761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15373627843082980711278725 2882555220578058883364761)
          ·
            refine ⟨2161916415433544162523571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2882555220578058883364761 2161916415433544162523571)
            ·
              refine ⟨3242874623150316243785357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2161916415433544162523571 3242874623150316243785357)
              ·
                refine ⟨1216077983681368591419509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3242874623150316243785357 1216077983681368591419509)
                ·
                  refine ⟨114007310970128305445579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1216077983681368591419509 114007310970128305445579)
                  ·
                    rfl

theorem cell21_499564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 5].length) (baseStart_499564 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_499564 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_499564 prefixEnd_499564 := by exact prefixLift 499564
  have htrace : WordTrace (prefixWord ++ tailWord_499564) baseStart_499564 baseEnd_499564 := by
    simpa [prefixWord, tailWord_499564, baseEnd_499564] using wordTrace_append hprefix tailTrace_499564
  have hstable : (prefixWord ++ tailWord_499564).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_499564).length < 2 ^ (prefixWord ++ tailWord_499564).sum := by decide
  have hdescent : baseEnd_499564 < baseStart_499564 := by decide
  rcases family_descends (prefixWord ++ tailWord_499564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_499615 : List Nat := [1, 1, 2, 5, 3, 1, 3, 2, 3]
def baseStart_499615 : Nat := 118140960795 + 499615 * 2 ^ 59
def prefixEnd_499615 : Nat := 4983230072969 + 3 ^ 40 * 499615 * 2
def baseEnd_499615 : Nat := 114018949864963550095475

theorem tailTrace_499615 : CollatzResearch.WordTrace tailWord_499615 prefixEnd_499615 114018949864963550095475 := by
  unfold tailWord_499615
  simp only [CollatzResearch.WordTrace]
  refine ⟨18222456084987657293844299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12148304056658438195896199 18222456084987657293844299)
  ·
    refine ⟨27333684127481485940766449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18222456084987657293844299 27333684127481485940766449)
    ·
      refine ⟨20500263095611114455574837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27333684127481485940766449 20500263095611114455574837)
      ·
        refine ⟨1921899665213541980210141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 20500263095611114455574837 1921899665213541980210141)
        ·
          refine ⟨720712374455078242578803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1921899665213541980210141 720712374455078242578803)
          ·
            refine ⟨1081068561682617363868205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 720712374455078242578803 1081068561682617363868205)
            ·
              refine ⟨405400710630981511450577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1081068561682617363868205 405400710630981511450577)
              ·
                refine ⟨304050532973236133587933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 405400710630981511450577 304050532973236133587933)
                ·
                  refine ⟨114018949864963550095475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 304050532973236133587933 114018949864963550095475)
                  ·
                    rfl

theorem cell21_499615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 3, 2, 3].length) (baseStart_499615 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_499615 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_499615 prefixEnd_499615 := by exact prefixLift 499615
  have htrace : WordTrace (prefixWord ++ tailWord_499615) baseStart_499615 baseEnd_499615 := by
    simpa [prefixWord, tailWord_499615, baseEnd_499615] using wordTrace_append hprefix tailTrace_499615
  have hstable : (prefixWord ++ tailWord_499615).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_499615).length < 2 ^ (prefixWord ++ tailWord_499615).sum := by decide
  have hdescent : baseEnd_499615 < baseStart_499615 := by decide
  rcases family_descends (prefixWord ++ tailWord_499615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_499671 : List Nat := [1, 1, 3, 2, 1, 1, 6, 2, 4]
def baseStart_499671 : Nat := 118140960795 + 499671 * 2 ^ 59
def prefixEnd_499671 : Nat := 4983230072969 + 3 ^ 40 * 499671 * 2
def baseEnd_499671 : Nat := 114031729827919897162027

theorem tailTrace_499671 : CollatzResearch.WordTrace tailWord_499671 prefixEnd_499671 114031729827919897162027 := by
  unfold tailWord_499671
  simp only [CollatzResearch.WordTrace]
  refine ⟨18224498572784778857882867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12149665715189852571921911 18224498572784778857882867)
  ·
    refine ⟨27336747859177168286824301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18224498572784778857882867 27336747859177168286824301)
    ·
      refine ⟨10251280447191438107559113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27336747859177168286824301 10251280447191438107559113)
      ·
        refine ⟨7688460335393578580669335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10251280447191438107559113 7688460335393578580669335)
        ·
          refine ⟨11532690503090367871004003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7688460335393578580669335 11532690503090367871004003)
          ·
            refine ⟨17299035754635551806506005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11532690503090367871004003 17299035754635551806506005)
            ·
              refine ⟨810892300998541490929969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 17299035754635551806506005 810892300998541490929969)
              ·
                refine ⟨608169225748906118197477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 810892300998541490929969 608169225748906118197477)
                ·
                  refine ⟨114031729827919897162027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 608169225748906118197477 114031729827919897162027)
                  ·
                    rfl

theorem cell21_499671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 6, 2, 4].length) (baseStart_499671 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_499671 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_499671 prefixEnd_499671 := by exact prefixLift 499671
  have htrace : WordTrace (prefixWord ++ tailWord_499671) baseStart_499671 baseEnd_499671 := by
    simpa [prefixWord, tailWord_499671, baseEnd_499671] using wordTrace_append hprefix tailTrace_499671
  have hstable : (prefixWord ++ tailWord_499671).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_499671).length < 2 ^ (prefixWord ++ tailWord_499671).sum := by decide
  have hdescent : baseEnd_499671 < baseStart_499671 := by decide
  rcases family_descends (prefixWord ++ tailWord_499671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_499674 : List Nat := [3, 1, 1, 2, 5, 1, 1, 4, 3]
def baseStart_499674 : Nat := 118140960795 + 499674 * 2 ^ 59
def prefixEnd_499674 : Nat := 4983230072969 + 3 ^ 40 * 499674 * 2
def baseEnd_499674 : Nat := 114032414468792558612021

theorem tailTrace_499674 : CollatzResearch.WordTrace tailWord_499674 prefixEnd_499674 114032414468792558612021 := by
  unfold tailWord_499674
  simp only [CollatzResearch.WordTrace]
  refine ⟨4556151997943477592560519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12149738661182606913494717 4556151997943477592560519)
  ·
    refine ⟨6834227996915216388840779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4556151997943477592560519 6834227996915216388840779)
    ·
      refine ⟨10251341995372824583261169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6834227996915216388840779 10251341995372824583261169)
      ·
        refine ⟨7688506496529618437445877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10251341995372824583261169 7688506496529618437445877)
        ·
          refine ⟨720797484049651728510551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7688506496529618437445877 720797484049651728510551)
          ·
            refine ⟨1081196226074477592765827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 720797484049651728510551 1081196226074477592765827)
            ·
              refine ⟨1621794339111716389148741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1081196226074477592765827 1621794339111716389148741)
              ·
                refine ⟨304086438583446822965389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1621794339111716389148741 304086438583446822965389)
                ·
                  refine ⟨114032414468792558612021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 304086438583446822965389 114032414468792558612021)
                  ·
                    rfl

theorem cell21_499674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 1, 4, 3].length) (baseStart_499674 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_499674 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_499674 prefixEnd_499674 := by exact prefixLift 499674
  have htrace : WordTrace (prefixWord ++ tailWord_499674) baseStart_499674 baseEnd_499674 := by
    simpa [prefixWord, tailWord_499674, baseEnd_499674] using wordTrace_append hprefix tailTrace_499674
  have hstable : (prefixWord ++ tailWord_499674).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_499674).length < 2 ^ (prefixWord ++ tailWord_499674).sum := by decide
  have hdescent : baseEnd_499674 < baseStart_499674 := by decide
  rcases family_descends (prefixWord ++ tailWord_499674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_499733 : List Nat := [1, 3, 2, 1, 5, 1, 2, 1, 5]
def baseStart_499733 : Nat := 118140960795 + 499733 * 2 ^ 59
def prefixEnd_499733 : Nat := 4983230072969 + 3 ^ 40 * 499733 * 2
def baseEnd_499733 : Nat := 114045879072621567128567

theorem tailTrace_499733 : CollatzResearch.WordTrace tailWord_499733 prefixEnd_499733 114045879072621567128567 := by
  unfold tailWord_499733
  simp only [CollatzResearch.WordTrace]
  refine ⟨18226759898560163446639853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12151173265706775631093235 18226759898560163446639853)
  ·
    refine ⟨6835034961960061292489945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18226759898560163446639853 6835034961960061292489945)
    ·
      refine ⟨5126276221470045969367459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6835034961960061292489945 5126276221470045969367459)
      ·
        refine ⟨7689414332205068954051189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5126276221470045969367459 7689414332205068954051189)
        ·
          refine ⟨720882593644225214442299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7689414332205068954051189 720882593644225214442299)
          ·
            refine ⟨1081323890466337821663449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 720882593644225214442299 1081323890466337821663449)
            ·
              refine ⟨810992917849753366247587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1081323890466337821663449 810992917849753366247587)
              ·
                refine ⟨1216489376774630049371381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 810992917849753366247587 1216489376774630049371381)
                ·
                  refine ⟨114045879072621567128567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1216489376774630049371381 114045879072621567128567)
                  ·
                    rfl

theorem cell21_499733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 2, 1, 5].length) (baseStart_499733 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_499733 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_499733 prefixEnd_499733 := by exact prefixLift 499733
  have htrace : WordTrace (prefixWord ++ tailWord_499733) baseStart_499733 baseEnd_499733 := by
    simpa [prefixWord, tailWord_499733, baseEnd_499733] using wordTrace_append hprefix tailTrace_499733
  have hstable : (prefixWord ++ tailWord_499733).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_499733).length < 2 ^ (prefixWord ++ tailWord_499733).sum := by decide
  have hdescent : baseEnd_499733 < baseStart_499733 := by decide
  rcases family_descends (prefixWord ++ tailWord_499733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_499761 : List Nat := [1, 2, 2, 3, 1, 4, 1, 7]
def baseStart_499761 : Nat := 118140960795 + 499761 * 2 ^ 59
def prefixEnd_499761 : Nat := 4983230072969 + 3 ^ 40 * 499761 * 2
def baseEnd_499761 : Nat := 38017423018033246887281

theorem tailTrace_499761 : CollatzResearch.WordTrace tailWord_499761 prefixEnd_499761 38017423018033246887281 := by
  unfold tailWord_499761
  simp only [CollatzResearch.WordTrace]
  refine ⟨18227781142458724228659137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12151854094972482819106091 18227781142458724228659137)
  ·
    refine ⟨13670835856844043171494353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18227781142458724228659137 13670835856844043171494353)
    ·
      refine ⟨10253126892633032378620765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13670835856844043171494353 10253126892633032378620765)
      ·
        refine ⟨3844922584737387141982787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10253126892633032378620765 3844922584737387141982787)
        ·
          refine ⟨5767383877106080712974181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3844922584737387141982787 5767383877106080712974181)
          ·
            refine ⟨1081384476957390133682659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5767383877106080712974181 1081384476957390133682659)
            ·
              refine ⟨1622076715436085200523989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1081384476957390133682659 1622076715436085200523989)
              ·
                refine ⟨38017423018033246887281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1622076715436085200523989 38017423018033246887281)
                ·
                  rfl

theorem cell21_499761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 1, 7].length) (baseStart_499761 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_499761 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_499761 prefixEnd_499761 := by exact prefixLift 499761
  have htrace : WordTrace (prefixWord ++ tailWord_499761) baseStart_499761 baseEnd_499761 := by
    simpa [prefixWord, tailWord_499761, baseEnd_499761] using wordTrace_append hprefix tailTrace_499761
  have hstable : (prefixWord ++ tailWord_499761).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_499761).length < 2 ^ (prefixWord ++ tailWord_499761).sum := by decide
  have hdescent : baseEnd_499761 < baseStart_499761 := by decide
  rcases family_descends (prefixWord ++ tailWord_499761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_499775 : List Nat := [1, 1, 2, 2, 3, 1, 2, 2, 7]
def baseStart_499775 : Nat := 118140960795 + 499775 * 2 ^ 59
def prefixEnd_499775 : Nat := 4983230072969 + 3 ^ 40 * 499775 * 2
def baseEnd_499775 : Nat := 114055464044838827428481

theorem tailTrace_499775 : CollatzResearch.WordTrace tailWord_499775 prefixEnd_499775 114055464044838827428481 := by
  unfold tailWord_499775
  simp only [CollatzResearch.WordTrace]
  refine ⟨18228291764408004619668779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12152194509605336413112519 18228291764408004619668779)
  ·
    refine ⟨27342437646612006929503169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18228291764408004619668779 27342437646612006929503169)
    ·
      refine ⟨20506828234959005197127377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27342437646612006929503169 20506828234959005197127377)
      ·
        refine ⟨15380121176219253897845533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20506828234959005197127377 15380121176219253897845533)
        ·
          refine ⟨5767545441082220211692075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15380121176219253897845533 5767545441082220211692075)
          ·
            refine ⟨8651318161623330317538113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5767545441082220211692075 8651318161623330317538113)
            ·
              refine ⟨6488488621217497738153585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8651318161623330317538113 6488488621217497738153585)
              ·
                refine ⟨4866366465913123303615189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6488488621217497738153585 4866366465913123303615189)
                ·
                  refine ⟨114055464044838827428481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4866366465913123303615189 114055464044838827428481)
                  ·
                    rfl

theorem cell21_499775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 2, 7].length) (baseStart_499775 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_499775 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_499775 prefixEnd_499775 := by exact prefixLift 499775
  have htrace : WordTrace (prefixWord ++ tailWord_499775) baseStart_499775 baseEnd_499775 := by
    simpa [prefixWord, tailWord_499775, baseEnd_499775] using wordTrace_append hprefix tailTrace_499775
  have hstable : (prefixWord ++ tailWord_499775).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_499775).length < 2 ^ (prefixWord ++ tailWord_499775).sum := by decide
  have hdescent : baseEnd_499775 < baseStart_499775 := by decide
  rcases family_descends (prefixWord ++ tailWord_499775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_499798 : List Nat := [5, 2, 2, 1, 1, 1, 4, 1, 4]
def baseStart_499798 : Nat := 118140960795 + 499798 * 2 ^ 59
def prefixEnd_499798 : Nat := 4983230072969 + 3 ^ 40 * 499798 * 2
def baseEnd_499798 : Nat := 114060712958195898545101

theorem tailTrace_499798 : CollatzResearch.WordTrace tailWord_499798 prefixEnd_499798 114060712958195898545101 := by
  unfold tailWord_499798
  simp only [CollatzResearch.WordTrace]
  refine ⟨1139320665207792471734753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 12152753762216453031837365 1139320665207792471734753)
  ·
    refine ⟨854490498905844353801065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1139320665207792471734753 854490498905844353801065)
    ·
      refine ⟨640867874179383265350799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 854490498905844353801065 640867874179383265350799)
      ·
        refine ⟨961301811269074898026199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 640867874179383265350799 961301811269074898026199)
        ·
          refine ⟨1441952716903612347039299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 961301811269074898026199 1441952716903612347039299)
          ·
            refine ⟨2162929075355418520558949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1441952716903612347039299 2162929075355418520558949)
            ·
              refine ⟨405549201629140972604803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2162929075355418520558949 405549201629140972604803)
              ·
                refine ⟨608323802443711458907205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 405549201629140972604803 608323802443711458907205)
                ·
                  refine ⟨114060712958195898545101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 608323802443711458907205 114060712958195898545101)
                  ·
                    rfl

theorem cell21_499798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 4, 1, 4].length) (baseStart_499798 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_499798 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_499798 prefixEnd_499798 := by exact prefixLift 499798
  have htrace : WordTrace (prefixWord ++ tailWord_499798) baseStart_499798 baseEnd_499798 := by
    simpa [prefixWord, tailWord_499798, baseEnd_499798] using wordTrace_append hprefix tailTrace_499798
  have hstable : (prefixWord ++ tailWord_499798).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_499798).length < 2 ^ (prefixWord ++ tailWord_499798).sum := by decide
  have hdescent : baseEnd_499798 < baseStart_499798 := by decide
  rcases family_descends (prefixWord ++ tailWord_499798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_499868 : List Nat := [2, 2, 3, 2, 1, 1, 3, 2, 5]
def baseStart_499868 : Nat := 118140960795 + 499868 * 2 ^ 59
def prefixEnd_499868 : Nat := 4983230072969 + 3 ^ 40 * 499868 * 2
def baseEnd_499868 : Nat := 114076687911891332378291

theorem tailTrace_499868 : CollatzResearch.WordTrace tailWord_499868 prefixEnd_499868 114076687911891332378291 := by
  unfold tailWord_499868
  simp only [CollatzResearch.WordTrace]
  refine ⟨9115841876535540751402129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12154455835380721001869505 9115841876535540751402129)
  ·
    refine ⟨6836881407401655563551597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9115841876535540751402129 6836881407401655563551597)
    ·
      refine ⟨2563830527775620836331849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6836881407401655563551597 2563830527775620836331849)
      ·
        refine ⟨1922872895831715627248887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2563830527775620836331849 1922872895831715627248887)
        ·
          refine ⟨2884309343747573440873331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1922872895831715627248887 2884309343747573440873331)
          ·
            refine ⟨4326464015621360161309997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2884309343747573440873331 4326464015621360161309997)
            ·
              refine ⟨1622424005858010060491249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4326464015621360161309997 1622424005858010060491249)
              ·
                refine ⟨1216818004393507545368437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1622424005858010060491249 1216818004393507545368437)
                ·
                  refine ⟨114076687911891332378291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1216818004393507545368437 114076687911891332378291)
                  ·
                    rfl

theorem cell21_499868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 3, 2, 5].length) (baseStart_499868 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_499868 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_499868 prefixEnd_499868 := by exact prefixLift 499868
  have htrace : WordTrace (prefixWord ++ tailWord_499868) baseStart_499868 baseEnd_499868 := by
    simpa [prefixWord, tailWord_499868, baseEnd_499868] using wordTrace_append hprefix tailTrace_499868
  have hstable : (prefixWord ++ tailWord_499868).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_499868).length < 2 ^ (prefixWord ++ tailWord_499868).sum := by decide
  have hdescent : baseEnd_499868 < baseStart_499868 := by decide
  rcases family_descends (prefixWord ++ tailWord_499868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_499896 : List Nat := [2, 1, 2, 1, 2, 1, 12]
def baseStart_499896 : Nat := 118140960795 + 499896 * 2 ^ 59
def prefixEnd_499896 : Nat := 4983230072969 + 3 ^ 40 * 499896 * 2
def baseEnd_499896 : Nat := 12675897543707722879063

theorem tailTrace_499896 : CollatzResearch.WordTrace tailWord_499896 prefixEnd_499896 12675897543707722879063 := by
  unfold tailWord_499896
  simp only [CollatzResearch.WordTrace]
  refine ⟨9116352498484821142411771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12155136664646428189882361 9116352498484821142411771)
  ·
    refine ⟨13674528747727231713617657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9116352498484821142411771 13674528747727231713617657)
    ·
      refine ⟨10255896560795423785213243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13674528747727231713617657 10255896560795423785213243)
      ·
        refine ⟨15383844841193135677819865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10255896560795423785213243 15383844841193135677819865)
        ·
          refine ⟨11537883630894851758364899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15383844841193135677819865 11537883630894851758364899)
          ·
            refine ⟨17306825446342277637547349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11537883630894851758364899 17306825446342277637547349)
            ·
              refine ⟨12675897543707722879063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 17306825446342277637547349 12675897543707722879063)
              ·
                rfl

theorem cell21_499896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 12].length) (baseStart_499896 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_499896 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_499896 prefixEnd_499896 := by exact prefixLift 499896
  have htrace : WordTrace (prefixWord ++ tailWord_499896) baseStart_499896 baseEnd_499896 := by
    simpa [prefixWord, tailWord_499896, baseEnd_499896] using wordTrace_append hprefix tailTrace_499896
  have hstable : (prefixWord ++ tailWord_499896).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_499896).length < 2 ^ (prefixWord ++ tailWord_499896).sum := by decide
  have hdescent : baseEnd_499896 < baseStart_499896 := by decide
  rcases family_descends (prefixWord ++ tailWord_499896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_500099 : List Nat := [1, 1, 1, 3, 7, 1, 2, 5]
def baseStart_500099 : Nat := 118140960795 + 500099 * 2 ^ 59
def prefixEnd_500099 : Nat := 4983230072969 + 3 ^ 40 * 500099 * 2
def baseEnd_500099 : Nat := 38043135086362088009273

theorem tailTrace_500099 : CollatzResearch.WordTrace tailWord_500099 prefixEnd_500099 38043135086362088009273 := by
  unfold tailWord_500099
  simp only [CollatzResearch.WordTrace]
  refine ⟨18240109015234207954463351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12160072676822805302975567 18240109015234207954463351)
  ·
    refine ⟨27360163522851311931695027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18240109015234207954463351 27360163522851311931695027)
    ·
      refine ⟨41040245284276967897542541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27360163522851311931695027 41040245284276967897542541)
      ·
        refine ⟨15390091981603862961578453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41040245284276967897542541 15390091981603862961578453)
        ·
          refine ⟨360705280818840538161995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 15390091981603862961578453 360705280818840538161995)
          ·
            refine ⟨541057921228260807242993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 360705280818840538161995 541057921228260807242993)
            ·
              refine ⟨405793440921195605432245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 541057921228260807242993 405793440921195605432245)
              ·
                refine ⟨38043135086362088009273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 405793440921195605432245 38043135086362088009273)
                ·
                  rfl

theorem cell21_500099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 7, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 7, 1, 2, 5].length) (baseStart_500099 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_500099 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_500099 prefixEnd_500099 := by exact prefixLift 500099
  have htrace : WordTrace (prefixWord ++ tailWord_500099) baseStart_500099 baseEnd_500099 := by
    simpa [prefixWord, tailWord_500099, baseEnd_500099] using wordTrace_append hprefix tailTrace_500099
  have hstable : (prefixWord ++ tailWord_500099).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_500099).length < 2 ^ (prefixWord ++ tailWord_500099).sum := by decide
  have hdescent : baseEnd_500099 < baseStart_500099 := by decide
  rcases family_descends (prefixWord ++ tailWord_500099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_500130 : List Nat := [3, 3, 1, 2, 1, 1, 5, 2, 3]
def baseStart_500130 : Nat := 118140960795 + 500130 * 2 ^ 59
def prefixEnd_500130 : Nat := 4983230072969 + 3 ^ 40 * 500130 * 2
def baseEnd_500130 : Nat := 114136479881437099011089

theorem tailTrace_500130 : CollatzResearch.WordTrace tailWord_500130 prefixEnd_500130 114136479881437099011089 := by
  unfold tailWord_500130
  simp only [CollatzResearch.WordTrace]
  refine ⟨4560309919530475062210461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12160826452081266832561229 4560309919530475062210461)
  ·
    refine ⟨1710116219823928148328923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4560309919530475062210461 1710116219823928148328923)
    ·
      refine ⟨2565174329735892222493385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1710116219823928148328923 2565174329735892222493385)
      ·
        refine ⟨1923880747301919166870039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2565174329735892222493385 1923880747301919166870039)
        ·
          refine ⟨2885821120952878750305059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1923880747301919166870039 2885821120952878750305059)
          ·
            refine ⟨4328731681429318125457589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2885821120952878750305059 4328731681429318125457589)
            ·
              refine ⟨405818595133998574261649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4328731681429318125457589 405818595133998574261649)
              ·
                refine ⟨304363946350498930696237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 405818595133998574261649 304363946350498930696237)
                ·
                  refine ⟨114136479881437099011089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 304363946350498930696237 114136479881437099011089)
                  ·
                    rfl

theorem cell21_500130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 5, 2, 3].length) (baseStart_500130 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_500130 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_500130 prefixEnd_500130 := by exact prefixLift 500130
  have htrace : WordTrace (prefixWord ++ tailWord_500130) baseStart_500130 baseEnd_500130 := by
    simpa [prefixWord, tailWord_500130, baseEnd_500130] using wordTrace_append hprefix tailTrace_500130
  have hstable : (prefixWord ++ tailWord_500130).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_500130).length < 2 ^ (prefixWord ++ tailWord_500130).sum := by decide
  have hdescent : baseEnd_500130 < baseStart_500130 := by decide
  rcases family_descends (prefixWord ++ tailWord_500130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_500169 : List Nat := [1, 2, 1, 1, 2, 1, 4, 1, 8]
def baseStart_500169 : Nat := 118140960795 + 500169 * 2 ^ 59
def prefixEnd_500169 : Nat := 4983230072969 + 3 ^ 40 * 500169 * 2
def baseEnd_500169 : Nat := 114145380212781697861009

theorem tailTrace_500169 : CollatzResearch.WordTrace tailWord_500169 prefixEnd_500169 114145380212781697861009 := by
  unfold tailWord_500169
  simp only [CollatzResearch.WordTrace]
  refine ⟨18242662124980609909511561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12161774749987073273007707 18242662124980609909511561)
  ·
    refine ⟨13681996593735457432133671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18242662124980609909511561 13681996593735457432133671)
    ·
      refine ⟨20522994890603186148200507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13681996593735457432133671 20522994890603186148200507)
      ·
        refine ⟨30784492335904779222300761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20522994890603186148200507 30784492335904779222300761)
        ·
          refine ⟨23088369251928584416725571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30784492335904779222300761 23088369251928584416725571)
          ·
            refine ⟨34632553877892876625088357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23088369251928584416725571 34632553877892876625088357)
            ·
              refine ⟨6493603852104914367204067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34632553877892876625088357 6493603852104914367204067)
              ·
                refine ⟨9740405778157371550806101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6493603852104914367204067 9740405778157371550806101)
                ·
                  refine ⟨114145380212781697861009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 9740405778157371550806101 114145380212781697861009)
                  ·
                    rfl

theorem cell21_500169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 1, 8].length) (baseStart_500169 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_500169 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_500169 prefixEnd_500169 := by exact prefixLift 500169
  have htrace : WordTrace (prefixWord ++ tailWord_500169) baseStart_500169 baseEnd_500169 := by
    simpa [prefixWord, tailWord_500169, baseEnd_500169] using wordTrace_append hprefix tailTrace_500169
  have hstable : (prefixWord ++ tailWord_500169).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_500169).length < 2 ^ (prefixWord ++ tailWord_500169).sum := by decide
  have hdescent : baseEnd_500169 < baseStart_500169 := by decide
  rcases family_descends (prefixWord ++ tailWord_500169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_500189 : List Nat := [1, 4, 3, 1, 1, 1, 3, 4, 3]
def baseStart_500189 : Nat := 118140960795 + 500189 * 2 ^ 59
def prefixEnd_500189 : Nat := 4983230072969 + 3 ^ 40 * 500189 * 2
def baseEnd_500189 : Nat := 114149944485266107527635

theorem tailTrace_500189 : CollatzResearch.WordTrace tailWord_500189 prefixEnd_500189 114149944485266107527635 := by
  unfold tailWord_500189
  simp only [CollatzResearch.WordTrace]
  refine ⟨18243391584908153325239621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12162261056605435550159747 18243391584908153325239621)
  ·
    refine ⟨3420635922170278748482429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18243391584908153325239621 3420635922170278748482429)
    ·
      refine ⟨1282738470813854530680911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3420635922170278748482429 1282738470813854530680911)
      ·
        refine ⟨1924107706220781796021367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1282738470813854530680911 1924107706220781796021367)
        ·
          refine ⟨2886161559331172694032051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1924107706220781796021367 2886161559331172694032051)
          ·
            refine ⟨4329242338996759041048077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2886161559331172694032051 4329242338996759041048077)
            ·
              refine ⟨1623465877123784640393029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4329242338996759041048077 1623465877123784640393029)
              ·
                refine ⟨304399851960709620073693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1623465877123784640393029 304399851960709620073693)
                ·
                  refine ⟨114149944485266107527635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 304399851960709620073693 114149944485266107527635)
                  ·
                    rfl

theorem cell21_500189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 3, 4, 3].length) (baseStart_500189 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_500189 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_500189 prefixEnd_500189 := by exact prefixLift 500189
  have htrace : WordTrace (prefixWord ++ tailWord_500189) baseStart_500189 baseEnd_500189 := by
    simpa [prefixWord, tailWord_500189, baseEnd_500189] using wordTrace_append hprefix tailTrace_500189
  have hstable : (prefixWord ++ tailWord_500189).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_500189).length < 2 ^ (prefixWord ++ tailWord_500189).sum := by decide
  have hdescent : baseEnd_500189 < baseStart_500189 := by decide
  rcases family_descends (prefixWord ++ tailWord_500189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_500237 : List Nat := [1, 7, 1, 1, 1, 1, 3, 2, 4]
def baseStart_500237 : Nat := 118140960795 + 500237 * 2 ^ 59
def prefixEnd_500237 : Nat := 4983230072969 + 3 ^ 40 * 500237 * 2
def baseEnd_500237 : Nat := 114160898739228690727537

theorem tailTrace_500237 : CollatzResearch.WordTrace tailWord_500237 prefixEnd_500237 114160898739228690727537 := by
  unfold tailWord_500237
  simp only [CollatzResearch.WordTrace]
  refine ⟨18245142288734257522986965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12163428192489505015324643 18245142288734257522986965)
  ·
    refine ⟨427620522392209160695007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 18245142288734257522986965 427620522392209160695007)
    ·
      refine ⟨641430783588313741042511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 427620522392209160695007 641430783588313741042511)
      ·
        refine ⟨962146175382470611563767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 641430783588313741042511 962146175382470611563767)
        ·
          refine ⟨1443219263073705917345651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 962146175382470611563767 1443219263073705917345651)
          ·
            refine ⟨2164828894610558876018477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1443219263073705917345651 2164828894610558876018477)
            ·
              refine ⟨811810835478959578506929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2164828894610558876018477 811810835478959578506929)
              ·
                refine ⟨608858126609219683880197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 811810835478959578506929 608858126609219683880197)
                ·
                  refine ⟨114160898739228690727537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 608858126609219683880197 114160898739228690727537)
                  ·
                    rfl

theorem cell21_500237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 3, 2, 4].length) (baseStart_500237 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_500237 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_500237 prefixEnd_500237 := by exact prefixLift 500237
  have htrace : WordTrace (prefixWord ++ tailWord_500237) baseStart_500237 baseEnd_500237 := by
    simpa [prefixWord, tailWord_500237, baseEnd_500237] using wordTrace_append hprefix tailTrace_500237
  have hstable : (prefixWord ++ tailWord_500237).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_500237).length < 2 ^ (prefixWord ++ tailWord_500237).sum := by decide
  have hdescent : baseEnd_500237 < baseStart_500237 := by decide
  rcases family_descends (prefixWord ++ tailWord_500237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_500248 : List Nat := [2, 1, 2, 3, 3, 2, 2, 1, 5]
def baseStart_500248 : Nat := 118140960795 + 500248 * 2 ^ 59
def prefixEnd_500248 : Nat := 4983230072969 + 3 ^ 40 * 500248 * 2
def baseEnd_500248 : Nat := 114163409089095116044181

theorem tailTrace_500248 : CollatzResearch.WordTrace tailWord_500248 prefixEnd_500248 114163409089095116044181 := by
  unfold tailWord_500248
  simp only [CollatzResearch.WordTrace]
  refine ⟨9122771745847203200818699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12163695661129604267758265 9122771745847203200818699)
  ·
    refine ⟨13684157618770804801228049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9122771745847203200818699 13684157618770804801228049)
    ·
      refine ⟨10263118214078103600921037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13684157618770804801228049 10263118214078103600921037)
      ·
        refine ⟨3848669330279288850345389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10263118214078103600921037 3848669330279288850345389)
        ·
          refine ⟨1443250998854733318879521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3848669330279288850345389 1443250998854733318879521)
          ·
            refine ⟨1082438249141049989159641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1443250998854733318879521 1082438249141049989159641)
            ·
              refine ⟨811828686855787491869731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1082438249141049989159641 811828686855787491869731)
              ·
                refine ⟨1217743030283681237804597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 811828686855787491869731 1217743030283681237804597)
                ·
                  refine ⟨114163409089095116044181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1217743030283681237804597 114163409089095116044181)
                  ·
                    rfl

theorem cell21_500248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 2, 1, 5].length) (baseStart_500248 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_500248 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_500248 prefixEnd_500248 := by exact prefixLift 500248
  have htrace : WordTrace (prefixWord ++ tailWord_500248) baseStart_500248 baseEnd_500248 := by
    simpa [prefixWord, tailWord_500248, baseEnd_500248] using wordTrace_append hprefix tailTrace_500248
  have hstable : (prefixWord ++ tailWord_500248).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_500248).length < 2 ^ (prefixWord ++ tailWord_500248).sum := by decide
  have hdescent : baseEnd_500248 < baseStart_500248 := by decide
  rcases family_descends (prefixWord ++ tailWord_500248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_500406 : List Nat := [5, 1, 3, 1, 3, 1, 1, 2, 4]
def baseStart_500406 : Nat := 118140960795 + 500406 * 2 ^ 59
def prefixEnd_500406 : Nat := 4983230072969 + 3 ^ 40 * 500406 * 2
def baseEnd_500406 : Nat := 114199466841721952410525

theorem tailTrace_500406 : CollatzResearch.WordTrace tailWord_500406 prefixEnd_500406 114199466841721952410525 := by
  unfold tailWord_500406
  simp only [CollatzResearch.WordTrace]
  refine ⟨1140706639070124961618067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 12167537483414666257259381 1140706639070124961618067)
  ·
    refine ⟨1711059958605187442427101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1140706639070124961618067 1711059958605187442427101)
    ·
      refine ⟨641647484476945290910163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1711059958605187442427101 641647484476945290910163)
      ·
        refine ⟨962471226715417936365245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 641647484476945290910163 962471226715417936365245)
        ·
          refine ⟨360926710018281726136967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 962471226715417936365245 360926710018281726136967)
          ·
            refine ⟨541390065027422589205451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 360926710018281726136967 541390065027422589205451)
            ·
              refine ⟨812085097541133883808177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 541390065027422589205451 812085097541133883808177)
              ·
                refine ⟨609063823155850412856133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 812085097541133883808177 609063823155850412856133)
                ·
                  refine ⟨114199466841721952410525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 609063823155850412856133 114199466841721952410525)
                  ·
                    rfl

theorem cell21_500406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 3, 1, 1, 2, 4].length) (baseStart_500406 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_500406 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_500406 prefixEnd_500406 := by exact prefixLift 500406
  have htrace : WordTrace (prefixWord ++ tailWord_500406) baseStart_500406 baseEnd_500406 := by
    simpa [prefixWord, tailWord_500406, baseEnd_500406] using wordTrace_append hprefix tailTrace_500406
  have hstable : (prefixWord ++ tailWord_500406).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_500406).length < 2 ^ (prefixWord ++ tailWord_500406).sum := by decide
  have hdescent : baseEnd_500406 < baseStart_500406 := by decide
  rcases family_descends (prefixWord ++ tailWord_500406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_500414 : List Nat := [4, 2, 1, 1, 2, 1, 3, 1, 6]
def baseStart_500414 : Nat := 118140960795 + 500414 * 2 ^ 59
def prefixEnd_500414 : Nat := 4983230072969 + 3 ^ 40 * 500414 * 2
def baseEnd_500414 : Nat := 114201292550715716277175

theorem tailTrace_500414 : CollatzResearch.WordTrace tailWord_500414 prefixEnd_500414 114201292550715716277175 := by
  unfold tailWord_500414
  simp only [CollatzResearch.WordTrace]
  refine ⟨2281449751136627094022537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12167732006062011168120197 2281449751136627094022537)
  ·
    refine ⟨1711087313352470320516903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2281449751136627094022537 1711087313352470320516903)
    ·
      refine ⟨2566630970028705480775355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1711087313352470320516903 2566630970028705480775355)
      ·
        refine ⟨3849946455043058221163033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2566630970028705480775355 3849946455043058221163033)
        ·
          refine ⟨2887459841282293665872275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3849946455043058221163033 2887459841282293665872275)
          ·
            refine ⟨4331189761923440498808413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2887459841282293665872275 4331189761923440498808413)
            ·
              refine ⟨1624196160721290187053155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4331189761923440498808413 1624196160721290187053155)
              ·
                refine ⟨2436294241081935280579733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1624196160721290187053155 2436294241081935280579733)
                ·
                  refine ⟨114201292550715716277175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2436294241081935280579733 114201292550715716277175)
                  ·
                    rfl

theorem cell21_500414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 3, 1, 6].length) (baseStart_500414 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_500414 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_500414 prefixEnd_500414 := by exact prefixLift 500414
  have htrace : WordTrace (prefixWord ++ tailWord_500414) baseStart_500414 baseEnd_500414 := by
    simpa [prefixWord, tailWord_500414, baseEnd_500414] using wordTrace_append hprefix tailTrace_500414
  have hstable : (prefixWord ++ tailWord_500414).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_500414).length < 2 ^ (prefixWord ++ tailWord_500414).sum := by decide
  have hdescent : baseEnd_500414 < baseStart_500414 := by decide
  rcases family_descends (prefixWord ++ tailWord_500414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_500468 : List Nat := [2, 6, 1, 1, 2, 1, 3, 2, 3]
def baseStart_500468 : Nat := 118140960795 + 500468 * 2 ^ 59
def prefixEnd_500468 : Nat := 4983230072969 + 3 ^ 40 * 500468 * 2
def baseEnd_500468 : Nat := 114213616086423622377065

theorem tailTrace_500468 : CollatzResearch.WordTrace tailWord_500468 prefixEnd_500468 114213616086423622377065 := by
  unfold tailWord_500468
  simp only [CollatzResearch.WordTrace]
  refine ⟨9126783775448691987323029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12169045033931589316430705 9126783775448691987323029)
  ·
    refine ⟨427817989474157436905767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 9126783775448691987323029 427817989474157436905767)
    ·
      refine ⟨641726984211236155358651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 427817989474157436905767 641726984211236155358651)
      ·
        refine ⟨962590476316854233037977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 641726984211236155358651 962590476316854233037977)
        ·
          refine ⟨721942857237640674778483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 962590476316854233037977 721942857237640674778483)
          ·
            refine ⟨1082914285856461012167725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 721942857237640674778483 1082914285856461012167725)
            ·
              refine ⟨406092857196172879562897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1082914285856461012167725 406092857196172879562897)
              ·
                refine ⟨304569642897129659672173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 406092857196172879562897 304569642897129659672173)
                ·
                  refine ⟨114213616086423622377065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 304569642897129659672173 114213616086423622377065)
                  ·
                    rfl

theorem cell21_500468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 3, 2, 3].length) (baseStart_500468 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_500468 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_500468 prefixEnd_500468 := by exact prefixLift 500468
  have htrace : WordTrace (prefixWord ++ tailWord_500468) baseStart_500468 baseEnd_500468 := by
    simpa [prefixWord, tailWord_500468, baseEnd_500468] using wordTrace_append hprefix tailTrace_500468
  have hstable : (prefixWord ++ tailWord_500468).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_500468).length < 2 ^ (prefixWord ++ tailWord_500468).sum := by decide
  have hdescent : baseEnd_500468 < baseStart_500468 := by decide
  rcases family_descends (prefixWord ++ tailWord_500468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_500476 : List Nat := [2, 2, 2, 1, 3, 4, 1, 1, 5]
def baseStart_500476 : Nat := 118140960795 + 500476 * 2 ^ 59
def prefixEnd_500476 : Nat := 4983230072969 + 3 ^ 40 * 500476 * 2
def baseEnd_500476 : Nat := 114215441795417386243715

theorem tailTrace_500476 : CollatzResearch.WordTrace tailWord_500476 prefixEnd_500476 114215441795417386243715 := by
  unfold tailWord_500476
  simp only [CollatzResearch.WordTrace]
  refine ⟨9126929667434200670468641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12169239556578934227291521 9126929667434200670468641)
  ·
    refine ⟨6845197250575650502851481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9126929667434200670468641 6845197250575650502851481)
    ·
      refine ⟨5133897937931737877138611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6845197250575650502851481 5133897937931737877138611)
      ·
        refine ⟨7700846906897606815707917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5133897937931737877138611 7700846906897606815707917)
        ·
          refine ⟨2887817590086602555890469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7700846906897606815707917 2887817590086602555890469)
          ·
            refine ⟨541465798141237979229463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2887817590086602555890469 541465798141237979229463)
            ·
              refine ⟨812198697211856968844195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 541465798141237979229463 812198697211856968844195)
              ·
                refine ⟨1218298045817785453266293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 812198697211856968844195 1218298045817785453266293)
                ·
                  refine ⟨114215441795417386243715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1218298045817785453266293 114215441795417386243715)
                  ·
                    rfl

theorem cell21_500476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 4, 1, 1, 5].length) (baseStart_500476 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_500476 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_500476 prefixEnd_500476 := by exact prefixLift 500476
  have htrace : WordTrace (prefixWord ++ tailWord_500476) baseStart_500476 baseEnd_500476 := by
    simpa [prefixWord, tailWord_500476, baseEnd_500476] using wordTrace_append hprefix tailTrace_500476
  have hstable : (prefixWord ++ tailWord_500476).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_500476).length < 2 ^ (prefixWord ++ tailWord_500476).sum := by decide
  have hdescent : baseEnd_500476 < baseStart_500476 := by decide
  rcases family_descends (prefixWord ++ tailWord_500476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_500490 : List Nat := [3, 1, 2, 2, 1, 2, 3, 3, 4]
def baseStart_500490 : Nat := 118140960795 + 500490 * 2 ^ 59
def prefixEnd_500490 : Nat := 4983230072969 + 3 ^ 40 * 500490 * 2
def baseEnd_500490 : Nat := 114218636786156473010353

theorem tailTrace_500490 : CollatzResearch.WordTrace tailWord_500490 prefixEnd_500490 114218636786156473010353 := by
  unfold tailWord_500490
  simp only [CollatzResearch.WordTrace]
  refine ⟨4563592489204420432986731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12169579971211787821297949 4563592489204420432986731)
  ·
    refine ⟨6845388733806630649480097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4563592489204420432986731 6845388733806630649480097)
    ·
      refine ⟨5134041550354972987110073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6845388733806630649480097 5134041550354972987110073)
      ·
        refine ⟨3850531162766229740332555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5134041550354972987110073 3850531162766229740332555)
        ·
          refine ⟨5775796744149344610498833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3850531162766229740332555 5775796744149344610498833)
          ·
            refine ⟨4331847558112008457874125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5775796744149344610498833 4331847558112008457874125)
            ·
              refine ⟨1624442834292003171702797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4331847558112008457874125 1624442834292003171702797)
              ·
                refine ⟨609166062859501189388549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1624442834292003171702797 609166062859501189388549)
                ·
                  refine ⟨114218636786156473010353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 609166062859501189388549 114218636786156473010353)
                  ·
                    rfl

theorem cell21_500490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 3, 3, 4].length) (baseStart_500490 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_500490 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_500490 prefixEnd_500490 := by exact prefixLift 500490
  have htrace : WordTrace (prefixWord ++ tailWord_500490) baseStart_500490 baseEnd_500490 := by
    simpa [prefixWord, tailWord_500490, baseEnd_500490] using wordTrace_append hprefix tailTrace_500490
  have hstable : (prefixWord ++ tailWord_500490).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_500490).length < 2 ^ (prefixWord ++ tailWord_500490).sum := by decide
  have hdescent : baseEnd_500490 < baseStart_500490 := by decide
  rcases family_descends (prefixWord ++ tailWord_500490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_500538 : List Nat := [3, 1, 1, 1, 7, 1, 1, 6]
def baseStart_500538 : Nat := 118140960795 + 500538 * 2 ^ 59
def prefixEnd_500538 : Nat := 4983230072969 + 3 ^ 40 * 500538 * 2
def baseEnd_500538 : Nat := 38076530346706352070085

theorem tailTrace_500538 : CollatzResearch.WordTrace tailWord_500538 prefixEnd_500538 38076530346706352070085 := by
  unfold tailWord_500538
  simp only [CollatzResearch.WordTrace]
  refine ⟨4564030165160946482423567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12170747107095857286462845 4564030165160946482423567)
  ·
    refine ⟨6846045247741419723635351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4564030165160946482423567 6846045247741419723635351)
    ·
      refine ⟨10269067871612129585453027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6846045247741419723635351 10269067871612129585453027)
      ·
        refine ⟨15403601807418194378179541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10269067871612129585453027 15403601807418194378179541)
        ·
          refine ⟨361021917361363930738583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 15403601807418194378179541 361021917361363930738583)
          ·
            refine ⟨541532876042045896107875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 361021917361363930738583 541532876042045896107875)
            ·
              refine ⟨812299314063068844161813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 541532876042045896107875 812299314063068844161813)
              ·
                refine ⟨38076530346706352070085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 812299314063068844161813 38076530346706352070085)
                ·
                  rfl

theorem cell21_500538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 7, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 7, 1, 1, 6].length) (baseStart_500538 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_500538 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_500538 prefixEnd_500538 := by exact prefixLift 500538
  have htrace : WordTrace (prefixWord ++ tailWord_500538) baseStart_500538 baseEnd_500538 := by
    simpa [prefixWord, tailWord_500538, baseEnd_500538] using wordTrace_append hprefix tailTrace_500538
  have hstable : (prefixWord ++ tailWord_500538).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_500538).length < 2 ^ (prefixWord ++ tailWord_500538).sum := by decide
  have hdescent : baseEnd_500538 < baseStart_500538 := by decide
  rcases family_descends (prefixWord ++ tailWord_500538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_500563 : List Nat := [1, 1, 1, 2, 1, 1, 3, 11]
def baseStart_500563 : Nat := 118140960795 + 500563 * 2 ^ 59
def prefixEnd_500563 : Nat := 4983230072969 + 3 ^ 40 * 500563 * 2
def baseEnd_500563 : Nat := 38078432126908189431179

theorem tailTrace_500563 : CollatzResearch.WordTrace tailWord_500563 prefixEnd_500563 38078432126908189431179 := by
  unfold tailWord_500563
  simp only [CollatzResearch.WordTrace]
  refine ⟨18257032485553215199354343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12171354990368810132902895 18257032485553215199354343)
  ·
    refine ⟨27385548728329822799031515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18257032485553215199354343 27385548728329822799031515)
    ·
      refine ⟨41078323092494734198547273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27385548728329822799031515 41078323092494734198547273)
      ·
        refine ⟨30808742319371050648910455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41078323092494734198547273 30808742319371050648910455)
        ·
          refine ⟨46213113479056575973365683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30808742319371050648910455 46213113479056575973365683)
          ·
            refine ⟨69319670218584863960048525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46213113479056575973365683 69319670218584863960048525)
            ·
              refine ⟨25994876331969323985018197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69319670218584863960048525 25994876331969323985018197)
              ·
                refine ⟨38078432126908189431179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 25994876331969323985018197 38078432126908189431179)
                ·
                  rfl

theorem cell21_500563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 11].length) (baseStart_500563 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_500563 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_500563 prefixEnd_500563 := by exact prefixLift 500563
  have htrace : WordTrace (prefixWord ++ tailWord_500563) baseStart_500563 baseEnd_500563 := by
    simpa [prefixWord, tailWord_500563, baseEnd_500563] using wordTrace_append hprefix tailTrace_500563
  have hstable : (prefixWord ++ tailWord_500563).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_500563).length < 2 ^ (prefixWord ++ tailWord_500563).sum := by decide
  have hdescent : baseEnd_500563 < baseStart_500563 := by decide
  rcases family_descends (prefixWord ++ tailWord_500563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_500580 : List Nat := [2, 3, 1, 1, 4, 2, 8]
def baseStart_500580 : Nat := 118140960795 + 500580 * 2 ^ 59
def prefixEnd_500580 : Nat := 4983230072969 + 3 ^ 40 * 500580 * 2
def baseEnd_500580 : Nat := 12693241779148479612241

theorem tailTrace_500580 : CollatzResearch.WordTrace tailWord_500580 prefixEnd_500580 12693241779148479612241 := by
  unfold tailWord_500580
  simp only [CollatzResearch.WordTrace]
  refine ⟨9128826263245813551361597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12171768350994418068482129 9128826263245813551361597)
  ·
    refine ⟨3423309848717180081760599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9128826263245813551361597 3423309848717180081760599)
    ·
      refine ⟨5134964773075770122640899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3423309848717180081760599 5134964773075770122640899)
      ·
        refine ⟨7702447159613655183961349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5134964773075770122640899 7702447159613655183961349)
        ·
          refine ⟨1444208842427560346992753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7702447159613655183961349 1444208842427560346992753)
          ·
            refine ⟨1083156631820670260244565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1444208842427560346992753 1083156631820670260244565)
            ·
              refine ⟨12693241779148479612241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1083156631820670260244565 12693241779148479612241)
              ·
                rfl

theorem cell21_500580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 8].length) (baseStart_500580 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_500580 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_500580 prefixEnd_500580 := by exact prefixLift 500580
  have htrace : WordTrace (prefixWord ++ tailWord_500580) baseStart_500580 baseEnd_500580 := by
    simpa [prefixWord, tailWord_500580, baseEnd_500580] using wordTrace_append hprefix tailTrace_500580
  have hstable : (prefixWord ++ tailWord_500580).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_500580).length < 2 ^ (prefixWord ++ tailWord_500580).sum := by decide
  have hdescent : baseEnd_500580 < baseStart_500580 := by decide
  rcases family_descends (prefixWord ++ tailWord_500580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_500583 : List Nat := [1, 1, 5, 1, 2, 4, 1, 2, 4]
def baseStart_500583 : Nat := 118140960795 + 500583 * 2 ^ 59
def prefixEnd_500583 : Nat := 4983230072969 + 3 ^ 40 * 500583 * 2
def baseEnd_500583 : Nat := 114239860653208977960163

theorem tailTrace_500583 : CollatzResearch.WordTrace tailWord_500583 prefixEnd_500583 114239860653208977960163 := by
  unfold tailWord_500583
  simp only [CollatzResearch.WordTrace]
  refine ⟨18257761945480758615082403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12171841296987172410054935 18257761945480758615082403)
  ·
    refine ⟨27386642918221137922623605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18257761945480758615082403 27386642918221137922623605)
    ·
      refine ⟨2567497773583231680245963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 27386642918221137922623605 2567497773583231680245963)
      ·
        refine ⟨3851246660374847520368945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2567497773583231680245963 3851246660374847520368945)
        ·
          refine ⟨2888434995281135640276709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3851246660374847520368945 2888434995281135640276709)
          ·
            refine ⟨541581561615212932551883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2888434995281135640276709 541581561615212932551883)
            ·
              refine ⟨812372342422819398827825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 541581561615212932551883 812372342422819398827825)
              ·
                refine ⟨609279256817114549120869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 812372342422819398827825 609279256817114549120869)
                ·
                  refine ⟨114239860653208977960163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 609279256817114549120869 114239860653208977960163)
                  ·
                    rfl

theorem cell21_500583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 4, 1, 2, 4].length) (baseStart_500583 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_500583 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_500583 prefixEnd_500583 := by exact prefixLift 500583
  have htrace : WordTrace (prefixWord ++ tailWord_500583) baseStart_500583 baseEnd_500583 := by
    simpa [prefixWord, tailWord_500583, baseEnd_500583] using wordTrace_append hprefix tailTrace_500583
  have hstable : (prefixWord ++ tailWord_500583).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_500583).length < 2 ^ (prefixWord ++ tailWord_500583).sum := by decide
  have hdescent : baseEnd_500583 < baseStart_500583 := by decide
  rcases family_descends (prefixWord ++ tailWord_500583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_500642 : List Nat := [3, 3, 1, 2, 2, 1, 2, 1, 6]
def baseStart_500642 : Nat := 118140960795 + 500642 * 2 ^ 59
def prefixEnd_500642 : Nat := 4983230072969 + 3 ^ 40 * 500642 * 2
def baseEnd_500642 : Nat := 114253325257037986476709

theorem tailTrace_500642 : CollatzResearch.WordTrace tailWord_500642 prefixEnd_500642 114253325257037986476709 := by
  unfold tailWord_500642
  simp only [CollatzResearch.WordTrace]
  refine ⟨4564978463066752922870045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12173275901511341127653453 4564978463066752922870045)
  ·
    refine ⟨1711866923650032346076267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4564978463066752922870045 1711866923650032346076267)
    ·
      refine ⟨2567800385475048519114401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1711866923650032346076267 2567800385475048519114401)
      ·
        refine ⟨1925850289106286389335801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2567800385475048519114401 1925850289106286389335801)
        ·
          refine ⟨1444387716829714792001851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1925850289106286389335801 1444387716829714792001851)
          ·
            refine ⟨2166581575244572188002777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1444387716829714792001851 2166581575244572188002777)
            ·
              refine ⟨1624936181433429141002083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2166581575244572188002777 1624936181433429141002083)
              ·
                refine ⟨2437404272150143711503125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1624936181433429141002083 2437404272150143711503125)
                ·
                  refine ⟨114253325257037986476709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2437404272150143711503125 114253325257037986476709)
                  ·
                    rfl

theorem cell21_500642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 2, 1, 6].length) (baseStart_500642 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_500642 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_500642 prefixEnd_500642 := by exact prefixLift 500642
  have htrace : WordTrace (prefixWord ++ tailWord_500642) baseStart_500642 baseEnd_500642 := by
    simpa [prefixWord, tailWord_500642, baseEnd_500642] using wordTrace_append hprefix tailTrace_500642
  have hstable : (prefixWord ++ tailWord_500642).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_500642).length < 2 ^ (prefixWord ++ tailWord_500642).sum := by decide
  have hdescent : baseEnd_500642 < baseStart_500642 := by decide
  rcases family_descends (prefixWord ++ tailWord_500642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_500797 : List Nat := [1, 4, 1, 3, 1, 4, 1, 3, 3]
def baseStart_500797 : Nat := 118140960795 + 500797 * 2 ^ 59
def prefixEnd_500797 : Nat := 4983230072969 + 3 ^ 40 * 500797 * 2
def baseEnd_500797 : Nat := 114288698368792161393059

theorem tailTrace_500797 : CollatzResearch.WordTrace tailWord_500797 prefixEnd_500797 114288698368792161393059 := by
  unfold tailWord_500797
  simp only [CollatzResearch.WordTrace]
  refine ⟨18265567166705473163372645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12177044777803648775581763 18265567166705473163372645)
  ·
    refine ⟨3424793843757276218132371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18265567166705473163372645 3424793843757276218132371)
    ·
      refine ⟨5137190765635914327198557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3424793843757276218132371 5137190765635914327198557)
      ·
        refine ⟨1926446537113467872699459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5137190765635914327198557 1926446537113467872699459)
        ·
          refine ⟨2889669805670201809049189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1926446537113467872699459 2889669805670201809049189)
          ·
            refine ⟨541813088563162839196723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2889669805670201809049189 541813088563162839196723)
            ·
              refine ⟨812719632844744258795085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 541813088563162839196723 812719632844744258795085)
              ·
                refine ⟨304769862316779097048157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 812719632844744258795085 304769862316779097048157)
                ·
                  refine ⟨114288698368792161393059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 304769862316779097048157 114288698368792161393059)
                  ·
                    rfl

theorem cell21_500797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 4, 1, 3, 3].length) (baseStart_500797 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_500797 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_500797 prefixEnd_500797 := by exact prefixLift 500797
  have htrace : WordTrace (prefixWord ++ tailWord_500797) baseStart_500797 baseEnd_500797 := by
    simpa [prefixWord, tailWord_500797, baseEnd_500797] using wordTrace_append hprefix tailTrace_500797
  have hstable : (prefixWord ++ tailWord_500797).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_500797).length < 2 ^ (prefixWord ++ tailWord_500797).sum := by decide
  have hdescent : baseEnd_500797 < baseStart_500797 := by decide
  rcases family_descends (prefixWord ++ tailWord_500797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_500873 : List Nat := [1, 2, 1, 1, 4, 5, 2, 2, 3]
def baseStart_500873 : Nat := 118140960795 + 500873 * 2 ^ 59
def prefixEnd_500873 : Nat := 4983230072969 + 3 ^ 40 * 500873 * 2
def baseEnd_500873 : Nat := 114306042604232918126237

theorem tailTrace_500873 : CollatzResearch.WordTrace tailWord_500873 prefixEnd_500873 114306042604232918126237 := by
  unfold tailWord_500873
  simp only [CollatzResearch.WordTrace]
  refine ⟨18268339114430138143139273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12178892742953425428759515 18268339114430138143139273)
  ·
    refine ⟨13701254335822603607354455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18268339114430138143139273 13701254335822603607354455)
    ·
      refine ⟨20551881503733905411031683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13701254335822603607354455 20551881503733905411031683)
      ·
        refine ⟨30827822255600858116547525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20551881503733905411031683 30827822255600858116547525)
        ·
          refine ⟨5780216672925160896852661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30827822255600858116547525 5780216672925160896852661)
          ·
            refine ⟨541895313086733834079937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5780216672925160896852661 541895313086733834079937)
            ·
              refine ⟨406421484815050375559953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 541895313086733834079937 406421484815050375559953)
              ·
                refine ⟨304816113611287781669965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 406421484815050375559953 304816113611287781669965)
                ·
                  refine ⟨114306042604232918126237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 304816113611287781669965 114306042604232918126237)
                  ·
                    rfl

theorem cell21_500873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 5, 2, 2, 3].length) (baseStart_500873 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_500873 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_500873 prefixEnd_500873 := by exact prefixLift 500873
  have htrace : WordTrace (prefixWord ++ tailWord_500873) baseStart_500873 baseEnd_500873 := by
    simpa [prefixWord, tailWord_500873, baseEnd_500873] using wordTrace_append hprefix tailTrace_500873
  have hstable : (prefixWord ++ tailWord_500873).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_500873).length < 2 ^ (prefixWord ++ tailWord_500873).sum := by decide
  have hdescent : baseEnd_500873 < baseStart_500873 := by decide
  rcases family_descends (prefixWord ++ tailWord_500873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_500912 : List Nat := [2, 1, 1, 1, 2, 1, 2, 3, 8]
def baseStart_500912 : Nat := 118140960795 + 500912 * 2 ^ 59
def prefixEnd_500912 : Nat := 4983230072969 + 3 ^ 40 * 500912 * 2
def baseEnd_500912 : Nat := 114314942935577516976157

theorem tailTrace_500912 : CollatzResearch.WordTrace tailWord_500912 prefixEnd_500912 114314942935577516976157 := by
  unfold tailWord_500912
  simp only [CollatzResearch.WordTrace]
  refine ⟨9134880780644423901904495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12179841040859231869205993 9134880780644423901904495)
  ·
    refine ⟨13702321170966635852856743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9134880780644423901904495 13702321170966635852856743)
    ·
      refine ⟨20553481756449953779285115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13702321170966635852856743 20553481756449953779285115)
      ·
        refine ⟨30830222634674930668927673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20553481756449953779285115 30830222634674930668927673)
        ·
          refine ⟨23122666976006198001695755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30830222634674930668927673 23122666976006198001695755)
          ·
            refine ⟨34684000464009297002543633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23122666976006198001695755 34684000464009297002543633)
            ·
              refine ⟨26013000348006972751907725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34684000464009297002543633 26013000348006972751907725)
              ·
                refine ⟨9754875130502614781965397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26013000348006972751907725 9754875130502614781965397)
                ·
                  refine ⟨114314942935577516976157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 9754875130502614781965397 114314942935577516976157)
                  ·
                    rfl

theorem cell21_500912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 3, 8].length) (baseStart_500912 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_500912 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_500912 prefixEnd_500912 := by exact prefixLift 500912
  have htrace : WordTrace (prefixWord ++ tailWord_500912) baseStart_500912 baseEnd_500912 := by
    simpa [prefixWord, tailWord_500912, baseEnd_500912] using wordTrace_append hprefix tailTrace_500912
  have hstable : (prefixWord ++ tailWord_500912).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_500912).length < 2 ^ (prefixWord ++ tailWord_500912).sum := by decide
  have hdescent : baseEnd_500912 < baseStart_500912 := by decide
  rcases family_descends (prefixWord ++ tailWord_500912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_500915 : List Nat := [1, 1, 1, 2, 3, 2, 3, 5, 3]
def baseStart_500915 : Nat := 118140960795 + 500915 * 2 ^ 59
def prefixEnd_500915 : Nat := 4983230072969 + 3 ^ 40 * 500915 * 2
def baseEnd_500915 : Nat := 114315627576450178426151

theorem tailTrace_500915 : CollatzResearch.WordTrace tailWord_500915 prefixEnd_500915 114315627576450178426151 := by
  unfold tailWord_500915
  simp only [CollatzResearch.WordTrace]
  refine ⟨18269870980277979316168199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12179913986851986210778799 18269870980277979316168199)
  ·
    refine ⟨27404806470416968974252299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18269870980277979316168199 27404806470416968974252299)
    ·
      refine ⟨41107209705625453461378449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27404806470416968974252299 41107209705625453461378449)
      ·
        refine ⟨30830407279219090096033837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41107209705625453461378449 30830407279219090096033837)
        ·
          refine ⟨11561402729707158786012689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30830407279219090096033837 11561402729707158786012689)
          ·
            refine ⟨8671052047280369089509517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11561402729707158786012689 8671052047280369089509517)
            ·
              refine ⟨3251644517730138408566069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8671052047280369089509517 3251644517730138408566069)
              ·
                refine ⟨304841673537200475803069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3251644517730138408566069 304841673537200475803069)
                ·
                  refine ⟨114315627576450178426151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 304841673537200475803069 114315627576450178426151)
                  ·
                    rfl

theorem cell21_500915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 3, 5, 3].length) (baseStart_500915 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_500915 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_500915 prefixEnd_500915 := by exact prefixLift 500915
  have htrace : WordTrace (prefixWord ++ tailWord_500915) baseStart_500915 baseEnd_500915 := by
    simpa [prefixWord, tailWord_500915, baseEnd_500915] using wordTrace_append hprefix tailTrace_500915
  have hstable : (prefixWord ++ tailWord_500915).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_500915).length < 2 ^ (prefixWord ++ tailWord_500915).sum := by decide
  have hdescent : baseEnd_500915 < baseStart_500915 := by decide
  rcases family_descends (prefixWord ++ tailWord_500915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_500918 : List Nat := [5, 1, 3, 2, 1, 1, 8]
def baseStart_500918 : Nat := 118140960795 + 500918 * 2 ^ 59
def prefixEnd_500918 : Nat := 4983230072969 + 3 ^ 40 * 500918 * 2
def baseEnd_500918 : Nat := 12701812468591426652905

theorem tailTrace_500918 : CollatzResearch.WordTrace tailWord_500918 prefixEnd_500918 12701812468591426652905 := by
  unfold tailWord_500918
  simp only [CollatzResearch.WordTrace]
  refine ⟨1141873774954194426782963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 12179986932844740552351605 1141873774954194426782963)
  ·
    refine ⟨1712810662431291640174445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1141873774954194426782963 1712810662431291640174445)
    ·
      refine ⟨642303998411734365065417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1712810662431291640174445 642303998411734365065417)
      ·
        refine ⟨481727998808800773799063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 642303998411734365065417 481727998808800773799063)
        ·
          refine ⟨722591998213201160698595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 481727998808800773799063 722591998213201160698595)
          ·
            refine ⟨1083887997319801741047893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 722591998213201160698595 1083887997319801741047893)
            ·
              refine ⟨12701812468591426652905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1083887997319801741047893 12701812468591426652905)
              ·
                rfl

theorem cell21_500918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 8].length) (baseStart_500918 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_500918 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_500918 prefixEnd_500918 := by exact prefixLift 500918
  have htrace : WordTrace (prefixWord ++ tailWord_500918) baseStart_500918 baseEnd_500918 := by
    simpa [prefixWord, tailWord_500918, baseEnd_500918] using wordTrace_append hprefix tailTrace_500918
  have hstable : (prefixWord ++ tailWord_500918).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_500918).length < 2 ^ (prefixWord ++ tailWord_500918).sum := by decide
  have hdescent : baseEnd_500918 < baseStart_500918 := by decide
  rcases family_descends (prefixWord ++ tailWord_500918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_500932 : List Nat := [2, 3, 3, 1, 3, 1, 2, 1, 5]
def baseStart_500932 : Nat := 118140960795 + 500932 * 2 ^ 59
def prefixEnd_500932 : Nat := 4983230072969 + 3 ^ 40 * 500932 * 2
def baseEnd_500932 : Nat := 114319507208061926642783

theorem tailTrace_500932 : CollatzResearch.WordTrace tailWord_500932 prefixEnd_500932 114319507208061926642783 := by
  unfold tailWord_500932
  simp only [CollatzResearch.WordTrace]
  refine ⟨9135245510608195609768525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12180327347477594146358033 9135245510608195609768525)
  ·
    refine ⟨3425717066478073353663197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9135245510608195609768525 3425717066478073353663197)
    ·
      refine ⟨1284643899929277507623699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3425717066478073353663197 1284643899929277507623699)
      ·
        refine ⟨1926965849893916261435549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1284643899929277507623699 1926965849893916261435549)
        ·
          refine ⟨722612193710218598038331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1926965849893916261435549 722612193710218598038331)
          ·
            refine ⟨1083918290565327897057497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 722612193710218598038331 1083918290565327897057497)
            ·
              refine ⟨812938717923995922793123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1083918290565327897057497 812938717923995922793123)
              ·
                refine ⟨1219408076885993884189685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 812938717923995922793123 1219408076885993884189685)
                ·
                  refine ⟨114319507208061926642783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1219408076885993884189685 114319507208061926642783)
                  ·
                    rfl

theorem cell21_500932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 2, 1, 5].length) (baseStart_500932 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_500932 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_500932 prefixEnd_500932 := by exact prefixLift 500932
  have htrace : WordTrace (prefixWord ++ tailWord_500932) baseStart_500932 baseEnd_500932 := by
    simpa [prefixWord, tailWord_500932, baseEnd_500932] using wordTrace_append hprefix tailTrace_500932
  have hstable : (prefixWord ++ tailWord_500932).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_500932).length < 2 ^ (prefixWord ++ tailWord_500932).sum := by decide
  have hdescent : baseEnd_500932 < baseStart_500932 := by decide
  rcases family_descends (prefixWord ++ tailWord_500932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_500960 : List Nat := [2, 1, 1, 3, 1, 4, 4, 5]
def baseStart_500960 : Nat := 118140960795 + 500960 * 2 ^ 59
def prefixEnd_500960 : Nat := 4983230072969 + 3 ^ 40 * 500960 * 2
def baseEnd_500960 : Nat := 38108632396513366725353

theorem tailTrace_500960 : CollatzResearch.WordTrace tailWord_500960 prefixEnd_500960 38108632396513366725353 := by
  unfold tailWord_500960
  simp only [CollatzResearch.WordTrace]
  refine ⟨9135756132557476000778167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12181008176743301334370889 9135756132557476000778167)
  ·
    refine ⟨13703634198836214001167251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9135756132557476000778167 13703634198836214001167251)
    ·
      refine ⟨20555451298254321001750877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13703634198836214001167251 20555451298254321001750877)
      ·
        refine ⟨7708294236845370375656579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20555451298254321001750877 7708294236845370375656579)
        ·
          refine ⟨11562441355268055563484869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7708294236845370375656579 11562441355268055563484869)
          ·
            refine ⟨2167957754112760418153413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11562441355268055563484869 2167957754112760418153413)
            ·
              refine ⟨406492078896142578403765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2167957754112760418153413 406492078896142578403765)
              ·
                refine ⟨38108632396513366725353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 406492078896142578403765 38108632396513366725353)
                ·
                  rfl

theorem cell21_500960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 4, 5].length) (baseStart_500960 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_500960 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_500960 prefixEnd_500960 := by exact prefixLift 500960
  have htrace : WordTrace (prefixWord ++ tailWord_500960) baseStart_500960 baseEnd_500960 := by
    simpa [prefixWord, tailWord_500960, baseEnd_500960] using wordTrace_append hprefix tailTrace_500960
  have hstable : (prefixWord ++ tailWord_500960).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_500960).length < 2 ^ (prefixWord ++ tailWord_500960).sum := by decide
  have hdescent : baseEnd_500960 < baseStart_500960 := by decide
  rcases family_descends (prefixWord ++ tailWord_500960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_500974 : List Nat := [4, 1, 2, 1, 1, 1, 2, 2, 7]
def baseStart_500974 : Nat := 118140960795 + 500974 * 2 ^ 59
def prefixEnd_500974 : Nat := 4983230072969 + 3 ^ 40 * 500974 * 2
def baseEnd_500974 : Nat := 114329092180279186942697

theorem tailTrace_500974 : CollatzResearch.WordTrace tailWord_500974 prefixEnd_500974 114329092180279186942697 := by
  unfold tailWord_500974
  simp only [CollatzResearch.WordTrace]
  refine ⟨2284002860883029049070747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12181348591376154928377317 2284002860883029049070747)
  ·
    refine ⟨3426004291324543573606121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2284002860883029049070747 3426004291324543573606121)
    ·
      refine ⟨2569503218493407680204591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3426004291324543573606121 2569503218493407680204591)
      ·
        refine ⟨3854254827740111520306887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2569503218493407680204591 3854254827740111520306887)
        ·
          refine ⟨5781382241610167280460331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3854254827740111520306887 5781382241610167280460331)
          ·
            refine ⟨8672073362415250920690497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5781382241610167280460331 8672073362415250920690497)
            ·
              refine ⟨6504055021811438190517873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8672073362415250920690497 6504055021811438190517873)
              ·
                refine ⟨4878041266358578642888405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6504055021811438190517873 4878041266358578642888405)
                ·
                  refine ⟨114329092180279186942697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4878041266358578642888405 114329092180279186942697)
                  ·
                    rfl

theorem cell21_500974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 2, 7].length) (baseStart_500974 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_500974 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_500974 prefixEnd_500974 := by exact prefixLift 500974
  have htrace : WordTrace (prefixWord ++ tailWord_500974) baseStart_500974 baseEnd_500974 := by
    simpa [prefixWord, tailWord_500974, baseEnd_500974] using wordTrace_append hprefix tailTrace_500974
  have hstable : (prefixWord ++ tailWord_500974).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_500974).length < 2 ^ (prefixWord ++ tailWord_500974).sum := by decide
  have hdescent : baseEnd_500974 < baseStart_500974 := by decide
  rcases family_descends (prefixWord ++ tailWord_500974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_500991 : List Nat := [1, 1, 2, 2, 1, 7, 1, 1, 5]
def baseStart_500991 : Nat := 118140960795 + 500991 * 2 ^ 59
def prefixEnd_500991 : Nat := 4983230072969 + 3 ^ 40 * 500991 * 2
def baseEnd_500991 : Nat := 114332971811890935159329

theorem tailTrace_500991 : CollatzResearch.WordTrace tailWord_500991 prefixEnd_500991 114332971811890935159329 := by
  unfold tailWord_500991
  simp only [CollatzResearch.WordTrace]
  refine ⟨18272642928002644295934827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12181761952001762863956551 18272642928002644295934827)
  ·
    refine ⟨27408964392003966443902241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18272642928002644295934827 27408964392003966443902241)
    ·
      refine ⟨20556723294002974832926681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27408964392003966443902241 20556723294002974832926681)
      ·
        refine ⟨15417542470502231124695011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20556723294002974832926681 15417542470502231124695011)
        ·
          refine ⟨23126313705753346687042517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15417542470502231124695011 23126313705753346687042517)
          ·
            refine ⟨542022977478594062977559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 23126313705753346687042517 542022977478594062977559)
            ·
              refine ⟨813034466217891094466339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 542022977478594062977559 813034466217891094466339)
              ·
                refine ⟨1219551699326836641699509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 813034466217891094466339 1219551699326836641699509)
                ·
                  refine ⟨114332971811890935159329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1219551699326836641699509 114332971811890935159329)
                  ·
                    rfl

theorem cell21_500991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 7, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 7, 1, 1, 5].length) (baseStart_500991 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_500991 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_500991 prefixEnd_500991 := by exact prefixLift 500991
  have htrace : WordTrace (prefixWord ++ tailWord_500991) baseStart_500991 baseEnd_500991 := by
    simpa [prefixWord, tailWord_500991, baseEnd_500991] using wordTrace_append hprefix tailTrace_500991
  have hstable : (prefixWord ++ tailWord_500991).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_500991).length < 2 ^ (prefixWord ++ tailWord_500991).sum := by decide
  have hdescent : baseEnd_500991 < baseStart_500991 := by decide
  rcases family_descends (prefixWord ++ tailWord_500991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_501050 : List Nat := [3, 1, 1, 1, 4, 1, 2, 3, 5]
def baseStart_501050 : Nat := 118140960795 + 501050 * 2 ^ 59
def prefixEnd_501050 : Nat := 4983230072969 + 3 ^ 40 * 501050 * 2
def baseEnd_501050 : Nat := 114346436415719943675875

theorem tailTrace_501050 : CollatzResearch.WordTrace tailWord_501050 prefixEnd_501050 114346436415719943675875 := by
  unfold tailWord_501050
  simp only [CollatzResearch.WordTrace]
  refine ⟨4568698708697224343083151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12183196556525931581555069 4568698708697224343083151)
  ·
    refine ⟨6853048063045836514624727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4568698708697224343083151 6853048063045836514624727)
    ·
      refine ⟨10279572094568754771937091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6853048063045836514624727 10279572094568754771937091)
      ·
        refine ⟨15419358141853132157905637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10279572094568754771937091 15419358141853132157905637)
        ·
          refine ⟨2891129651597462279607307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15419358141853132157905637 2891129651597462279607307)
          ·
            refine ⟨4336694477396193419410961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2891129651597462279607307 4336694477396193419410961)
            ·
              refine ⟨3252520858047145064558221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4336694477396193419410961 3252520858047145064558221)
              ·
                refine ⟨1219695321767679399209333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3252520858047145064558221 1219695321767679399209333)
                ·
                  refine ⟨114346436415719943675875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1219695321767679399209333 114346436415719943675875)
                  ·
                    rfl

theorem cell21_501050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 2, 3, 5].length) (baseStart_501050 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_501050 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_501050 prefixEnd_501050 := by exact prefixLift 501050
  have htrace : WordTrace (prefixWord ++ tailWord_501050) baseStart_501050 baseEnd_501050 := by
    simpa [prefixWord, tailWord_501050, baseEnd_501050] using wordTrace_append hprefix tailTrace_501050
  have hstable : (prefixWord ++ tailWord_501050).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_501050).length < 2 ^ (prefixWord ++ tailWord_501050).sum := by decide
  have hdescent : baseEnd_501050 < baseStart_501050 := by decide
  rcases family_descends (prefixWord ++ tailWord_501050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_501064 : List Nat := [2, 1, 3, 1, 1, 2, 1, 2, 8]
def baseStart_501064 : Nat := 118140960795 + 501064 * 2 ^ 59
def prefixEnd_501064 : Nat := 4983230072969 + 3 ^ 40 * 501064 * 2
def baseEnd_501064 : Nat := 114349631406459030442513

theorem tailTrace_501064 : CollatzResearch.WordTrace tailWord_501064 prefixEnd_501064 114349631406459030442513 := by
  unfold tailWord_501064
  simp only [CollatzResearch.WordTrace]
  refine ⟨9137652728369088881671123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12183536971158785175561497 9137652728369088881671123)
  ·
    refine ⟨13706479092553633322506685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9137652728369088881671123 13706479092553633322506685)
    ·
      refine ⟨5139929659707612495940007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13706479092553633322506685 5139929659707612495940007)
      ·
        refine ⟨7709894489561418743910011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5139929659707612495940007 7709894489561418743910011)
        ·
          refine ⟨11564841734342128115865017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7709894489561418743910011 11564841734342128115865017)
          ·
            refine ⟨8673631300756596086898763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11564841734342128115865017 8673631300756596086898763)
            ·
              refine ⟨13010446951134894130348145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8673631300756596086898763 13010446951134894130348145)
              ·
                refine ⟨9757835213351170597761109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13010446951134894130348145 9757835213351170597761109)
                ·
                  refine ⟨114349631406459030442513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 9757835213351170597761109 114349631406459030442513)
                  ·
                    rfl

theorem cell21_501064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 2, 8].length) (baseStart_501064 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_501064 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_501064 prefixEnd_501064 := by exact prefixLift 501064
  have htrace : WordTrace (prefixWord ++ tailWord_501064) baseStart_501064 baseEnd_501064 := by
    simpa [prefixWord, tailWord_501064, baseEnd_501064] using wordTrace_append hprefix tailTrace_501064
  have hstable : (prefixWord ++ tailWord_501064).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_501064).length < 2 ^ (prefixWord ++ tailWord_501064).sum := by decide
  have hdescent : baseEnd_501064 < baseStart_501064 := by decide
  rcases family_descends (prefixWord ++ tailWord_501064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_501098 : List Nat := [3, 1, 3, 3, 2, 1, 1, 1, 6]
def baseStart_501098 : Nat := 118140960795 + 501098 * 2 ^ 59
def prefixEnd_501098 : Nat := 4983230072969 + 3 ^ 40 * 501098 * 2
def baseEnd_501098 : Nat := 114357390669682526875777

theorem tailTrace_501098 : CollatzResearch.WordTrace tailWord_501098 prefixEnd_501098 114357390669682526875777 := by
  unfold tailWord_501098
  simp only [CollatzResearch.WordTrace]
  refine ⟨4569136384653750392519987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12184363692410001046719965 4569136384653750392519987)
  ·
    refine ⟨6853704576980625588779981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4569136384653750392519987 6853704576980625588779981)
    ·
      refine ⟨2570139216367734595792493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6853704576980625588779981 2570139216367734595792493)
      ·
        refine ⟨963802206137900473422185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2570139216367734595792493 963802206137900473422185)
        ·
          refine ⟨722851654603425355066639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 963802206137900473422185 722851654603425355066639)
          ·
            refine ⟨1084277481905138032599959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 722851654603425355066639 1084277481905138032599959)
            ·
              refine ⟨1626416222857707048899939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1084277481905138032599959 1626416222857707048899939)
              ·
                refine ⟨2439624334286560573349909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1626416222857707048899939 2439624334286560573349909)
                ·
                  refine ⟨114357390669682526875777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2439624334286560573349909 114357390669682526875777)
                  ·
                    rfl

theorem cell21_501098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 1, 1, 6].length) (baseStart_501098 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_501098 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_501098 prefixEnd_501098 := by exact prefixLift 501098
  have htrace : WordTrace (prefixWord ++ tailWord_501098) baseStart_501098 baseEnd_501098 := by
    simpa [prefixWord, tailWord_501098, baseEnd_501098] using wordTrace_append hprefix tailTrace_501098
  have hstable : (prefixWord ++ tailWord_501098).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_501098).length < 2 ^ (prefixWord ++ tailWord_501098).sum := by decide
  have hdescent : baseEnd_501098 < baseStart_501098 := by decide
  rcases family_descends (prefixWord ++ tailWord_501098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_501129 : List Nat := [1, 2, 1, 1, 7, 2, 2, 5]
def baseStart_501129 : Nat := 118140960795 + 501129 * 2 ^ 59
def prefixEnd_501129 : Nat := 4983230072969 + 3 ^ 40 * 501129 * 2
def baseEnd_501129 : Nat := 38121488430677787286349

theorem tailTrace_501129 : CollatzResearch.WordTrace tailWord_501129 prefixEnd_501129 38121488430677787286349 := by
  unfold tailWord_501129
  simp only [CollatzResearch.WordTrace]
  refine ⟨18277676201502693864458441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12185117467668462576305627 18277676201502693864458441)
  ·
    refine ⟨13708257151127020398343831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18277676201502693864458441 13708257151127020398343831)
    ·
      refine ⟨20562385726690530597515747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13708257151127020398343831 20562385726690530597515747)
      ·
        refine ⟨30843578590035795896273621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20562385726690530597515747 30843578590035795896273621)
        ·
          refine ⟨722896373203963966318913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 30843578590035795896273621 722896373203963966318913)
          ·
            refine ⟨542172279902972974739185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 722896373203963966318913 542172279902972974739185)
            ·
              refine ⟨406629209927229731054389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 542172279902972974739185 406629209927229731054389)
              ·
                refine ⟨38121488430677787286349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 406629209927229731054389 38121488430677787286349)
                ·
                  rfl

theorem cell21_501129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 2, 2, 5].length) (baseStart_501129 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_501129 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_501129 prefixEnd_501129 := by exact prefixLift 501129
  have htrace : WordTrace (prefixWord ++ tailWord_501129) baseStart_501129 baseEnd_501129 := by
    simpa [prefixWord, tailWord_501129, baseEnd_501129] using wordTrace_append hprefix tailTrace_501129
  have hstable : (prefixWord ++ tailWord_501129).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_501129).length < 2 ^ (prefixWord ++ tailWord_501129).sum := by decide
  have hdescent : baseEnd_501129 < baseStart_501129 := by decide
  rcases family_descends (prefixWord ++ tailWord_501129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_501188 : List Nat := [2, 3, 3, 2, 1, 1, 2, 7]
def baseStart_501188 : Nat := 118140960795 + 501188 * 2 ^ 59
def prefixEnd_501188 : Nat := 4983230072969 + 3 ^ 40 * 501188 * 2
def baseEnd_501188 : Nat := 38125976631954123458531

theorem tailTrace_501188 : CollatzResearch.WordTrace tailWord_501188 prefixEnd_501188 38125976631954123458531 := by
  unfold tailWord_501188
  simp only [CollatzResearch.WordTrace]
  refine ⟨9139914054144473470428109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12186552072192631293904145 9139914054144473470428109)
  ·
    refine ⟨3427467770304177551410541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9139914054144473470428109 3427467770304177551410541)
    ·
      refine ⟨1285300413864066581778953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3427467770304177551410541 1285300413864066581778953)
      ·
        refine ⟨963975310398049936334215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1285300413864066581778953 963975310398049936334215)
        ·
          refine ⟨1445962965597074904501323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 963975310398049936334215 1445962965597074904501323)
          ·
            refine ⟨2168944448395612356751985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1445962965597074904501323 2168944448395612356751985)
            ·
              refine ⟨1626708336296709267563989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2168944448395612356751985 1626708336296709267563989)
              ·
                refine ⟨38125976631954123458531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1626708336296709267563989 38125976631954123458531)
                ·
                  rfl

theorem cell21_501188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 2, 7].length) (baseStart_501188 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_501188 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_501188 prefixEnd_501188 := by exact prefixLift 501188
  have htrace : WordTrace (prefixWord ++ tailWord_501188) baseStart_501188 baseEnd_501188 := by
    simpa [prefixWord, tailWord_501188, baseEnd_501188] using wordTrace_append hprefix tailTrace_501188
  have hstable : (prefixWord ++ tailWord_501188).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_501188).length < 2 ^ (prefixWord ++ tailWord_501188).sum := by decide
  have hdescent : baseEnd_501188 < baseStart_501188 := by decide
  rcases family_descends (prefixWord ++ tailWord_501188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_501233 : List Nat := [1, 2, 2, 2, 3, 2, 2, 3, 4]
def baseStart_501233 : Nat := 118140960795 + 501233 * 2 ^ 59
def prefixEnd_501233 : Nat := 4983230072969 + 3 ^ 40 * 501233 * 2
def baseEnd_501233 : Nat := 114388199508952292125501

theorem tailTrace_501233 : CollatzResearch.WordTrace tailWord_501233 prefixEnd_501233 114388199508952292125501 := by
  unfold tailWord_501233
  simp only [CollatzResearch.WordTrace]
  refine ⟨18281469393125919626244353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12187646262083946417496235 18281469393125919626244353)
  ·
    refine ⟨13711102044844439719683265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18281469393125919626244353 13711102044844439719683265)
    ·
      refine ⟨10283326533633329789762449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13711102044844439719683265 10283326533633329789762449)
      ·
        refine ⟨7712494900224997342321837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10283326533633329789762449 7712494900224997342321837)
        ·
          refine ⟨2892185587584374003370689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7712494900224997342321837 2892185587584374003370689)
          ·
            refine ⟨2169139190688280502528017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2892185587584374003370689 2169139190688280502528017)
            ·
              refine ⟨1626854393016210376896013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2169139190688280502528017 1626854393016210376896013)
              ·
                refine ⟨610070397381078891336005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1626854393016210376896013 610070397381078891336005)
                ·
                  refine ⟨114388199508952292125501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 610070397381078891336005 114388199508952292125501)
                  ·
                    rfl

theorem cell21_501233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 2, 3, 4].length) (baseStart_501233 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_501233 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_501233 prefixEnd_501233 := by exact prefixLift 501233
  have htrace : WordTrace (prefixWord ++ tailWord_501233) baseStart_501233 baseEnd_501233 := by
    simpa [prefixWord, tailWord_501233, baseEnd_501233] using wordTrace_append hprefix tailTrace_501233
  have hstable : (prefixWord ++ tailWord_501233).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_501233).length < 2 ^ (prefixWord ++ tailWord_501233).sum := by decide
  have hdescent : baseEnd_501233 < baseStart_501233 := by decide
  rcases family_descends (prefixWord ++ tailWord_501233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_501340 : List Nat := [2, 2, 4, 1, 2, 2, 2, 6]
def baseStart_501340 : Nat := 118140960795 + 501340 * 2 ^ 59
def prefixEnd_501340 : Nat := 4983230072969 + 3 ^ 40 * 501340 * 2
def baseEnd_501340 : Nat := 38137539455581294613983

theorem tailTrace_501340 : CollatzResearch.WordTrace tailWord_501340 prefixEnd_501340 38137539455581294613983 := by
  unfold tailWord_501340
  simp only [CollatzResearch.WordTrace]
  refine ⟨9142686001869138450194737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12190248002492184600259649 9142686001869138450194737)
  ·
    refine ⟨6857014501401853837646053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9142686001869138450194737 6857014501401853837646053)
    ·
      refine ⟨1285690219012847594558635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6857014501401853837646053 1285690219012847594558635)
      ·
        refine ⟨1928535328519271391837953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1285690219012847594558635 1928535328519271391837953)
        ·
          refine ⟨1446401496389453543878465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1928535328519271391837953 1446401496389453543878465)
          ·
            refine ⟨1084801122292090157908849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1446401496389453543878465 1084801122292090157908849)
            ·
              refine ⟨813600841719067618431637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1084801122292090157908849 813600841719067618431637)
              ·
                refine ⟨38137539455581294613983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 813600841719067618431637 38137539455581294613983)
                ·
                  rfl

theorem cell21_501340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 2, 6].length) (baseStart_501340 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_501340 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_501340 prefixEnd_501340 := by exact prefixLift 501340
  have htrace : WordTrace (prefixWord ++ tailWord_501340) baseStart_501340 baseEnd_501340 := by
    simpa [prefixWord, tailWord_501340, baseEnd_501340] using wordTrace_append hprefix tailTrace_501340
  have hstable : (prefixWord ++ tailWord_501340).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_501340).length < 2 ^ (prefixWord ++ tailWord_501340).sum := by decide
  have hdescent : baseEnd_501340 < baseStart_501340 := by decide
  rcases family_descends (prefixWord ++ tailWord_501340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_501399 : List Nat := [1, 1, 3, 3, 2, 2, 3, 6]
def baseStart_501399 : Nat := 118140960795 + 501399 * 2 ^ 59
def prefixEnd_501399 : Nat := 4983230072969 + 3 ^ 40 * 501399 * 2
def baseEnd_501399 : Nat := 38142027656857630786165

theorem tailTrace_501399 : CollatzResearch.WordTrace tailWord_501399 prefixEnd_501399 38142027656857630786165 := by
  unfold tailWord_501399
  simp only [CollatzResearch.WordTrace]
  refine ⟨18287523910524529976787251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12191682607016353317858167 18287523910524529976787251)
  ·
    refine ⟨27431285865786794965180877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18287523910524529976787251 27431285865786794965180877)
    ·
      refine ⟨10286732199670048111942829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27431285865786794965180877 10286732199670048111942829)
      ·
        refine ⟨3857524574876268041978561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10286732199670048111942829 3857524574876268041978561)
        ·
          refine ⟨2893143431157201031483921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3857524574876268041978561 2893143431157201031483921)
          ·
            refine ⟨2169857573367900773612941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2893143431157201031483921 2169857573367900773612941)
            ·
              refine ⟨813696590012962790104853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2169857573367900773612941 813696590012962790104853)
              ·
                refine ⟨38142027656857630786165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 813696590012962790104853 38142027656857630786165)
                ·
                  rfl

theorem cell21_501399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 3, 6].length) (baseStart_501399 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_501399 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_501399 prefixEnd_501399 := by exact prefixLift 501399
  have htrace : WordTrace (prefixWord ++ tailWord_501399) baseStart_501399 baseEnd_501399 := by
    simpa [prefixWord, tailWord_501399, baseEnd_501399] using wordTrace_append hprefix tailTrace_501399
  have hstable : (prefixWord ++ tailWord_501399).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_501399).length < 2 ^ (prefixWord ++ tailWord_501399).sum := by decide
  have hdescent : baseEnd_501399 < baseStart_501399 := by decide
  rcases family_descends (prefixWord ++ tailWord_501399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_501413 : List Nat := [1, 3, 1, 2, 1, 2, 3, 1, 7]
def baseStart_501413 : Nat := 118140960795 + 501413 * 2 ^ 59
def prefixEnd_501413 : Nat := 4983230072969 + 3 ^ 40 * 501413 * 2
def baseEnd_501413 : Nat := 114429277961311979125133

theorem tailTrace_501413 : CollatzResearch.WordTrace tailWord_501413 prefixEnd_501413 114429277961311979125133 := by
  unfold tailWord_501413
  simp only [CollatzResearch.WordTrace]
  refine ⟨18288034532473810367796893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12192023021649206911864595 18288034532473810367796893)
  ·
    refine ⟨6858012949677678887923835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18288034532473810367796893 6858012949677678887923835)
    ·
      refine ⟨10287019424516518331885753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6858012949677678887923835 10287019424516518331885753)
      ·
        refine ⟨7715264568387388748914315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10287019424516518331885753 7715264568387388748914315)
        ·
          refine ⟨11572896852581083123371473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7715264568387388748914315 11572896852581083123371473)
          ·
            refine ⟨8679672639435812342528605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11572896852581083123371473 8679672639435812342528605)
            ·
              refine ⟨3254877239788429628448227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8679672639435812342528605 3254877239788429628448227)
              ·
                refine ⟨4882315859682644442672341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3254877239788429628448227 4882315859682644442672341)
                ·
                  refine ⟨114429277961311979125133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4882315859682644442672341 114429277961311979125133)
                  ·
                    rfl

theorem cell21_501413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 3, 1, 7].length) (baseStart_501413 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_501413 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_501413 prefixEnd_501413 := by exact prefixLift 501413
  have htrace : WordTrace (prefixWord ++ tailWord_501413) baseStart_501413 baseEnd_501413 := by
    simpa [prefixWord, tailWord_501413, baseEnd_501413] using wordTrace_append hprefix tailTrace_501413
  have hstable : (prefixWord ++ tailWord_501413).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_501413).length < 2 ^ (prefixWord ++ tailWord_501413).sum := by decide
  have hdescent : baseEnd_501413 < baseStart_501413 := by decide
  rcases family_descends (prefixWord ++ tailWord_501413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_501557 : List Nat := [1, 3, 3, 1, 4, 2, 2, 2, 3]
def baseStart_501557 : Nat := 118140960795 + 501557 * 2 ^ 59
def prefixEnd_501557 : Nat := 4983230072969 + 3 ^ 40 * 501557 * 2
def baseEnd_501557 : Nat := 114462140723199728724839

theorem tailTrace_501557 : CollatzResearch.WordTrace tailWord_501557 prefixEnd_501557 114462140723199728724839 := by
  unfold tailWord_501557
  simp only [CollatzResearch.WordTrace]
  refine ⟨18293286643952122961038925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12195524429301415307359283 18293286643952122961038925)
  ·
    refine ⟨6859982491482046110389597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18293286643952122961038925 6859982491482046110389597)
    ·
      refine ⟨2572493434305767291396099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6859982491482046110389597 2572493434305767291396099)
      ·
        refine ⟨3858740151458650937094149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2572493434305767291396099 3858740151458650937094149)
        ·
          refine ⟨723513778398497050705153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3858740151458650937094149 723513778398497050705153)
          ·
            refine ⟨542635333798872788028865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 723513778398497050705153 542635333798872788028865)
            ·
              refine ⟨406976500349154591021649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 542635333798872788028865 406976500349154591021649)
              ·
                refine ⟨305232375261865943266237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 406976500349154591021649 305232375261865943266237)
                ·
                  refine ⟨114462140723199728724839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 305232375261865943266237 114462140723199728724839)
                  ·
                    rfl

theorem cell21_501557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 2, 2, 2, 3].length) (baseStart_501557 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_501557 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_501557 prefixEnd_501557 := by exact prefixLift 501557
  have htrace : WordTrace (prefixWord ++ tailWord_501557) baseStart_501557 baseEnd_501557 := by
    simpa [prefixWord, tailWord_501557, baseEnd_501557] using wordTrace_append hprefix tailTrace_501557
  have hstable : (prefixWord ++ tailWord_501557).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_501557).length < 2 ^ (prefixWord ++ tailWord_501557).sum := by decide
  have hdescent : baseEnd_501557 < baseStart_501557 := by decide
  rcases family_descends (prefixWord ++ tailWord_501557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_501599 : List Nat := [1, 1, 2, 3, 1, 5, 2, 3, 3]
def baseStart_501599 : Nat := 118140960795 + 501599 * 2 ^ 59
def prefixEnd_501599 : Nat := 4983230072969 + 3 ^ 40 * 501599 * 2
def baseEnd_501599 : Nat := 114471725695416989024753

theorem tailTrace_501599 : CollatzResearch.WordTrace tailWord_501599 prefixEnd_501599 114471725695416989024753 := by
  unfold tailWord_501599
  simp only [CollatzResearch.WordTrace]
  refine ⟨18294818509799964134067851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12196545673199976089378567 18294818509799964134067851)
  ·
    refine ⟨27442227764699946201101777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18294818509799964134067851 27442227764699946201101777)
    ·
      refine ⟨20581670823524959650826333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27442227764699946201101777 20581670823524959650826333)
      ·
        refine ⟨7718126558821859869059875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20581670823524959650826333 7718126558821859869059875)
        ·
          refine ⟨11577189838232789803589813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7718126558821859869059875 11577189838232789803589813)
          ·
            refine ⟨1085361547334324044086545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11577189838232789803589813 1085361547334324044086545)
            ·
              refine ⟨814021160500743033064909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1085361547334324044086545 814021160500743033064909)
              ·
                refine ⟨305257935187778637399341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 814021160500743033064909 305257935187778637399341)
                ·
                  refine ⟨114471725695416989024753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 305257935187778637399341 114471725695416989024753)
                  ·
                    rfl

theorem cell21_501599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 2, 3, 3].length) (baseStart_501599 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_501599 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_501599 prefixEnd_501599 := by exact prefixLift 501599
  have htrace : WordTrace (prefixWord ++ tailWord_501599) baseStart_501599 baseEnd_501599 := by
    simpa [prefixWord, tailWord_501599, baseEnd_501599] using wordTrace_append hprefix tailTrace_501599
  have hstable : (prefixWord ++ tailWord_501599).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_501599).length < 2 ^ (prefixWord ++ tailWord_501599).sum := by decide
  have hdescent : baseEnd_501599 < baseStart_501599 := by decide
  rcases family_descends (prefixWord ++ tailWord_501599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_501613 : List Nat := [1, 5, 1, 1, 1, 1, 5, 2, 4]
def baseStart_501613 : Nat := 118140960795 + 501613 * 2 ^ 59
def prefixEnd_501613 : Nat := 4983230072969 + 3 ^ 40 * 501613 * 2
def baseEnd_501613 : Nat := 114474920686156075791391

theorem tailTrace_501613 : CollatzResearch.WordTrace tailWord_501613 prefixEnd_501613 114474920686156075791391 := by
  unfold tailWord_501613
  simp only [CollatzResearch.WordTrace]
  refine ⟨18295329131749244525077493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12196886087832829683384995 18295329131749244525077493)
  ·
    refine ⟨1715187106101491674226015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 18295329131749244525077493 1715187106101491674226015)
    ·
      refine ⟨2572780659152237511339023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1715187106101491674226015 2572780659152237511339023)
      ·
        refine ⟨3859170988728356267008535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2572780659152237511339023 3859170988728356267008535)
        ·
          refine ⟨5788756483092534400512803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3859170988728356267008535 5788756483092534400512803)
          ·
            refine ⟨8683134724638801600769205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5788756483092534400512803 8683134724638801600769205)
            ·
              refine ⟨814043880434887650072113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8683134724638801600769205 814043880434887650072113)
              ·
                refine ⟨610532910326165737554085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 814043880434887650072113 610532910326165737554085)
                ·
                  refine ⟨114474920686156075791391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 610532910326165737554085 114474920686156075791391)
                  ·
                    rfl

theorem cell21_501613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 5, 2, 4].length) (baseStart_501613 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_501613 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_501613 prefixEnd_501613 := by exact prefixLift 501613
  have htrace : WordTrace (prefixWord ++ tailWord_501613) baseStart_501613 baseEnd_501613 := by
    simpa [prefixWord, tailWord_501613, baseEnd_501613] using wordTrace_append hprefix tailTrace_501613
  have hstable : (prefixWord ++ tailWord_501613).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_501613).length < 2 ^ (prefixWord ++ tailWord_501613).sum := by decide
  have hdescent : baseEnd_501613 < baseStart_501613 := by decide
  rcases family_descends (prefixWord ++ tailWord_501613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_501641 : List Nat := [1, 2, 1, 1, 5, 1, 1, 4, 5]
def baseStart_501641 : Nat := 118140960795 + 501641 * 2 ^ 59
def prefixEnd_501641 : Nat := 4983230072969 + 3 ^ 40 * 501641 * 2
def baseEnd_501641 : Nat := 114481310667634249324667

theorem tailTrace_501641 : CollatzResearch.WordTrace tailWord_501641 prefixEnd_501641 114481310667634249324667 := by
  unfold tailWord_501641
  simp only [CollatzResearch.WordTrace]
  refine ⟨18296350375647805307096777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12197566917098536871397851 18296350375647805307096777)
  ·
    refine ⟨13722262781735853980322583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18296350375647805307096777 13722262781735853980322583)
    ·
      refine ⟨20583394172603780970483875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13722262781735853980322583 20583394172603780970483875)
      ·
        refine ⟨30875091258905671455725813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20583394172603780970483875 30875091258905671455725813)
        ·
          refine ⟨2894539805522406698974295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 30875091258905671455725813 2894539805522406698974295)
          ·
            refine ⟨4341809708283610048461443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2894539805522406698974295 4341809708283610048461443)
            ·
              refine ⟨6512714562425415072692165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4341809708283610048461443 6512714562425415072692165)
              ·
                refine ⟨1221133980454765326129781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6512714562425415072692165 1221133980454765326129781)
                ·
                  refine ⟨114481310667634249324667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1221133980454765326129781 114481310667634249324667)
                  ·
                    rfl

theorem cell21_501641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 4, 5].length) (baseStart_501641 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_501641 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_501641 prefixEnd_501641 := by exact prefixLift 501641
  have htrace : WordTrace (prefixWord ++ tailWord_501641) baseStart_501641 baseEnd_501641 := by
    simpa [prefixWord, tailWord_501641, baseEnd_501641] using wordTrace_append hprefix tailTrace_501641
  have hstable : (prefixWord ++ tailWord_501641).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_501641).length < 2 ^ (prefixWord ++ tailWord_501641).sum := by decide
  have hdescent : baseEnd_501641 < baseStart_501641 := by decide
  rcases family_descends (prefixWord ++ tailWord_501641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_501678 : List Nat := [4, 1, 5, 1, 1, 1, 2, 6]
def baseStart_501678 : Nat := 118140960795 + 501678 * 2 ^ 59
def prefixEnd_501678 : Nat := 4983230072969 + 3 ^ 40 * 501678 * 2
def baseEnd_501678 : Nat := 38163251523910135735975

theorem tailTrace_501678 : CollatzResearch.WordTrace tailWord_501678 prefixEnd_501678 38163251523910135735975 := by
  unfold tailWord_501678
  simp only [CollatzResearch.WordTrace]
  refine ⟨2287212484564220078274211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12198466584342507084129125 2287212484564220078274211)
  ·
    refine ⟨3430818726846330117411317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2287212484564220078274211 3430818726846330117411317)
    ·
      refine ⟨321639255641843448507311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3430818726846330117411317 321639255641843448507311)
      ·
        refine ⟨482458883462765172760967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 321639255641843448507311 482458883462765172760967)
        ·
          refine ⟨723688325194147759141451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 482458883462765172760967 723688325194147759141451)
          ·
            refine ⟨1085532487791221638712177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 723688325194147759141451 1085532487791221638712177)
            ·
              refine ⟨814149365843416229034133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1085532487791221638712177 814149365843416229034133)
              ·
                refine ⟨38163251523910135735975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 814149365843416229034133 38163251523910135735975)
                ·
                  rfl

theorem cell21_501678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 2, 6].length) (baseStart_501678 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_501678 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_501678 prefixEnd_501678 := by exact prefixLift 501678
  have htrace : WordTrace (prefixWord ++ tailWord_501678) baseStart_501678 baseEnd_501678 := by
    simpa [prefixWord, tailWord_501678, baseEnd_501678] using wordTrace_append hprefix tailTrace_501678
  have hstable : (prefixWord ++ tailWord_501678).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_501678).length < 2 ^ (prefixWord ++ tailWord_501678).sum := by decide
  have hdescent : baseEnd_501678 < baseStart_501678 := by decide
  rcases family_descends (prefixWord ++ tailWord_501678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_501799 : List Nat := [1, 1, 7, 1, 2, 1, 3, 1, 4]
def baseStart_501799 : Nat := 118140960795 + 501799 * 2 ^ 59
def prefixEnd_501799 : Nat := 4983230072969 + 3 ^ 40 * 501799 * 2
def baseEnd_501799 : Nat := 114517368420261085691011

theorem tailTrace_501799 : CollatzResearch.WordTrace tailWord_501799 prefixEnd_501799 114517368420261085691011 := by
  unfold tailWord_501799
  simp only [CollatzResearch.WordTrace]
  refine ⟨18302113109075398291348451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12201408739383598860898967 18302113109075398291348451)
  ·
    refine ⟨27453169663613097437022677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18302113109075398291348451 27453169663613097437022677)
    ·
      refine ⟨643433663990931971180219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 27453169663613097437022677 643433663990931971180219)
      ·
        refine ⟨965150495986397956770329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 643433663990931971180219 965150495986397956770329)
        ·
          refine ⟨723862871989798467577747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 965150495986397956770329 723862871989798467577747)
          ·
            refine ⟨1085794307984697701366621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 723862871989798467577747 1085794307984697701366621)
            ·
              refine ⟨407172865494261638012483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1085794307984697701366621 407172865494261638012483)
              ·
                refine ⟨610759298241392457018725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 407172865494261638012483 610759298241392457018725)
                ·
                  refine ⟨114517368420261085691011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 610759298241392457018725 114517368420261085691011)
                  ·
                    rfl

theorem cell21_501799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 3, 1, 4].length) (baseStart_501799 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_501799 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_501799 prefixEnd_501799 := by exact prefixLift 501799
  have htrace : WordTrace (prefixWord ++ tailWord_501799) baseStart_501799 baseEnd_501799 := by
    simpa [prefixWord, tailWord_501799, baseEnd_501799] using wordTrace_append hprefix tailTrace_501799
  have hstable : (prefixWord ++ tailWord_501799).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_501799).length < 2 ^ (prefixWord ++ tailWord_501799).sum := by decide
  have hdescent : baseEnd_501799 < baseStart_501799 := by decide
  rcases family_descends (prefixWord ++ tailWord_501799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_501838 : List Nat := [4, 1, 1, 1, 1, 4, 9]
def baseStart_501838 : Nat := 118140960795 + 501838 * 2 ^ 59
def prefixEnd_501838 : Nat := 4983230072969 + 3 ^ 40 * 501838 * 2
def baseEnd_501838 : Nat := 12725140972400631615659

theorem tailTrace_501838 : CollatzResearch.WordTrace tailWord_501838 prefixEnd_501838 12725140972400631615659 := by
  unfold tailWord_501838
  simp only [CollatzResearch.WordTrace]
  refine ⟨2287941944491763494002271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12202357037289405301345445 2287941944491763494002271)
  ·
    refine ⟨3431912916737645241003407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2287941944491763494002271 3431912916737645241003407)
    ·
      refine ⟨5147869375106467861505111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3431912916737645241003407 5147869375106467861505111)
      ·
        refine ⟨7721804062659701792257667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5147869375106467861505111 7721804062659701792257667)
        ·
          refine ⟨11582706093989552688386501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7721804062659701792257667 11582706093989552688386501)
          ·
            refine ⟨2171757392623041129072469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11582706093989552688386501 2171757392623041129072469)
            ·
              refine ⟨12725140972400631615659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2171757392623041129072469 12725140972400631615659)
              ·
                rfl

theorem cell21_501838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 9].length) (baseStart_501838 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_501838 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_501838 prefixEnd_501838 := by exact prefixLift 501838
  have htrace : WordTrace (prefixWord ++ tailWord_501838) baseStart_501838 baseEnd_501838 := by
    simpa [prefixWord, tailWord_501838, baseEnd_501838] using wordTrace_append hprefix tailTrace_501838
  have hstable : (prefixWord ++ tailWord_501838).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_501838).length < 2 ^ (prefixWord ++ tailWord_501838).sum := by decide
  have hdescent : baseEnd_501838 < baseStart_501838 := by decide
  rcases family_descends (prefixWord ++ tailWord_501838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_501858 : List Nat := [3, 3, 2, 2, 2, 1, 1, 3, 4]
def baseStart_501858 : Nat := 118140960795 + 501858 * 2 ^ 59
def prefixEnd_501858 : Nat := 4983230072969 + 3 ^ 40 * 501858 * 2
def baseEnd_501858 : Nat := 114530833024090094207557

theorem tailTrace_501858 : CollatzResearch.WordTrace tailWord_501858 prefixEnd_501858 114530833024090094207557 := by
  unfold tailWord_501858
  simp only [CollatzResearch.WordTrace]
  refine ⟨4576066253965412841936557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12202843343907767578497485 4576066253965412841936557)
  ·
    refine ⟨1716024845237029815726209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4576066253965412841936557 1716024845237029815726209)
    ·
      refine ⟨1287018633927772361794657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1716024845237029815726209 1287018633927772361794657)
      ·
        refine ⟨965263975445829271345993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1287018633927772361794657 965263975445829271345993)
        ·
          refine ⟨723947981584371953509495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 965263975445829271345993 723947981584371953509495)
          ·
            refine ⟨1085921972376557930264243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 723947981584371953509495 1085921972376557930264243)
            ·
              refine ⟨1628882958564836895396365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1085921972376557930264243 1628882958564836895396365)
              ·
                refine ⟨610831109461813835773637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1628882958564836895396365 610831109461813835773637)
                ·
                  refine ⟨114530833024090094207557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 610831109461813835773637 114530833024090094207557)
                  ·
                    rfl

theorem cell21_501858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 1, 3, 4].length) (baseStart_501858 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_501858 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_501858 prefixEnd_501858 := by exact prefixLift 501858
  have htrace : WordTrace (prefixWord ++ tailWord_501858) baseStart_501858 baseEnd_501858 := by
    simpa [prefixWord, tailWord_501858, baseEnd_501858] using wordTrace_append hprefix tailTrace_501858
  have hstable : (prefixWord ++ tailWord_501858).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_501858).length < 2 ^ (prefixWord ++ tailWord_501858).sum := by decide
  have hdescent : baseEnd_501858 < baseStart_501858 := by decide
  rcases family_descends (prefixWord ++ tailWord_501858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_501869 : List Nat := [1, 5, 1, 1, 2, 1, 2, 1, 7]
def baseStart_501869 : Nat := 118140960795 + 501869 * 2 ^ 59
def prefixEnd_501869 : Nat := 4983230072969 + 3 ^ 40 * 501869 * 2
def baseEnd_501869 : Nat := 114533343373956519524201

theorem tailTrace_501869 : CollatzResearch.WordTrace tailWord_501869 prefixEnd_501869 114533343373956519524201 := by
  unfold tailWord_501869
  simp only [CollatzResearch.WordTrace]
  refine ⟨18304666218821800246396661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12203110812547866830931107 18304666218821800246396661)
  ·
    refine ⟨1716062458014543773099687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 18304666218821800246396661 1716062458014543773099687)
    ·
      refine ⟨2574093687021815659649531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1716062458014543773099687 2574093687021815659649531)
      ·
        refine ⟨3861140530532723489474297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2574093687021815659649531 3861140530532723489474297)
        ·
          refine ⟨2895855397899542617105723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3861140530532723489474297 2895855397899542617105723)
          ·
            refine ⟨4343783096849313925658585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2895855397899542617105723 4343783096849313925658585)
            ·
              refine ⟨3257837322636985444243939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4343783096849313925658585 3257837322636985444243939)
              ·
                refine ⟨4886755983955478166365909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3257837322636985444243939 4886755983955478166365909)
                ·
                  refine ⟨114533343373956519524201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4886755983955478166365909 114533343373956519524201)
                  ·
                    rfl

theorem cell21_501869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 2, 1, 7].length) (baseStart_501869 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_501869 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_501869 prefixEnd_501869 := by exact prefixLift 501869
  have htrace : WordTrace (prefixWord ++ tailWord_501869) baseStart_501869 baseEnd_501869 := by
    simpa [prefixWord, tailWord_501869, baseEnd_501869] using wordTrace_append hprefix tailTrace_501869
  have hstable : (prefixWord ++ tailWord_501869).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_501869).length < 2 ^ (prefixWord ++ tailWord_501869).sum := by decide
  have hdescent : baseEnd_501869 < baseStart_501869 := by decide
  rcases family_descends (prefixWord ++ tailWord_501869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_501962 : List Nat := [3, 1, 2, 1, 3, 1, 1, 6, 3]
def baseStart_501962 : Nat := 118140960795 + 501962 * 2 ^ 59
def prefixEnd_501962 : Nat := 4983230072969 + 3 ^ 40 * 501962 * 2
def baseEnd_501962 : Nat := 114554567241009024474011

theorem tailTrace_501962 : CollatzResearch.WordTrace tailWord_501962 prefixEnd_501962 114554567241009024474011 := by
  unfold tailWord_501962
  simp only [CollatzResearch.WordTrace]
  refine ⟨4577014551871219282383035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12205372138323251419688093 4577014551871219282383035)
  ·
    refine ⟨6865521827806828923574553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4577014551871219282383035 6865521827806828923574553)
    ·
      refine ⟨5149141370855121692680915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6865521827806828923574553 5149141370855121692680915)
      ·
        refine ⟨7723712056282682539021373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5149141370855121692680915 7723712056282682539021373)
        ·
          refine ⟨2896392021106005952133015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7723712056282682539021373 2896392021106005952133015)
          ·
            refine ⟨4344588031659008928199523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2896392021106005952133015 4344588031659008928199523)
            ·
              refine ⟨6516882047488513392299285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4344588031659008928199523 6516882047488513392299285)
              ·
                refine ⟨305478845976024065264029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 6516882047488513392299285 305478845976024065264029)
                ·
                  refine ⟨114554567241009024474011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 305478845976024065264029 114554567241009024474011)
                  ·
                    rfl

theorem cell21_501962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 6, 3].length) (baseStart_501962 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_501962 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_501962 prefixEnd_501962 := by exact prefixLift 501962
  have htrace : WordTrace (prefixWord ++ tailWord_501962) baseStart_501962 baseEnd_501962 := by
    simpa [prefixWord, tailWord_501962, baseEnd_501962] using wordTrace_append hprefix tailTrace_501962
  have hstable : (prefixWord ++ tailWord_501962).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_501962).length < 2 ^ (prefixWord ++ tailWord_501962).sum := by decide
  have hdescent : baseEnd_501962 < baseStart_501962 := by decide
  rcases family_descends (prefixWord ++ tailWord_501962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_502066 : List Nat := [3, 2, 1, 1, 5, 9]
def baseStart_502066 : Nat := 118140960795 + 502066 * 2 ^ 59
def prefixEnd_502066 : Nat := 4983230072969 + 3 ^ 40 * 502066 * 2
def baseEnd_502066 : Nat := 4243640794738072397795

theorem tailTrace_502066 : CollatzResearch.WordTrace tailWord_502066 prefixEnd_502066 4243640794738072397795 := by
  unfold tailWord_502066
  simp only [CollatzResearch.WordTrace]
  refine ⟨4577962849777025722829513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12207900932738735260878701 4577962849777025722829513)
  ·
    refine ⟨3433472137332769292122135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4577962849777025722829513 3433472137332769292122135)
    ·
      refine ⟨5150208205999153938183203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3433472137332769292122135 5150208205999153938183203)
      ·
        refine ⟨7725312308998730907274805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5150208205999153938183203 7725312308998730907274805)
        ·
          refine ⟨724248028968631022557013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7725312308998730907274805 724248028968631022557013)
          ·
            refine ⟨4243640794738072397795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 724248028968631022557013 4243640794738072397795)
            ·
              rfl

theorem cell21_502066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 9].length) (baseStart_502066 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_502066 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_502066 prefixEnd_502066 := by exact prefixLift 502066
  have htrace : WordTrace (prefixWord ++ tailWord_502066) baseStart_502066 baseEnd_502066 := by
    simpa [prefixWord, tailWord_502066, baseEnd_502066] using wordTrace_append hprefix tailTrace_502066
  have hstable : (prefixWord ++ tailWord_502066).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_502066).length < 2 ^ (prefixWord ++ tailWord_502066).sum := by decide
  have hdescent : baseEnd_502066 < baseStart_502066 := by decide
  rcases family_descends (prefixWord ++ tailWord_502066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_502097 : List Nat := [1, 2, 2, 1, 4, 3, 1, 2, 5]
def baseStart_502097 : Nat := 118140960795 + 502097 * 2 ^ 59
def prefixEnd_502097 : Nat := 4983230072969 + 3 ^ 40 * 502097 * 2
def baseEnd_502097 : Nat := 114585376080278789723735

theorem tailTrace_502097 : CollatzResearch.WordTrace tailWord_502097 prefixEnd_502097 114585376080278789723735 := by
  unfold tailWord_502097
  simp only [CollatzResearch.WordTrace]
  refine ⟨18312982061995795185696545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12208654707997196790464363 18312982061995795185696545)
  ·
    refine ⟨13734736546496846389272409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18312982061995795185696545 13734736546496846389272409)
    ·
      refine ⟨10301052409872634791954307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13734736546496846389272409 10301052409872634791954307)
      ·
        refine ⟨15451578614808952187931461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10301052409872634791954307 15451578614808952187931461)
        ·
          refine ⟨2897170990276678535237149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15451578614808952187931461 2897170990276678535237149)
          ·
            refine ⟨1086439121353754450713931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2897170990276678535237149 1086439121353754450713931)
            ·
              refine ⟨1629658682030631676070897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1086439121353754450713931 1629658682030631676070897)
              ·
                refine ⟨1222244011522973757053173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1629658682030631676070897 1222244011522973757053173)
                ·
                  refine ⟨114585376080278789723735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1222244011522973757053173 114585376080278789723735)
                  ·
                    rfl

theorem cell21_502097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 1, 2, 5].length) (baseStart_502097 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_502097 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_502097 prefixEnd_502097 := by exact prefixLift 502097
  have htrace : WordTrace (prefixWord ++ tailWord_502097) baseStart_502097 baseEnd_502097 := by
    simpa [prefixWord, tailWord_502097, baseEnd_502097] using wordTrace_append hprefix tailTrace_502097
  have hstable : (prefixWord ++ tailWord_502097).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_502097).length < 2 ^ (prefixWord ++ tailWord_502097).sum := by decide
  have hdescent : baseEnd_502097 < baseStart_502097 := by decide
  rcases family_descends (prefixWord ++ tailWord_502097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_502128 : List Nat := [2, 1, 1, 1, 4, 3, 3, 2, 4]
def baseStart_502128 : Nat := 118140960795 + 502128 * 2 ^ 59
def prefixEnd_502128 : Nat := 4983230072969 + 3 ^ 40 * 502128 * 2
def baseEnd_502128 : Nat := 114592450702629624707005

theorem tailTrace_502128 : CollatzResearch.WordTrace tailWord_502128 prefixEnd_502128 114592450702629624707005 := by
  unfold tailWord_502128
  simp only [CollatzResearch.WordTrace]
  refine ⟨9157056362441743740037519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12209408483255658320050025 9157056362441743740037519)
  ·
    refine ⟨13735584543662615610056279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9157056362441743740037519 13735584543662615610056279)
    ·
      refine ⟨20603376815493923415084419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13735584543662615610056279 20603376815493923415084419)
      ·
        refine ⟨30905065223240885122626629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20603376815493923415084419 30905065223240885122626629)
        ·
          refine ⟨5794699729357665960492493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30905065223240885122626629 5794699729357665960492493)
          ·
            refine ⟨2173012398509124735184685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5794699729357665960492493 2173012398509124735184685)
            ·
              refine ⟨814879649440921775694257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2173012398509124735184685 814879649440921775694257)
              ·
                refine ⟨611159737080691331770693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 814879649440921775694257 611159737080691331770693)
                ·
                  refine ⟨114592450702629624707005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 611159737080691331770693 114592450702629624707005)
                  ·
                    rfl

theorem cell21_502128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 3, 2, 4].length) (baseStart_502128 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_502128 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_502128 prefixEnd_502128 := by exact prefixLift 502128
  have htrace : WordTrace (prefixWord ++ tailWord_502128) baseStart_502128 baseEnd_502128 := by
    simpa [prefixWord, tailWord_502128, baseEnd_502128] using wordTrace_append hprefix tailTrace_502128
  have hstable : (prefixWord ++ tailWord_502128).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_502128).length < 2 ^ (prefixWord ++ tailWord_502128).sum := by decide
  have hdescent : baseEnd_502128 < baseStart_502128 := by decide
  rcases family_descends (prefixWord ++ tailWord_502128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_502196 : List Nat := [2, 5, 2, 2, 1, 2, 2, 1, 4]
def baseStart_502196 : Nat := 118140960795 + 502196 * 2 ^ 59
def prefixEnd_502196 : Nat := 4983230072969 + 3 ^ 40 * 502196 * 2
def baseEnd_502196 : Nat := 114607969229076617573533

theorem tailTrace_502196 : CollatzResearch.WordTrace tailWord_502196 prefixEnd_502196 114607969229076617573533 := by
  unfold tailWord_502196
  simp only [CollatzResearch.WordTrace]
  refine ⟨9158296444318567546775221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12211061925758090062366961 9158296444318567546775221)
  ·
    refine ⟨858590291654865707510177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 9158296444318567546775221 858590291654865707510177)
    ·
      refine ⟨643942718741149280632633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 858590291654865707510177 643942718741149280632633)
      ·
        refine ⟨482957039055861960474475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 643942718741149280632633 482957039055861960474475)
        ·
          refine ⟨724435558583792940711713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 482957039055861960474475 724435558583792940711713)
          ·
            refine ⟨543326668937844705533785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 724435558583792940711713 543326668937844705533785)
            ·
              refine ⟨407495001703383529150339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 543326668937844705533785 407495001703383529150339)
              ·
                refine ⟨611242502555075293725509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 407495001703383529150339 611242502555075293725509)
                ·
                  refine ⟨114607969229076617573533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 611242502555075293725509 114607969229076617573533)
                  ·
                    rfl

theorem cell21_502196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 2, 2, 1, 4].length) (baseStart_502196 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_502196 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_502196 prefixEnd_502196 := by exact prefixLift 502196
  have htrace : WordTrace (prefixWord ++ tailWord_502196) baseStart_502196 baseEnd_502196 := by
    simpa [prefixWord, tailWord_502196, baseEnd_502196] using wordTrace_append hprefix tailTrace_502196
  have hstable : (prefixWord ++ tailWord_502196).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_502196).length < 2 ^ (prefixWord ++ tailWord_502196).sum := by decide
  have hdescent : baseEnd_502196 < baseStart_502196 := by decide
  rcases family_descends (prefixWord ++ tailWord_502196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_502277 : List Nat := [1, 3, 1, 1, 2, 2, 2, 9]
def baseStart_502277 : Nat := 118140960795 + 502277 * 2 ^ 59
def prefixEnd_502277 : Nat := 4983230072969 + 3 ^ 40 * 502277 * 2
def baseEnd_502277 : Nat := 38208818177546158907789

theorem tailTrace_502277 : CollatzResearch.WordTrace tailWord_502277 prefixEnd_502277 38208818177546158907789 := by
  unfold tailWord_502277
  simp only [CollatzResearch.WordTrace]
  refine ⟨18319547201343685927249085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12213031467562457284832723 18319547201343685927249085)
  ·
    refine ⟨6869830200503882222718407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18319547201343685927249085 6869830200503882222718407)
    ·
      refine ⟨10304745300755823334077611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6869830200503882222718407 10304745300755823334077611)
      ·
        refine ⟨15457117951133735001116417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10304745300755823334077611 15457117951133735001116417)
        ·
          refine ⟨11592838463350301250837313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15457117951133735001116417 11592838463350301250837313)
          ·
            refine ⟨8694628847512725938127985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11592838463350301250837313 8694628847512725938127985)
            ·
              refine ⟨6520971635634544453595989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8694628847512725938127985 6520971635634544453595989)
              ·
                refine ⟨38208818177546158907789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 6520971635634544453595989 38208818177546158907789)
                ·
                  rfl

theorem cell21_502277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 9].length) (baseStart_502277 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_502277 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_502277 prefixEnd_502277 := by exact prefixLift 502277
  have htrace : WordTrace (prefixWord ++ tailWord_502277) baseStart_502277 baseEnd_502277 := by
    simpa [prefixWord, tailWord_502277, baseEnd_502277] using wordTrace_append hprefix tailTrace_502277
  have hstable : (prefixWord ++ tailWord_502277).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_502277).length < 2 ^ (prefixWord ++ tailWord_502277).sum := by decide
  have hdescent : baseEnd_502277 < baseStart_502277 := by decide
  rcases family_descends (prefixWord ++ tailWord_502277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_502353 : List Nat := [1, 2, 2, 1, 3, 3, 9]
def baseStart_502353 : Nat := 118140960795 + 502353 * 2 ^ 59
def prefixEnd_502353 : Nat := 4983230072969 + 3 ^ 40 * 502353 * 2
def baseEnd_502353 : Nat := 12738199863119914828505

theorem tailTrace_502353 : CollatzResearch.WordTrace tailWord_502353 prefixEnd_502353 12738199863119914828505 := by
  unfold tailWord_502353
  simp only [CollatzResearch.WordTrace]
  refine ⟨18322319149068350907015713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12214879432712233938010475 18322319149068350907015713)
  ·
    refine ⟨13741739361801263180261785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18322319149068350907015713 13741739361801263180261785)
    ·
      refine ⟨10306304521350947385196339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13741739361801263180261785 10306304521350947385196339)
      ·
        refine ⟨15459456782026421077794509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10306304521350947385196339 15459456782026421077794509)
        ·
          refine ⟨5797296293259907904172941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15459456782026421077794509 5797296293259907904172941)
          ·
            refine ⟨2173986109972465464064853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5797296293259907904172941 2173986109972465464064853)
            ·
              refine ⟨12738199863119914828505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2173986109972465464064853 12738199863119914828505)
              ·
                rfl

theorem cell21_502353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 9].length) (baseStart_502353 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_502353 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_502353 prefixEnd_502353 := by exact prefixLift 502353
  have htrace : WordTrace (prefixWord ++ tailWord_502353) baseStart_502353 baseEnd_502353 := by
    simpa [prefixWord, tailWord_502353, baseEnd_502353] using wordTrace_append hprefix tailTrace_502353
  have hstable : (prefixWord ++ tailWord_502353).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_502353).length < 2 ^ (prefixWord ++ tailWord_502353).sum := by decide
  have hdescent : baseEnd_502353 < baseStart_502353 := by decide
  rcases family_descends (prefixWord ++ tailWord_502353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_502460 : List Nat := [2, 2, 2, 3, 1, 1, 1, 2, 7]
def baseStart_502460 : Nat := 118140960795 + 502460 * 2 ^ 59
def prefixEnd_502460 : Nat := 4983230072969 + 3 ^ 40 * 502460 * 2
def baseEnd_502460 : Nat := 114668217625870825172993

theorem tailTrace_502460 : CollatzResearch.WordTrace tailWord_502460 prefixEnd_502460 114668217625870825172993 := by
  unfold tailWord_502460
  simp only [CollatzResearch.WordTrace]
  refine ⟨9163110879840354090580417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12217481173120472120773889 9163110879840354090580417)
  ·
    refine ⟨6872333159880265567935313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9163110879840354090580417 6872333159880265567935313)
    ·
      refine ⟨5154249869910199175951485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6872333159880265567935313 5154249869910199175951485)
      ·
        refine ⟨1932843701216324690981807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5154249869910199175951485 1932843701216324690981807)
        ·
          refine ⟨2899265551824487036472711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1932843701216324690981807 2899265551824487036472711)
          ·
            refine ⟨4348898327736730554709067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2899265551824487036472711 4348898327736730554709067)
            ·
              refine ⟨6523347491605095832063601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4348898327736730554709067 6523347491605095832063601)
              ·
                refine ⟨4892510618703821874047701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6523347491605095832063601 4892510618703821874047701)
                ·
                  refine ⟨114668217625870825172993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4892510618703821874047701 114668217625870825172993)
                  ·
                    rfl

theorem cell21_502460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 2, 7].length) (baseStart_502460 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_502460 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_502460 prefixEnd_502460 := by exact prefixLift 502460
  have htrace : WordTrace (prefixWord ++ tailWord_502460) baseStart_502460 baseEnd_502460 := by
    simpa [prefixWord, tailWord_502460, baseEnd_502460] using wordTrace_append hprefix tailTrace_502460
  have hstable : (prefixWord ++ tailWord_502460).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_502460).length < 2 ^ (prefixWord ++ tailWord_502460).sum := by decide
  have hdescent : baseEnd_502460 < baseStart_502460 := by decide
  rcases family_descends (prefixWord ++ tailWord_502460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_502581 : List Nat := [1, 3, 3, 1, 3, 10]
def baseStart_502581 : Nat := 118140960795 + 502581 * 2 ^ 59
def prefixEnd_502581 : Nat := 4983230072969 + 3 ^ 40 * 502581 * 2
def baseEnd_502581 : Nat := 4247993758311166802077

theorem tailTrace_502581 : CollatzResearch.WordTrace tailWord_502581 prefixEnd_502581 4247993758311166802077 := by
  unfold tailWord_502581
  simp only [CollatzResearch.WordTrace]
  refine ⟨18330634992242345846315597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12220423328161563897543731 18330634992242345846315597)
  ·
    refine ⟨6873988122090879692368349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18330634992242345846315597 6873988122090879692368349)
    ·
      refine ⟨2577745545784079884638131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6873988122090879692368349 2577745545784079884638131)
      ·
        refine ⟨3866618318676119826957197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2577745545784079884638131 3866618318676119826957197)
        ·
          refine ⟨1449981869503544935108949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3866618318676119826957197 1449981869503544935108949)
          ·
            refine ⟨4247993758311166802077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 1449981869503544935108949 4247993758311166802077)
            ·
              rfl

theorem cell21_502581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 10].length) (baseStart_502581 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_502581 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_502581 prefixEnd_502581 := by exact prefixLift 502581
  have htrace : WordTrace (prefixWord ++ tailWord_502581) baseStart_502581 baseEnd_502581 := by
    simpa [prefixWord, tailWord_502581, baseEnd_502581] using wordTrace_append hprefix tailTrace_502581
  have hstable : (prefixWord ++ tailWord_502581).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_502581).length < 2 ^ (prefixWord ++ tailWord_502581).sum := by decide
  have hdescent : baseEnd_502581 < baseStart_502581 := by decide
  rcases family_descends (prefixWord ++ tailWord_502581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_502629 : List Nat := [1, 3, 1, 3, 1, 1, 3, 5, 3]
def baseStart_502629 : Nat := 118140960795 + 502629 * 2 ^ 59
def prefixEnd_502629 : Nat := 4983230072969 + 3 ^ 40 * 502629 * 2
def baseEnd_502629 : Nat := 114706785728364086855981

theorem tailTrace_502629 : CollatzResearch.WordTrace tailWord_502629 prefixEnd_502629 114706785728364086855981 := by
  unfold tailWord_502629
  simp only [CollatzResearch.WordTrace]
  refine ⟨18332385696068450044062941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12221590464045633362708627 18332385696068450044062941)
  ·
    refine ⟨6874644636025668766523603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18332385696068450044062941 6874644636025668766523603)
    ·
      refine ⟨10311966954038503149785405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6874644636025668766523603 10311966954038503149785405)
      ·
        refine ⟨3866987607764438681169527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10311966954038503149785405 3866987607764438681169527)
        ·
          refine ⟨5800481411646658021754291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3866987607764438681169527 5800481411646658021754291)
          ·
            refine ⟨8700722117469987032631437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5800481411646658021754291 8700722117469987032631437)
            ·
              refine ⟨3262770794051245137236789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8700722117469987032631437 3262770794051245137236789)
              ·
                refine ⟨305884761942304231615949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3262770794051245137236789 305884761942304231615949)
                ·
                  refine ⟨114706785728364086855981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 305884761942304231615949 114706785728364086855981)
                  ·
                    rfl

theorem cell21_502629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 3, 5, 3].length) (baseStart_502629 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_502629 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_502629 prefixEnd_502629 := by exact prefixLift 502629
  have htrace : WordTrace (prefixWord ++ tailWord_502629) baseStart_502629 baseEnd_502629 := by
    simpa [prefixWord, tailWord_502629, baseEnd_502629] using wordTrace_append hprefix tailTrace_502629
  have hstable : (prefixWord ++ tailWord_502629).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_502629).length < 2 ^ (prefixWord ++ tailWord_502629).sum := by decide
  have hdescent : baseEnd_502629 < baseStart_502629 := by decide
  rcases family_descends (prefixWord ++ tailWord_502629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_502643 : List Nat := [1, 1, 1, 2, 2, 1, 7, 2, 4]
def baseStart_502643 : Nat := 118140960795 + 502643 * 2 ^ 59
def prefixEnd_502643 : Nat := 4983230072969 + 3 ^ 40 * 502643 * 2
def baseEnd_502643 : Nat := 114709980719103173622619

theorem tailTrace_502643 : CollatzResearch.WordTrace tailWord_502643 prefixEnd_502643 114709980719103173622619 := by
  unfold tailWord_502643
  simp only [CollatzResearch.WordTrace]
  refine ⟨18332896318017730435072583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12221930878678486956715055 18332896318017730435072583)
  ·
    refine ⟨27499344477026595652608875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18332896318017730435072583 27499344477026595652608875)
    ·
      refine ⟨41249016715539893478913313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27499344477026595652608875 41249016715539893478913313)
      ·
        refine ⟨30936762536654920109184985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41249016715539893478913313 30936762536654920109184985)
        ·
          refine ⟨23202571902491190081888739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30936762536654920109184985 23202571902491190081888739)
          ·
            refine ⟨34803857853736785122833109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23202571902491190081888739 34803857853736785122833109)
            ·
              refine ⟨815715418446955901316401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 34803857853736785122833109 815715418446955901316401)
              ·
                refine ⟨611786563835216925987301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 815715418446955901316401 611786563835216925987301)
                ·
                  refine ⟨114709980719103173622619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 611786563835216925987301 114709980719103173622619)
                  ·
                    rfl

theorem cell21_502643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 7, 2, 4].length) (baseStart_502643 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_502643 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_502643 prefixEnd_502643 := by exact prefixLift 502643
  have htrace : WordTrace (prefixWord ++ tailWord_502643) baseStart_502643 baseEnd_502643 := by
    simpa [prefixWord, tailWord_502643, baseEnd_502643] using wordTrace_append hprefix tailTrace_502643
  have hstable : (prefixWord ++ tailWord_502643).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_502643).length < 2 ^ (prefixWord ++ tailWord_502643).sum := by decide
  have hdescent : baseEnd_502643 < baseStart_502643 := by decide
  rcases family_descends (prefixWord ++ tailWord_502643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_502646 : List Nat := [5, 1, 1, 3, 1, 2, 2, 1, 5]
def baseStart_502646 : Nat := 118140960795 + 502646 * 2 ^ 59
def prefixEnd_502646 : Nat := 4983230072969 + 3 ^ 40 * 502646 * 2
def baseEnd_502646 : Nat := 114710665359975835072613

theorem tailTrace_502646 : CollatzResearch.WordTrace tailWord_502646 prefixEnd_502646 114710665359975835072613 := by
  unfold tailWord_502646
  simp only [CollatzResearch.WordTrace]
  refine ⟨1145812858562928871714487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 12222003824671241298287861 1145812858562928871714487)
  ·
    refine ⟨1718719287844393307571731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1145812858562928871714487 1718719287844393307571731)
    ·
      refine ⟨2578078931766589961357597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1718719287844393307571731 2578078931766589961357597)
      ·
        refine ⟨966779599412471235509099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2578078931766589961357597 966779599412471235509099)
        ·
          refine ⟨1450169399118706853263649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 966779599412471235509099 1450169399118706853263649)
          ·
            refine ⟨1087627049339030139947737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1450169399118706853263649 1087627049339030139947737)
            ·
              refine ⟨815720287004272604960803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1087627049339030139947737 815720287004272604960803)
              ·
                refine ⟨1223580430506408907441205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 815720287004272604960803 1223580430506408907441205)
                ·
                  refine ⟨114710665359975835072613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1223580430506408907441205 114710665359975835072613)
                  ·
                    rfl

theorem cell21_502646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 2, 1, 5].length) (baseStart_502646 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_502646 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_502646 prefixEnd_502646 := by exact prefixLift 502646
  have htrace : WordTrace (prefixWord ++ tailWord_502646) baseStart_502646 baseEnd_502646 := by
    simpa [prefixWord, tailWord_502646, baseEnd_502646] using wordTrace_append hprefix tailTrace_502646
  have hstable : (prefixWord ++ tailWord_502646).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_502646).length < 2 ^ (prefixWord ++ tailWord_502646).sum := by decide
  have hdescent : baseEnd_502646 < baseStart_502646 := by decide
  rcases family_descends (prefixWord ++ tailWord_502646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_502798 : List Nat := [4, 1, 1, 2, 2, 3, 2, 3, 3]
def baseStart_502798 : Nat := 118140960795 + 502798 * 2 ^ 59
def prefixEnd_502798 : Nat := 4983230072969 + 3 ^ 40 * 502798 * 2
def baseEnd_502798 : Nat := 114745353830857348538969

theorem tailTrace_502798 : CollatzResearch.WordTrace tailWord_502798 prefixEnd_502798 114745353830857348538969 := by
  unfold tailWord_502798
  simp only [CollatzResearch.WordTrace]
  refine ⟨2292318704057023988370631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12225699754970794604643365 2292318704057023988370631)
  ·
    refine ⟨3438478056085535982555947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2292318704057023988370631 3438478056085535982555947)
    ·
      refine ⟨5157717084128303973833921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3438478056085535982555947 5157717084128303973833921)
      ·
        refine ⟨3868287813096227980375441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5157717084128303973833921 3868287813096227980375441)
        ·
          refine ⟨2901215859822170985281581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3868287813096227980375441 2901215859822170985281581)
          ·
            refine ⟨1087955947433314119480593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2901215859822170985281581 1087955947433314119480593)
            ·
              refine ⟨815966960574985589610445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1087955947433314119480593 815966960574985589610445)
              ·
                refine ⟨305987610215619596103917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 815966960574985589610445 305987610215619596103917)
                ·
                  refine ⟨114745353830857348538969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 305987610215619596103917 114745353830857348538969)
                  ·
                    rfl

theorem cell21_502798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 2, 3, 3].length) (baseStart_502798 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_502798 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_502798 prefixEnd_502798 := by exact prefixLift 502798
  have htrace : WordTrace (prefixWord ++ tailWord_502798) baseStart_502798 baseEnd_502798 := by
    simpa [prefixWord, tailWord_502798, baseEnd_502798] using wordTrace_append hprefix tailTrace_502798
  have hstable : (prefixWord ++ tailWord_502798).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_502798).length < 2 ^ (prefixWord ++ tailWord_502798).sum := by decide
  have hdescent : baseEnd_502798 < baseStart_502798 := by decide
  rcases family_descends (prefixWord ++ tailWord_502798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_502840 : List Nat := [2, 1, 2, 1, 5, 1, 2, 2, 5]
def baseStart_502840 : Nat := 118140960795 + 502840 * 2 ^ 59
def prefixEnd_502840 : Nat := 4983230072969 + 3 ^ 40 * 502840 * 2
def baseEnd_502840 : Nat := 114754938803074608838883

theorem tailTrace_502840 : CollatzResearch.WordTrace tailWord_502840 prefixEnd_502840 114754938803074608838883 := by
  unfold tailWord_502840
  simp only [CollatzResearch.WordTrace]
  refine ⟨9170040749152016539996987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12226720998869355386662649 9170040749152016539996987)
  ·
    refine ⟨13755061123728024809995481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9170040749152016539996987 13755061123728024809995481)
    ·
      refine ⟨10316295842796018607496611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13755061123728024809995481 10316295842796018607496611)
      ·
        refine ⟨15474443764194027911244917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10316295842796018607496611 15474443764194027911244917)
        ·
          refine ⟨1450729102893190116679211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 15474443764194027911244917 1450729102893190116679211)
          ·
            refine ⟨2176093654339785175018817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1450729102893190116679211 2176093654339785175018817)
            ·
              refine ⟨1632070240754838881264113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2176093654339785175018817 1632070240754838881264113)
              ·
                refine ⟨1224052680566129160948085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1632070240754838881264113 1224052680566129160948085)
                ·
                  refine ⟨114754938803074608838883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1224052680566129160948085 114754938803074608838883)
                  ·
                    rfl

theorem cell21_502840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 2, 2, 5].length) (baseStart_502840 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_502840 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_502840 prefixEnd_502840 := by exact prefixLift 502840
  have htrace : WordTrace (prefixWord ++ tailWord_502840) baseStart_502840 baseEnd_502840 := by
    simpa [prefixWord, tailWord_502840, baseEnd_502840] using wordTrace_append hprefix tailTrace_502840
  have hstable : (prefixWord ++ tailWord_502840).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_502840).length < 2 ^ (prefixWord ++ tailWord_502840).sum := by decide
  have hdescent : baseEnd_502840 < baseStart_502840 := by decide
  rcases family_descends (prefixWord ++ tailWord_502840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_502885 : List Nat := [1, 3, 1, 3, 2, 1, 4, 6]
def baseStart_502885 : Nat := 118140960795 + 502885 * 2 ^ 59
def prefixEnd_502885 : Nat := 4983230072969 + 3 ^ 40 * 502885 * 2
def baseEnd_502885 : Nat := 38255069472054843529597

theorem tailTrace_502885 : CollatzResearch.WordTrace tailWord_502885 prefixEnd_502885 38255069472054843529597 := by
  unfold tailWord_502885
  simp only [CollatzResearch.WordTrace]
  refine ⟨18341722783141005765382109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12227815188760670510254739 18341722783141005765382109)
  ·
    refine ⟨6878146043677877162018291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18341722783141005765382109 6878146043677877162018291)
    ·
      refine ⟨10317219065516815743027437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6878146043677877162018291 10317219065516815743027437)
      ·
        refine ⟨3868957149568805903635289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10317219065516815743027437 3868957149568805903635289)
        ·
          refine ⟨2901717862176604427726467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3868957149568805903635289 2901717862176604427726467)
          ·
            refine ⟨4352576793264906641589701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2901717862176604427726467 4352576793264906641589701)
            ·
              refine ⟨816108148737169995298069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4352576793264906641589701 816108148737169995298069)
              ·
                refine ⟨38255069472054843529597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 816108148737169995298069 38255069472054843529597)
                ·
                  rfl

theorem cell21_502885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 4, 6].length) (baseStart_502885 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_502885 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_502885 prefixEnd_502885 := by exact prefixLift 502885
  have htrace : WordTrace (prefixWord ++ tailWord_502885) baseStart_502885 baseEnd_502885 := by
    simpa [prefixWord, tailWord_502885, baseEnd_502885] using wordTrace_append hprefix tailTrace_502885
  have hstable : (prefixWord ++ tailWord_502885).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_502885).length < 2 ^ (prefixWord ++ tailWord_502885).sum := by decide
  have hdescent : baseEnd_502885 < baseStart_502885 := by decide
  rcases family_descends (prefixWord ++ tailWord_502885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_502998 : List Nat := [5, 2, 1, 2, 2, 1, 3, 1, 4]
def baseStart_502998 : Nat := 118140960795 + 502998 * 2 ^ 59
def prefixEnd_502998 : Nat := 4983230072969 + 3 ^ 40 * 502998 * 2
def baseEnd_502998 : Nat := 114790996555701445205227

theorem tailTrace_502998 : CollatzResearch.WordTrace tailWord_502998 prefixEnd_502998 114790996555701445205227 := by
  unfold tailWord_502998
  simp only [CollatzResearch.WordTrace]
  refine ⟨1146615264483226629015353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 12230562821154417376163765 1146615264483226629015353)
  ·
    refine ⟨859961448362419971761515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1146615264483226629015353 859961448362419971761515)
    ·
      refine ⟨1289942172543629957642273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 859961448362419971761515 1289942172543629957642273)
      ·
        refine ⟨967456629407722468231705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1289942172543629957642273 967456629407722468231705)
        ·
          refine ⟨725592472055791851173779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 967456629407722468231705 725592472055791851173779)
          ·
            refine ⟨1088388708083687776760669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 725592472055791851173779 1088388708083687776760669)
            ·
              refine ⟨408145765531382916285251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1088388708083687776760669 408145765531382916285251)
              ·
                refine ⟨612218648297074374427877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 408145765531382916285251 612218648297074374427877)
                ·
                  refine ⟨114790996555701445205227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 612218648297074374427877 114790996555701445205227)
                  ·
                    rfl

theorem cell21_502998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 3, 1, 4].length) (baseStart_502998 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_502998 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_502998 prefixEnd_502998 := by exact prefixLift 502998
  have htrace : WordTrace (prefixWord ++ tailWord_502998) baseStart_502998 baseEnd_502998 := by
    simpa [prefixWord, tailWord_502998, baseEnd_502998] using wordTrace_append hprefix tailTrace_502998
  have hstable : (prefixWord ++ tailWord_502998).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_502998).length < 2 ^ (prefixWord ++ tailWord_502998).sum := by decide
  have hdescent : baseEnd_502998 < baseStart_502998 := by decide
  rcases family_descends (prefixWord ++ tailWord_502998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_503127 : List Nat := [1, 1, 3, 2, 3, 2, 1, 1, 7]
def baseStart_503127 : Nat := 118140960795 + 503127 * 2 ^ 59
def prefixEnd_503127 : Nat := 4983230072969 + 3 ^ 40 * 503127 * 2
def baseEnd_503127 : Nat := 114820436113225887554963

theorem tailTrace_503127 : CollatzResearch.WordTrace tailWord_503127 prefixEnd_503127 114820436113225887554963 := by
  unfold tailWord_503127
  simp only [CollatzResearch.WordTrace]
  refine ⟨18350549248264281095691635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12233699498842854063794423 18350549248264281095691635)
  ·
    refine ⟨27525823872396421643537453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18350549248264281095691635 27525823872396421643537453)
    ·
      refine ⟨10322183952148658116326545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27525823872396421643537453 10322183952148658116326545)
      ·
        refine ⟨7741637964111493587244909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10322183952148658116326545 7741637964111493587244909)
        ·
          refine ⟨2903114236541810095216841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7741637964111493587244909 2903114236541810095216841)
          ·
            refine ⟨2177335677406357571412631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2903114236541810095216841 2177335677406357571412631)
            ·
              refine ⟨3266003516109536357118947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2177335677406357571412631 3266003516109536357118947)
              ·
                refine ⟨4899005274164304535678421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3266003516109536357118947 4899005274164304535678421)
                ·
                  refine ⟨114820436113225887554963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4899005274164304535678421 114820436113225887554963)
                  ·
                    rfl

theorem cell21_503127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 1, 1, 7].length) (baseStart_503127 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_503127 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_503127 prefixEnd_503127 := by exact prefixLift 503127
  have htrace : WordTrace (prefixWord ++ tailWord_503127) baseStart_503127 baseEnd_503127 := by
    simpa [prefixWord, tailWord_503127, baseEnd_503127] using wordTrace_append hprefix tailTrace_503127
  have hstable : (prefixWord ++ tailWord_503127).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_503127).length < 2 ^ (prefixWord ++ tailWord_503127).sum := by decide
  have hdescent : baseEnd_503127 < baseStart_503127 := by decide
  rcases family_descends (prefixWord ++ tailWord_503127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_503150 : List Nat := [4, 1, 2, 4, 2, 1, 1, 2, 4]
def baseStart_503150 : Nat := 118140960795 + 503150 * 2 ^ 59
def prefixEnd_503150 : Nat := 4983230072969 + 3 ^ 40 * 503150 * 2
def baseEnd_503150 : Nat := 114825685026582958671583

theorem tailTrace_503150 : CollatzResearch.WordTrace tailWord_503150 prefixEnd_503150 114825685026582958671583 := by
  unfold tailWord_503150
  simp only [CollatzResearch.WordTrace]
  refine ⟨2293923515897619502972363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12234258751453970682519269 2293923515897619502972363)
  ·
    refine ⟨3440885273846429254458545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2293923515897619502972363 3440885273846429254458545)
    ·
      refine ⟨2580663955384821940843909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3440885273846429254458545 2580663955384821940843909)
      ·
        refine ⟨483874491634654113908233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2580663955384821940843909 483874491634654113908233)
        ·
          refine ⟨362905868725990585431175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 483874491634654113908233 362905868725990585431175)
          ·
            refine ⟨544358803088985878146763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 362905868725990585431175 544358803088985878146763)
            ·
              refine ⟨816538204633478817220145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 544358803088985878146763 816538204633478817220145)
              ·
                refine ⟨612403653475109112915109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 816538204633478817220145 612403653475109112915109)
                ·
                  refine ⟨114825685026582958671583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 612403653475109112915109 114825685026582958671583)
                  ·
                    rfl

theorem cell21_503150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 2, 1, 1, 2, 4].length) (baseStart_503150 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_503150 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_503150 prefixEnd_503150 := by exact prefixLift 503150
  have htrace : WordTrace (prefixWord ++ tailWord_503150) baseStart_503150 baseEnd_503150 := by
    simpa [prefixWord, tailWord_503150, baseEnd_503150] using wordTrace_append hprefix tailTrace_503150
  have hstable : (prefixWord ++ tailWord_503150).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_503150).length < 2 ^ (prefixWord ++ tailWord_503150).sum := by decide
  have hdescent : baseEnd_503150 < baseStart_503150 := by decide
  rcases family_descends (prefixWord ++ tailWord_503150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_503189 : List Nat := [1, 3, 2, 1, 1, 2, 6, 5]
def baseStart_503189 : Nat := 118140960795 + 503189 * 2 ^ 59
def prefixEnd_503189 : Nat := 4983230072969 + 3 ^ 40 * 503189 * 2
def baseEnd_503189 : Nat := 38278195119309185840501

theorem tailTrace_503189 : CollatzResearch.WordTrace tailWord_503189 prefixEnd_503189 38278195119309185840501 := by
  unfold tailWord_503189
  simp only [CollatzResearch.WordTrace]
  refine ⟨18352810574039665684448621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12235207049359777122965747 18352810574039665684448621)
  ·
    refine ⟨6882303965264874631668233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18352810574039665684448621 6882303965264874631668233)
    ·
      refine ⟨5161727973948655973751175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6882303965264874631668233 5161727973948655973751175)
      ·
        refine ⟨7742591960922983960626763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5161727973948655973751175 7742591960922983960626763)
        ·
          refine ⟨11613887941384475940940145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7742591960922983960626763 11613887941384475940940145)
          ·
            refine ⟨8710415956038356955705109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11613887941384475940940145 8710415956038356955705109)
            ·
              refine ⟨408300747939297982298677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 8710415956038356955705109 408300747939297982298677)
              ·
                refine ⟨38278195119309185840501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 408300747939297982298677 38278195119309185840501)
                ·
                  rfl

theorem cell21_503189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 6, 5].length) (baseStart_503189 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_503189 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_503189 prefixEnd_503189 := by exact prefixLift 503189
  have htrace : WordTrace (prefixWord ++ tailWord_503189) baseStart_503189 baseEnd_503189 := by
    simpa [prefixWord, tailWord_503189, baseEnd_503189] using wordTrace_append hprefix tailTrace_503189
  have hstable : (prefixWord ++ tailWord_503189).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_503189).length < 2 ^ (prefixWord ++ tailWord_503189).sum := by decide
  have hdescent : baseEnd_503189 < baseStart_503189 := by decide
  rcases family_descends (prefixWord ++ tailWord_503189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_503282 : List Nat := [3, 2, 1, 4, 1, 3, 1, 6]
def baseStart_503282 : Nat := 118140960795 + 503282 * 2 ^ 59
def prefixEnd_503282 : Nat := 4983230072969 + 3 ^ 40 * 503282 * 2
def baseEnd_503282 : Nat := 38285269741660020823771

theorem tailTrace_503282 : CollatzResearch.WordTrace tailWord_503282 prefixEnd_503282 38285269741660020823771 := by
  unfold tailWord_503282
  simp only [CollatzResearch.WordTrace]
  refine ⟨4589050640675685641896025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12237468375135161711722733 4589050640675685641896025)
  ·
    refine ⟨3441787980506764231422019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4589050640675685641896025 3441787980506764231422019)
    ·
      refine ⟨5162681970760146347133029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3441787980506764231422019 5162681970760146347133029)
      ·
        refine ⟨968002869517527440087443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5162681970760146347133029 968002869517527440087443)
        ·
          refine ⟨1452004304276291160131165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 968002869517527440087443 1452004304276291160131165)
          ·
            refine ⟨544501614103609185049187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1452004304276291160131165 544501614103609185049187)
            ·
              refine ⟨816752421155413777573781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 544501614103609185049187 816752421155413777573781)
              ·
                refine ⟨38285269741660020823771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 816752421155413777573781 38285269741660020823771)
                ·
                  rfl

theorem cell21_503282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 3, 1, 6].length) (baseStart_503282 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_503282 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_503282 prefixEnd_503282 := by exact prefixLift 503282
  have htrace : WordTrace (prefixWord ++ tailWord_503282) baseStart_503282 baseEnd_503282 := by
    simpa [prefixWord, tailWord_503282, baseEnd_503282] using wordTrace_append hprefix tailTrace_503282
  have hstable : (prefixWord ++ tailWord_503282).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_503282).length < 2 ^ (prefixWord ++ tailWord_503282).sum := by decide
  have hdescent : baseEnd_503282 < baseStart_503282 := by decide
  rcases family_descends (prefixWord ++ tailWord_503282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_503324 : List Nat := [2, 2, 3, 1, 2, 1, 10]
def baseStart_503324 : Nat := 118140960795 + 503324 * 2 ^ 59
def prefixEnd_503324 : Nat := 4983230072969 + 3 ^ 40 * 503324 * 2
def baseEnd_503324 : Nat := 12762821577466369196803

theorem tailTrace_503324 : CollatzResearch.WordTrace tailWord_503324 prefixEnd_503324 12762821577466369196803 := by
  unfold tailWord_503324
  simp only [CollatzResearch.WordTrace]
  refine ⟨9178867214275291870306513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12238489619033722493742017 9178867214275291870306513)
  ·
    refine ⟨6884150410706468902729885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9178867214275291870306513 6884150410706468902729885)
    ·
      refine ⟨2581556404014925838523707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6884150410706468902729885 2581556404014925838523707)
      ·
        refine ⟨3872334606022388757785561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2581556404014925838523707 3872334606022388757785561)
        ·
          refine ⟨2904250954516791568339171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3872334606022388757785561 2904250954516791568339171)
          ·
            refine ⟨4356376431775187352508757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2904250954516791568339171 4356376431775187352508757)
            ·
              refine ⟨12762821577466369196803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 4356376431775187352508757 12762821577466369196803)
              ·
                rfl

theorem cell21_503324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 10].length) (baseStart_503324 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_503324 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_503324 prefixEnd_503324 := by exact prefixLift 503324
  have htrace : WordTrace (prefixWord ++ tailWord_503324) baseStart_503324 baseEnd_503324 := by
    simpa [prefixWord, tailWord_503324, baseEnd_503324] using wordTrace_append hprefix tailTrace_503324
  have hstable : (prefixWord ++ tailWord_503324).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_503324).length < 2 ^ (prefixWord ++ tailWord_503324).sum := by decide
  have hdescent : baseEnd_503324 < baseStart_503324 := by decide
  rcases family_descends (prefixWord ++ tailWord_503324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_503445 : List Nat := [1, 3, 2, 1, 1, 1, 1, 5, 6]
def baseStart_503445 : Nat := 118140960795 + 503445 * 2 ^ 59
def prefixEnd_503445 : Nat := 4983230072969 + 3 ^ 40 * 503445 * 2
def baseEnd_503445 : Nat := 114893008045728001254313

theorem tailTrace_503445 : CollatzResearch.WordTrace tailWord_503445 prefixEnd_503445 114893008045728001254313 := by
  unfold tailWord_503445
  simp only [CollatzResearch.WordTrace]
  refine ⟨18362147661112221405767789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12241431774074814270511859 18362147661112221405767789)
  ·
    refine ⟨6885805372917083027162921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18362147661112221405767789 6885805372917083027162921)
    ·
      refine ⟨5164354029687812270372191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6885805372917083027162921 5164354029687812270372191)
      ·
        refine ⟨7746531044531718405558287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5164354029687812270372191 7746531044531718405558287)
        ·
          refine ⟨11619796566797577608337431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7746531044531718405558287 11619796566797577608337431)
          ·
            refine ⟨17429694850196366412506147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11619796566797577608337431 17429694850196366412506147)
            ·
              refine ⟨26144542275294549618759221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17429694850196366412506147 26144542275294549618759221)
              ·
                refine ⟨2451050838308864026758677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26144542275294549618759221 2451050838308864026758677)
                ·
                  refine ⟨114893008045728001254313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2451050838308864026758677 114893008045728001254313)
                  ·
                    rfl

theorem cell21_503445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 5, 6].length) (baseStart_503445 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_503445 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_503445 prefixEnd_503445 := by exact prefixLift 503445
  have htrace : WordTrace (prefixWord ++ tailWord_503445) baseStart_503445 baseEnd_503445 := by
    simpa [prefixWord, tailWord_503445, baseEnd_503445] using wordTrace_append hprefix tailTrace_503445
  have hstable : (prefixWord ++ tailWord_503445).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_503445).length < 2 ^ (prefixWord ++ tailWord_503445).sum := by decide
  have hdescent : baseEnd_503445 < baseStart_503445 := by decide
  rcases family_descends (prefixWord ++ tailWord_503445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_503527 : List Nat := [1, 1, 5, 4, 1, 2, 2, 5]
def baseStart_503527 : Nat := 118140960795 + 503527 * 2 ^ 59
def prefixEnd_503527 : Nat := 4983230072969 + 3 ^ 40 * 503527 * 2
def baseEnd_503527 : Nat := 38303907187638026962493

theorem tailTrace_503527 : CollatzResearch.WordTrace tailWord_503527 prefixEnd_503527 38303907187638026962493 := by
  unfold tailWord_503527
  simp only [CollatzResearch.WordTrace]
  refine ⟨18365138446815149410252835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12243425631210099606835223 18365138446815149410252835)
  ·
    refine ⟨27547707670222724115379253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18365138446815149410252835 27547707670222724115379253)
    ·
      refine ⟨2582597594083380385816805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 27547707670222724115379253 2582597594083380385816805)
      ·
        refine ⟨484237048890633822340651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2582597594083380385816805 484237048890633822340651)
        ·
          refine ⟨726355573335950733510977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 484237048890633822340651 726355573335950733510977)
          ·
            refine ⟨544766680001963050133233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 726355573335950733510977 544766680001963050133233)
            ·
              refine ⟨408575010001472287599925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 544766680001963050133233 408575010001472287599925)
              ·
                refine ⟨38303907187638026962493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 408575010001472287599925 38303907187638026962493)
                ·
                  rfl

theorem cell21_503527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 2, 2, 5].length) (baseStart_503527 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_503527 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_503527 prefixEnd_503527 := by exact prefixLift 503527
  have htrace : WordTrace (prefixWord ++ tailWord_503527) baseStart_503527 baseEnd_503527 := by
    simpa [prefixWord, tailWord_503527, baseEnd_503527] using wordTrace_append hprefix tailTrace_503527
  have hstable : (prefixWord ++ tailWord_503527).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_503527).length < 2 ^ (prefixWord ++ tailWord_503527).sum := by decide
  have hdescent : baseEnd_503527 < baseStart_503527 := by decide
  rcases family_descends (prefixWord ++ tailWord_503527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_503673 : List Nat := [1, 2, 1, 3, 2, 2, 3, 1, 6]
def baseStart_503673 : Nat := 118140960795 + 503673 * 2 ^ 59
def prefixEnd_503673 : Nat := 4983230072969 + 3 ^ 40 * 503673 * 2
def baseEnd_503673 : Nat := 114945040752050271453847

theorem tailTrace_503673 : CollatzResearch.WordTrace tailWord_503673 prefixEnd_503673 114945040752050271453847 := by
  unfold tailWord_503673
  simp only [CollatzResearch.WordTrace]
  refine ⟨18370463504286216345067673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12246975669524144230045115 18370463504286216345067673)
  ·
    refine ⟨13777847628214662258800755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18370463504286216345067673 13777847628214662258800755)
    ·
      refine ⟨20666771442321993388201133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13777847628214662258800755 20666771442321993388201133)
      ·
        refine ⟨7750039290870747520575425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20666771442321993388201133 7750039290870747520575425)
        ·
          refine ⟨5812529468153060640431569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7750039290870747520575425 5812529468153060640431569)
          ·
            refine ⟨4359397101114795480323677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5812529468153060640431569 4359397101114795480323677)
            ·
              refine ⟨1634773912918048305121379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4359397101114795480323677 1634773912918048305121379)
              ·
                refine ⟨2452160869377072457682069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1634773912918048305121379 2452160869377072457682069)
                ·
                  refine ⟨114945040752050271453847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2452160869377072457682069 114945040752050271453847)
                  ·
                    rfl

theorem cell21_503673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 3, 1, 6].length) (baseStart_503673 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_503673 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_503673 prefixEnd_503673 := by exact prefixLift 503673
  have htrace : WordTrace (prefixWord ++ tailWord_503673) baseStart_503673 baseEnd_503673 := by
    simpa [prefixWord, tailWord_503673, baseEnd_503673] using wordTrace_append hprefix tailTrace_503673
  have hstable : (prefixWord ++ tailWord_503673).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_503673).length < 2 ^ (prefixWord ++ tailWord_503673).sum := by decide
  have hdescent : baseEnd_503673 < baseStart_503673 := by decide
  rcases family_descends (prefixWord ++ tailWord_503673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_503783 : List Nat := [1, 1, 5, 2, 3, 1, 2, 2, 4]
def baseStart_503783 : Nat := 118140960795 + 503783 * 2 ^ 59
def prefixEnd_503783 : Nat := 4983230072969 + 3 ^ 40 * 503783 * 2
def baseEnd_503783 : Nat := 114970144250714524620289

theorem tailTrace_503783 : CollatzResearch.WordTrace tailWord_503783 prefixEnd_503783 114970144250714524620289 := by
  unfold tailWord_503783
  simp only [CollatzResearch.WordTrace]
  refine ⟨18374475533887705131572003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12249650355925136754381335 18374475533887705131572003)
  ·
    refine ⟨27561713300831557697358005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18374475533887705131572003 27561713300831557697358005)
    ·
      refine ⟨2583910621952958534127313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 27561713300831557697358005 2583910621952958534127313)
      ·
        refine ⟨1937932966464718900595485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2583910621952958534127313 1937932966464718900595485)
        ·
          refine ⟨726724862424269587723307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1937932966464718900595485 726724862424269587723307)
          ·
            refine ⟨1090087293636404381584961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 726724862424269587723307 1090087293636404381584961)
            ·
              refine ⟨817565470227303286188721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1090087293636404381584961 817565470227303286188721)
              ·
                refine ⟨613174102670477464641541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 817565470227303286188721 613174102670477464641541)
                ·
                  refine ⟨114970144250714524620289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 613174102670477464641541 114970144250714524620289)
                  ·
                    rfl

theorem cell21_503783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 2, 2, 4].length) (baseStart_503783 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_503783 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_503783 prefixEnd_503783 := by exact prefixLift 503783
  have htrace : WordTrace (prefixWord ++ tailWord_503783) baseStart_503783 baseEnd_503783 := by
    simpa [prefixWord, tailWord_503783, baseEnd_503783] using wordTrace_append hprefix tailTrace_503783
  have hstable : (prefixWord ++ tailWord_503783).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_503783).length < 2 ^ (prefixWord ++ tailWord_503783).sum := by decide
  have hdescent : baseEnd_503783 < baseStart_503783 := by decide
  rcases family_descends (prefixWord ++ tailWord_503783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_503839 : List Nat := [1, 1, 2, 4, 1, 2, 10]
def baseStart_503839 : Nat := 118140960795 + 503839 * 2 ^ 59
def prefixEnd_503839 : Nat := 4983230072969 + 3 ^ 40 * 503839 * 2
def baseEnd_503839 : Nat := 12775880468185652409649

theorem tailTrace_503839 : CollatzResearch.WordTrace tailWord_503839 prefixEnd_503839 12775880468185652409649 := by
  unfold tailWord_503839
  simp only [CollatzResearch.WordTrace]
  refine ⟨18376518021684826695610571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12251012014456551130407047 18376518021684826695610571)
  ·
    refine ⟨27564777032527240043415857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18376518021684826695610571 27564777032527240043415857)
    ·
      refine ⟨20673582774395430032561893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27564777032527240043415857 20673582774395430032561893)
      ·
        refine ⟨3876296770199143131105355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20673582774395430032561893 3876296770199143131105355)
        ·
          refine ⟨5814445155298714696658033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3876296770199143131105355 5814445155298714696658033)
          ·
            refine ⟨4360833866474036022493525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5814445155298714696658033 4360833866474036022493525)
            ·
              refine ⟨12775880468185652409649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 4360833866474036022493525 12775880468185652409649)
              ·
                rfl

theorem cell21_503839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 10].length) (baseStart_503839 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_503839 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_503839 prefixEnd_503839 := by exact prefixLift 503839
  have htrace : WordTrace (prefixWord ++ tailWord_503839) baseStart_503839 baseEnd_503839 := by
    simpa [prefixWord, tailWord_503839, baseEnd_503839] using wordTrace_append hprefix tailTrace_503839
  have hstable : (prefixWord ++ tailWord_503839).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_503839).length < 2 ^ (prefixWord ++ tailWord_503839).sum := by decide
  have hdescent : baseEnd_503839 < baseStart_503839 := by decide
  rcases family_descends (prefixWord ++ tailWord_503839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_503873 : List Nat := [1, 2, 5, 1, 2, 1, 4, 5]
def baseStart_503873 : Nat := 118140960795 + 503873 * 2 ^ 59
def prefixEnd_503873 : Nat := 4983230072969 + 3 ^ 40 * 503873 * 2
def baseEnd_503873 : Nat := 38330227825631456040035

theorem tailTrace_503873 : CollatzResearch.WordTrace tailWord_503873 prefixEnd_503873 38330227825631456040035 := by
  unfold tailWord_503873
  simp only [CollatzResearch.WordTrace]
  refine ⟨18377758103561650502348273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12251838735707767001565515 18377758103561650502348273)
  ·
    refine ⟨13783318577671237876761205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18377758103561650502348273 13783318577671237876761205)
    ·
      refine ⟨1292186116656678550946363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 13783318577671237876761205 1292186116656678550946363)
      ·
        refine ⟨1938279174985017826419545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1292186116656678550946363 1938279174985017826419545)
        ·
          refine ⟨1453709381238763369814659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1938279174985017826419545 1453709381238763369814659)
          ·
            refine ⟨2180564071858145054721989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1453709381238763369814659 2180564071858145054721989)
            ·
              refine ⟨408855763473402197760373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2180564071858145054721989 408855763473402197760373)
              ·
                refine ⟨38330227825631456040035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 408855763473402197760373 38330227825631456040035)
                ·
                  rfl

theorem cell21_503873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 4, 5].length) (baseStart_503873 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_503873 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_503873 prefixEnd_503873 := by exact prefixLift 503873
  have htrace : WordTrace (prefixWord ++ tailWord_503873) baseStart_503873 baseEnd_503873 := by
    simpa [prefixWord, tailWord_503873, baseEnd_503873] using wordTrace_append hprefix tailTrace_503873
  have hstable : (prefixWord ++ tailWord_503873).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_503873).length < 2 ^ (prefixWord ++ tailWord_503873).sum := by decide
  have hdescent : baseEnd_503873 < baseStart_503873 := by decide
  rcases family_descends (prefixWord ++ tailWord_503873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_503918 : List Nat := [4, 1, 2, 2, 1, 1, 3, 3, 4]
def baseStart_503918 : Nat := 118140960795 + 503918 * 2 ^ 59
def prefixEnd_503918 : Nat := 4983230072969 + 3 ^ 40 * 503918 * 2
def baseEnd_503918 : Nat := 115000953089984289870013

theorem tailTrace_503918 : CollatzResearch.WordTrace tailWord_503918 prefixEnd_503918 115000953089984289870013 := by
  unfold tailWord_503918
  simp only [CollatzResearch.WordTrace]
  refine ⟨2297424923549827898467051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12252932925599082125157605 2297424923549827898467051)
  ·
    refine ⟨3446137385324741847700577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2297424923549827898467051 3446137385324741847700577)
    ·
      refine ⟨2584603038993556385775433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3446137385324741847700577 2584603038993556385775433)
      ·
        refine ⟨1938452279245167289331575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2584603038993556385775433 1938452279245167289331575)
        ·
          refine ⟨2907678418867750933997363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1938452279245167289331575 2907678418867750933997363)
          ·
            refine ⟨4361517628301626400996045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2907678418867750933997363 4361517628301626400996045)
            ·
              refine ⟨1635569110613109900373517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4361517628301626400996045 1635569110613109900373517)
              ·
                refine ⟨613338416479916212640069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1635569110613109900373517 613338416479916212640069)
                ·
                  refine ⟨115000953089984289870013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 613338416479916212640069 115000953089984289870013)
                  ·
                    rfl

theorem cell21_503918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 3, 3, 4].length) (baseStart_503918 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_503918 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_503918 prefixEnd_503918 := by exact prefixLift 503918
  have htrace : WordTrace (prefixWord ++ tailWord_503918) baseStart_503918 baseEnd_503918 := by
    simpa [prefixWord, tailWord_503918, baseEnd_503918] using wordTrace_append hprefix tailTrace_503918
  have hstable : (prefixWord ++ tailWord_503918).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_503918).length < 2 ^ (prefixWord ++ tailWord_503918).sum := by decide
  have hdescent : baseEnd_503918 < baseStart_503918 := by decide
  rcases family_descends (prefixWord ++ tailWord_503918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_503966 : List Nat := [4, 3, 1, 1, 3, 2, 1, 6]
def baseStart_503966 : Nat := 118140960795 + 503966 * 2 ^ 59
def prefixEnd_503966 : Nat := 4983230072969 + 3 ^ 40 * 503966 * 2
def baseEnd_503966 : Nat := 38337302447982291023305

theorem tailTrace_503966 : CollatzResearch.WordTrace tailWord_503966 prefixEnd_503966 38337302447982291023305 := by
  unfold tailWord_503966
  simp only [CollatzResearch.WordTrace]
  refine ⟨2297643761528090923185469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12254100061483151590322501 2297643761528090923185469)
  ·
    refine ⟨861616410573034096194551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2297643761528090923185469 861616410573034096194551)
    ·
      refine ⟨1292424615859551144291827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 861616410573034096194551 1292424615859551144291827)
      ·
        refine ⟨1938636923789326716437741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1292424615859551144291827 1938636923789326716437741)
        ·
          refine ⟨726988846420997518664153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1938636923789326716437741 726988846420997518664153)
          ·
            refine ⟨545241634815748138998115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 726988846420997518664153 545241634815748138998115)
            ·
              refine ⟨817862452223622208497173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 545241634815748138998115 817862452223622208497173)
              ·
                refine ⟨38337302447982291023305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 817862452223622208497173 38337302447982291023305)
                ·
                  rfl

theorem cell21_503966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 2, 1, 6].length) (baseStart_503966 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_503966 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_503966 prefixEnd_503966 := by exact prefixLift 503966
  have htrace : WordTrace (prefixWord ++ tailWord_503966) baseStart_503966 baseEnd_503966 := by
    simpa [prefixWord, tailWord_503966, baseEnd_503966] using wordTrace_append hprefix tailTrace_503966
  have hstable : (prefixWord ++ tailWord_503966).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_503966).length < 2 ^ (prefixWord ++ tailWord_503966).sum := by decide
  have hdescent : baseEnd_503966 < baseStart_503966 := by decide
  rcases family_descends (prefixWord ++ tailWord_503966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_504039 : List Nat := [1, 1, 5, 3, 1, 1, 2, 2, 5]
def baseStart_504039 : Nat := 118140960795 + 504039 * 2 ^ 59
def prefixEnd_504039 : Nat := 4983230072969 + 3 ^ 40 * 504039 * 2
def baseEnd_504039 : Nat := 115028566938514968353099

theorem tailTrace_504039 : CollatzResearch.WordTrace tailWord_504039 prefixEnd_504039 115028566938514968353099 := by
  unfold tailWord_504039
  simp only [CollatzResearch.WordTrace]
  refine ⟨18383812620960260852891171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12255875080640173901927447 18383812620960260852891171)
  ·
    refine ⟨27575718931440391279336757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18383812620960260852891171 27575718931440391279336757)
    ·
      refine ⟨2585223649822536682437821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 27575718931440391279336757 2585223649822536682437821)
      ·
        refine ⟨969458868683451255914183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2585223649822536682437821 969458868683451255914183)
        ·
          refine ⟨1454188303025176883871275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 969458868683451255914183 1454188303025176883871275)
          ·
            refine ⟨2181282454537765325806913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1454188303025176883871275 2181282454537765325806913)
            ·
              refine ⟨1635961840903323994355185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2181282454537765325806913 1635961840903323994355185)
              ·
                refine ⟨1226971380677492995766389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1635961840903323994355185 1226971380677492995766389)
                ·
                  refine ⟨115028566938514968353099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1226971380677492995766389 115028566938514968353099)
                  ·
                    rfl

theorem cell21_504039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 2, 2, 5].length) (baseStart_504039 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_504039 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_504039 prefixEnd_504039 := by exact prefixLift 504039
  have htrace : WordTrace (prefixWord ++ tailWord_504039) baseStart_504039 baseEnd_504039 := by
    simpa [prefixWord, tailWord_504039, baseEnd_504039] using wordTrace_append hprefix tailTrace_504039
  have hstable : (prefixWord ++ tailWord_504039).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_504039).length < 2 ^ (prefixWord ++ tailWord_504039).sum := by decide
  have hdescent : baseEnd_504039 < baseStart_504039 := by decide
  rcases family_descends (prefixWord ++ tailWord_504039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_504087 : List Nat := [1, 1, 3, 4, 1, 4, 2, 1, 4]
def baseStart_504087 : Nat := 118140960795 + 504087 * 2 ^ 59
def prefixEnd_504087 : Nat := 4983230072969 + 3 ^ 40 * 504087 * 2
def baseEnd_504087 : Nat := 115039521192477551553001

theorem tailTrace_504087 : CollatzResearch.WordTrace tailWord_504087 prefixEnd_504087 115039521192477551553001 := by
  unfold tailWord_504087
  simp only [CollatzResearch.WordTrace]
  refine ⟨18385563324786365050638515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12257042216524243367092343 18385563324786365050638515)
  ·
    refine ⟨27578344987179547575957773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18385563324786365050638515 27578344987179547575957773)
    ·
      refine ⟨10341879370192330340984165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27578344987179547575957773 10341879370192330340984165)
      ·
        refine ⟨1939102381911061938934531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10341879370192330340984165 1939102381911061938934531)
        ·
          refine ⟨2908653572866592908401797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1939102381911061938934531 2908653572866592908401797)
          ·
            refine ⟨545372544912486170325337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2908653572866592908401797 545372544912486170325337)
            ·
              refine ⟨409029408684364627744003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 545372544912486170325337 409029408684364627744003)
              ·
                refine ⟨613544113026546941616005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 409029408684364627744003 613544113026546941616005)
                ·
                  refine ⟨115039521192477551553001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 613544113026546941616005 115039521192477551553001)
                  ·
                    rfl

theorem cell21_504087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 4, 2, 1, 4].length) (baseStart_504087 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_504087 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_504087 prefixEnd_504087 := by exact prefixLift 504087
  have htrace : WordTrace (prefixWord ++ tailWord_504087) baseStart_504087 baseEnd_504087 := by
    simpa [prefixWord, tailWord_504087, baseEnd_504087] using wordTrace_append hprefix tailTrace_504087
  have hstable : (prefixWord ++ tailWord_504087).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_504087).length < 2 ^ (prefixWord ++ tailWord_504087).sum := by decide
  have hdescent : baseEnd_504087 < baseStart_504087 := by decide
  rcases family_descends (prefixWord ++ tailWord_504087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_504112 : List Nat := [2, 1, 1, 1, 2, 2, 2, 4, 6]
def baseStart_504112 : Nat := 118140960795 + 504112 * 2 ^ 59
def prefixEnd_504112 : Nat := 4983230072969 + 3 ^ 40 * 504112 * 2
def baseEnd_504112 : Nat := 115045226533083063636283

theorem tailTrace_504112 : CollatzResearch.WordTrace tailWord_504112 prefixEnd_504112 115045226533083063636283 := by
  unfold tailWord_504112
  simp only [CollatzResearch.WordTrace]
  refine ⟨9193237574847897160149295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12257650099797196213532393 9193237574847897160149295)
  ·
    refine ⟨13789856362271845740223943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9193237574847897160149295 13789856362271845740223943)
    ·
      refine ⟨20684784543407768610335915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13789856362271845740223943 20684784543407768610335915)
      ·
        refine ⟨31027176815111652915503873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20684784543407768610335915 31027176815111652915503873)
        ·
          refine ⟨23270382611333739686627905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31027176815111652915503873 23270382611333739686627905)
          ·
            refine ⟨17452786958500304764970929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23270382611333739686627905 17452786958500304764970929)
            ·
              refine ⟨13089590218875228573728197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17452786958500304764970929 13089590218875228573728197)
              ·
                refine ⟨2454298166039105357574037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13089590218875228573728197 2454298166039105357574037)
                ·
                  refine ⟨115045226533083063636283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2454298166039105357574037 115045226533083063636283)
                  ·
                    rfl

theorem cell21_504112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 4, 6].length) (baseStart_504112 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_504112 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_504112 prefixEnd_504112 := by exact prefixLift 504112
  have htrace : WordTrace (prefixWord ++ tailWord_504112) baseStart_504112 baseEnd_504112 := by
    simpa [prefixWord, tailWord_504112, baseEnd_504112] using wordTrace_append hprefix tailTrace_504112
  have hstable : (prefixWord ++ tailWord_504112).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_504112).length < 2 ^ (prefixWord ++ tailWord_504112).sum := by decide
  have hdescent : baseEnd_504112 < baseStart_504112 := by decide
  rcases family_descends (prefixWord ++ tailWord_504112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_504115 : List Nat := [1, 1, 1, 2, 5, 1, 2, 5, 3]
def baseStart_504115 : Nat := 118140960795 + 504115 * 2 ^ 59
def prefixEnd_504115 : Nat := 4983230072969 + 3 ^ 40 * 504115 * 2
def baseEnd_504115 : Nat := 115045911173955725086277

theorem tailTrace_504115 : CollatzResearch.WordTrace tailWord_504115 prefixEnd_504115 115045911173955725086277 := by
  unfold tailWord_504115
  simp only [CollatzResearch.WordTrace]
  refine ⟨18386584568684925832657799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12257723045789950555105199 18386584568684925832657799)
  ·
    refine ⟨27579876853027388748986699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18386584568684925832657799 27579876853027388748986699)
    ·
      refine ⟨41369815279541083123480049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27579876853027388748986699 41369815279541083123480049)
      ·
        refine ⟨31027361459655812342610037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41369815279541083123480049 31027361459655812342610037)
        ·
          refine ⟨2908815136842732407119691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 31027361459655812342610037 2908815136842732407119691)
          ·
            refine ⟨4363222705264098610679537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2908815136842732407119691 4363222705264098610679537)
            ·
              refine ⟨3272417028948073958009653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4363222705264098610679537 3272417028948073958009653)
              ·
                refine ⟨306789096463881933563405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3272417028948073958009653 306789096463881933563405)
                ·
                  refine ⟨115045911173955725086277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 306789096463881933563405 115045911173955725086277)
                  ·
                    rfl

theorem cell21_504115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 2, 5, 3].length) (baseStart_504115 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_504115 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_504115 prefixEnd_504115 := by exact prefixLift 504115
  have htrace : WordTrace (prefixWord ++ tailWord_504115) baseStart_504115 baseEnd_504115 := by
    simpa [prefixWord, tailWord_504115, baseEnd_504115] using wordTrace_append hprefix tailTrace_504115
  have hstable : (prefixWord ++ tailWord_504115).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_504115).length < 2 ^ (prefixWord ++ tailWord_504115).sum := by decide
  have hdescent : baseEnd_504115 < baseStart_504115 := by decide
  rcases family_descends (prefixWord ++ tailWord_504115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_504222 : List Nat := [4, 3, 1, 2, 1, 1, 1, 2, 6]
def baseStart_504222 : Nat := 118140960795 + 504222 * 2 ^ 59
def prefixEnd_504222 : Nat := 4983230072969 + 3 ^ 40 * 504222 * 2
def baseEnd_504222 : Nat := 115070330031747316802725

theorem tailTrace_504222 : CollatzResearch.WordTrace tailWord_504222 prefixEnd_504222 115070330031747316802725 := by
  unfold tailWord_504222
  simp only [CollatzResearch.WordTrace]
  refine ⟨2298810897412160388350365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12260324786198188737868613 2298810897412160388350365)
  ·
    refine ⟨862054086529560145631387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2298810897412160388350365 862054086529560145631387)
    ·
      refine ⟨1293081129794340218447081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 862054086529560145631387 1293081129794340218447081)
      ·
        refine ⟨969810847345755163835311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1293081129794340218447081 969810847345755163835311)
        ·
          refine ⟨1454716271018632745752967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 969810847345755163835311 1454716271018632745752967)
          ·
            refine ⟨2182074406527949118629451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1454716271018632745752967 2182074406527949118629451)
            ·
              refine ⟨3273111609791923677944177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2182074406527949118629451 3273111609791923677944177)
              ·
                refine ⟨2454833707343942758458133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3273111609791923677944177 2454833707343942758458133)
                ·
                  refine ⟨115070330031747316802725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2454833707343942758458133 115070330031747316802725)
                  ·
                    rfl

theorem cell21_504222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 1, 2, 6].length) (baseStart_504222 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_504222 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_504222 prefixEnd_504222 := by exact prefixLift 504222
  have htrace : WordTrace (prefixWord ++ tailWord_504222) baseStart_504222 baseEnd_504222 := by
    simpa [prefixWord, tailWord_504222, baseEnd_504222] using wordTrace_append hprefix tailTrace_504222
  have hstable : (prefixWord ++ tailWord_504222).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_504222).length < 2 ^ (prefixWord ++ tailWord_504222).sum := by decide
  have hdescent : baseEnd_504222 < baseStart_504222 := by decide
  rcases family_descends (prefixWord ++ tailWord_504222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_504233 : List Nat := [1, 2, 1, 1, 1, 1, 3, 4, 7]
def baseStart_504233 : Nat := 118140960795 + 504233 * 2 ^ 59
def prefixEnd_504233 : Nat := 4983230072969 + 3 ^ 40 * 504233 * 2
def baseEnd_504233 : Nat := 115072840381613742119369

theorem tailTrace_504233 : CollatzResearch.WordTrace tailWord_504233 prefixEnd_504233 115072840381613742119369 := by
  unfold tailWord_504233
  simp only [CollatzResearch.WordTrace]
  refine ⟨18390888382257431985453353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12260592254838287990302235 18390888382257431985453353)
  ·
    refine ⟨13793166286693073989090015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18390888382257431985453353 13793166286693073989090015)
    ·
      refine ⟨20689749430039610983635023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13793166286693073989090015 20689749430039610983635023)
      ·
        refine ⟨31034624145059416475452535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20689749430039610983635023 31034624145059416475452535)
        ·
          refine ⟨46551936217589124713178803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31034624145059416475452535 46551936217589124713178803)
          ·
            refine ⟨69827904326383687069768205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46551936217589124713178803 69827904326383687069768205)
            ·
              refine ⟨26185464122393882651163077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69827904326383687069768205 26185464122393882651163077)
              ·
                refine ⟨4909774522948852997093077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26185464122393882651163077 4909774522948852997093077)
                ·
                  refine ⟨115072840381613742119369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4909774522948852997093077 115072840381613742119369)
                  ·
                    rfl

theorem cell21_504233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 4, 7].length) (baseStart_504233 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_504233 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_504233 prefixEnd_504233 := by exact prefixLift 504233
  have htrace : WordTrace (prefixWord ++ tailWord_504233) baseStart_504233 baseEnd_504233 := by
    simpa [prefixWord, tailWord_504233, baseEnd_504233] using wordTrace_append hprefix tailTrace_504233
  have hstable : (prefixWord ++ tailWord_504233).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_504233).length < 2 ^ (prefixWord ++ tailWord_504233).sum := by decide
  have hdescent : baseEnd_504233 < baseStart_504233 := by decide
  rcases family_descends (prefixWord ++ tailWord_504233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_504298 : List Nat := [3, 1, 3, 1, 3, 2, 2, 2, 4]
def baseStart_504298 : Nat := 118140960795 + 504298 * 2 ^ 59
def prefixEnd_504298 : Nat := 4983230072969 + 3 ^ 40 * 504298 * 2
def baseEnd_504298 : Nat := 115087674267188073535903

theorem tailTrace_504298 : CollatzResearch.WordTrace tailWord_504298 prefixEnd_504298 115087674267188073535903 := by
  unfold tailWord_504298
  simp only [CollatzResearch.WordTrace]
  refine ⟨4598314781755487021642387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12262172751347965391046365 4598314781755487021642387)
  ·
    refine ⟨6897472172633230532463581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4598314781755487021642387 6897472172633230532463581)
    ·
      refine ⟨2586552064737461449673843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6897472172633230532463581 2586552064737461449673843)
      ·
        refine ⟨3879828097106192174510765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2586552064737461449673843 3879828097106192174510765)
        ·
          refine ⟨1454935536414822065441537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3879828097106192174510765 1454935536414822065441537)
          ·
            refine ⟨1091201652311116549081153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1454935536414822065441537 1091201652311116549081153)
            ·
              refine ⟨818401239233337411810865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1091201652311116549081153 818401239233337411810865)
              ·
                refine ⟨613800929425003058858149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 818401239233337411810865 613800929425003058858149)
                ·
                  refine ⟨115087674267188073535903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 613800929425003058858149 115087674267188073535903)
                  ·
                    rfl

theorem cell21_504298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 2, 2, 4].length) (baseStart_504298 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_504298 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_504298 prefixEnd_504298 := by exact prefixLift 504298
  have htrace : WordTrace (prefixWord ++ tailWord_504298) baseStart_504298 baseEnd_504298 := by
    simpa [prefixWord, tailWord_504298, baseEnd_504298] using wordTrace_append hprefix tailTrace_504298
  have hstable : (prefixWord ++ tailWord_504298).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_504298).length < 2 ^ (prefixWord ++ tailWord_504298).sum := by decide
  have hdescent : baseEnd_504298 < baseStart_504298 := by decide
  rcases family_descends (prefixWord ++ tailWord_504298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_504301 : List Nat := [1, 5, 1, 3, 1, 1, 4, 2, 3]
def baseStart_504301 : Nat := 118140960795 + 504301 * 2 ^ 59
def prefixEnd_504301 : Nat := 4983230072969 + 3 ^ 40 * 504301 * 2
def baseEnd_504301 : Nat := 115088358908060734985897

theorem tailTrace_504301 : CollatzResearch.WordTrace tailWord_504301 prefixEnd_504301 115088358908060734985897 := by
  unfold tailWord_504301
  simp only [CollatzResearch.WordTrace]
  refine ⟨18393368546011079598928757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12262245697340719732619171 18393368546011079598928757)
  ·
    refine ⟨1724378301188538712399571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 18393368546011079598928757 1724378301188538712399571)
    ·
      refine ⟨2586567451782808068599357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1724378301188538712399571 2586567451782808068599357)
      ·
        refine ⟨969962794418553025724759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2586567451782808068599357 969962794418553025724759)
        ·
          refine ⟨1454944191627829538587139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 969962794418553025724759 1454944191627829538587139)
          ·
            refine ⟨2182416287441744307880709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1454944191627829538587139 2182416287441744307880709)
            ·
              refine ⟨409203053895327057727633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2182416287441744307880709 409203053895327057727633)
              ·
                refine ⟨306902290421495293295725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 409203053895327057727633 306902290421495293295725)
                ·
                  refine ⟨115088358908060734985897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 306902290421495293295725 115088358908060734985897)
                  ·
                    rfl

theorem cell21_504301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 4, 2, 3].length) (baseStart_504301 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_504301 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_504301 prefixEnd_504301 := by exact prefixLift 504301
  have htrace : WordTrace (prefixWord ++ tailWord_504301) baseStart_504301 baseEnd_504301 := by
    simpa [prefixWord, tailWord_504301, baseEnd_504301] using wordTrace_append hprefix tailTrace_504301
  have hstable : (prefixWord ++ tailWord_504301).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_504301).length < 2 ^ (prefixWord ++ tailWord_504301).sum := by decide
  have hdescent : baseEnd_504301 < baseStart_504301 := by decide
  rcases family_descends (prefixWord ++ tailWord_504301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_504357 : List Nat := [1, 3, 1, 2, 2, 1, 5, 2, 4]
def baseStart_504357 : Nat := 118140960795 + 504357 * 2 ^ 59
def prefixEnd_504357 : Nat := 4983230072969 + 3 ^ 40 * 504357 * 2
def baseEnd_504357 : Nat := 115101138871017082052449

theorem tailTrace_504357 : CollatzResearch.WordTrace tailWord_504357 prefixEnd_504357 115101138871017082052449 := by
  unfold tailWord_504357
  simp only [CollatzResearch.WordTrace]
  refine ⟨18395411033808201162967325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12263607355872134108644883 18395411033808201162967325)
  ·
    refine ⟨6898279137678075436112747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18395411033808201162967325 6898279137678075436112747)
    ·
      refine ⟨10347418706517113154169121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6898279137678075436112747 10347418706517113154169121)
      ·
        refine ⟨7760564029887834865626841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10347418706517113154169121 7760564029887834865626841)
        ·
          refine ⟨5820423022415876149220131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7760564029887834865626841 5820423022415876149220131)
          ·
            refine ⟨8730634533623814223830197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5820423022415876149220131 8730634533623814223830197)
            ·
              refine ⟨818496987527232583484081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8730634533623814223830197 818496987527232583484081)
              ·
                refine ⟨613872740645424437613061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 818496987527232583484081 613872740645424437613061)
                ·
                  refine ⟨115101138871017082052449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 613872740645424437613061 115101138871017082052449)
                  ·
                    rfl

theorem cell21_504357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 5, 2, 4].length) (baseStart_504357 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_504357 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_504357 prefixEnd_504357 := by exact prefixLift 504357
  have htrace : WordTrace (prefixWord ++ tailWord_504357) baseStart_504357 baseEnd_504357 := by
    simpa [prefixWord, tailWord_504357, baseEnd_504357] using wordTrace_append hprefix tailTrace_504357
  have hstable : (prefixWord ++ tailWord_504357).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_504357).length < 2 ^ (prefixWord ++ tailWord_504357).sum := by decide
  have hdescent : baseEnd_504357 < baseStart_504357 := by decide
  rcases family_descends (prefixWord ++ tailWord_504357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_504360 : List Nat := [2, 1, 5, 2, 1, 1, 2, 4, 3]
def baseStart_504360 : Nat := 118140960795 + 504360 * 2 ^ 59
def prefixEnd_504360 : Nat := 4983230072969 + 3 ^ 40 * 504360 * 2
def baseEnd_504360 : Nat := 115101823511889743502443

theorem tailTrace_504360 : CollatzResearch.WordTrace tailWord_504360 prefixEnd_504360 115101823511889743502443 := by
  unfold tailWord_504360
  simp only [CollatzResearch.WordTrace]
  refine ⟨9197760226398666337663267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12263680301864888450217689 9197760226398666337663267)
  ·
    refine ⟨13796640339597999506494901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9197760226398666337663267 13796640339597999506494901)
    ·
      refine ⟨1293435031837312453733897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 13796640339597999506494901 1293435031837312453733897)
      ·
        refine ⟨970076273877984340300423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1293435031837312453733897 970076273877984340300423)
        ·
          refine ⟨1455114410816976510450635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 970076273877984340300423 1455114410816976510450635)
          ·
            refine ⟨2182671616225464765675953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1455114410816976510450635 2182671616225464765675953)
            ·
              refine ⟨1637003712169098574256965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2182671616225464765675953 1637003712169098574256965)
              ·
                refine ⟨306938196031705982673181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1637003712169098574256965 306938196031705982673181)
                ·
                  refine ⟨115101823511889743502443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 306938196031705982673181 115101823511889743502443)
                  ·
                    rfl

theorem cell21_504360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 2, 4, 3].length) (baseStart_504360 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_504360 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_504360 prefixEnd_504360 := by exact prefixLift 504360
  have htrace : WordTrace (prefixWord ++ tailWord_504360) baseStart_504360 baseEnd_504360 := by
    simpa [prefixWord, tailWord_504360, baseEnd_504360] using wordTrace_append hprefix tailTrace_504360
  have hstable : (prefixWord ++ tailWord_504360).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_504360).length < 2 ^ (prefixWord ++ tailWord_504360).sum := by decide
  have hdescent : baseEnd_504360 < baseStart_504360 := by decide
  rcases family_descends (prefixWord ++ tailWord_504360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_504416 : List Nat := [2, 1, 1, 3, 2, 1, 4, 1, 6]
def baseStart_504416 : Nat := 118140960795 + 504416 * 2 ^ 59
def prefixEnd_504416 : Nat := 4983230072969 + 3 ^ 40 * 504416 * 2
def baseEnd_504416 : Nat := 115114603474846090568995

theorem tailTrace_504416 : CollatzResearch.WordTrace tailWord_504416 prefixEnd_504416 115114603474846090568995 := by
  unfold tailWord_504416
  simp only [CollatzResearch.WordTrace]
  refine ⟨9198781470297227119682551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12265041960396302826243401 9198781470297227119682551)
  ·
    refine ⟨13798172205445840679523827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9198781470297227119682551 13798172205445840679523827)
    ·
      refine ⟨20697258308168761019285741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13798172205445840679523827 20697258308168761019285741)
      ·
        refine ⟨7761471865563285382232153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20697258308168761019285741 7761471865563285382232153)
        ·
          refine ⟨5821103899172464036674115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7761471865563285382232153 5821103899172464036674115)
          ·
            refine ⟨8731655848758696055011173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5821103899172464036674115 8731655848758696055011173)
            ·
              refine ⟨1637185471642255510314595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8731655848758696055011173 1637185471642255510314595)
              ·
                refine ⟨2455778207463383265471893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1637185471642255510314595 2455778207463383265471893)
                ·
                  refine ⟨115114603474846090568995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2455778207463383265471893 115114603474846090568995)
                  ·
                    rfl

theorem cell21_504416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 4, 1, 6].length) (baseStart_504416 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_504416 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_504416 prefixEnd_504416 := by exact prefixLift 504416
  have htrace : WordTrace (prefixWord ++ tailWord_504416) baseStart_504416 baseEnd_504416 := by
    simpa [prefixWord, tailWord_504416, baseEnd_504416] using wordTrace_append hprefix tailTrace_504416
  have hstable : (prefixWord ++ tailWord_504416).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_504416).length < 2 ^ (prefixWord ++ tailWord_504416).sum := by decide
  have hdescent : baseEnd_504416 < baseStart_504416 := by decide
  rcases family_descends (prefixWord ++ tailWord_504416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_504481 : List Nat := [1, 2, 3, 3, 4, 1, 1, 6]
def baseStart_504481 : Nat := 118140960795 + 504481 * 2 ^ 59
def prefixEnd_504481 : Nat := 4983230072969 + 3 ^ 40 * 504481 * 2
def baseEnd_504481 : Nat := 38376479120140140661843

theorem tailTrace_504481 : CollatzResearch.WordTrace tailWord_504481 prefixEnd_504481 38376479120140140661843 := by
  unfold tailWord_504481
  simp only [CollatzResearch.WordTrace]
  refine ⟨18399933685358970340481297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12266622456905980226987531 18399933685358970340481297)
  ·
    refine ⟨13799950264019227755360973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18399933685358970340481297 13799950264019227755360973)
    ·
      refine ⟨5174981349007210408260365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13799950264019227755360973 5174981349007210408260365)
      ·
        refine ⟨1940618005877703903097637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5174981349007210408260365 1940618005877703903097637)
        ·
          refine ⟨363865876102069481830807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1940618005877703903097637 363865876102069481830807)
          ·
            refine ⟨545798814153104222746211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 363865876102069481830807 545798814153104222746211)
            ·
              refine ⟨818698221229656334119317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 545798814153104222746211 818698221229656334119317)
              ·
                refine ⟨38376479120140140661843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 818698221229656334119317 38376479120140140661843)
                ·
                  rfl

theorem cell21_504481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 4, 1, 1, 6].length) (baseStart_504481 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_504481 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_504481 prefixEnd_504481 := by exact prefixLift 504481
  have htrace : WordTrace (prefixWord ++ tailWord_504481) baseStart_504481 baseEnd_504481 := by
    simpa [prefixWord, tailWord_504481, baseEnd_504481] using wordTrace_append hprefix tailTrace_504481
  have hstable : (prefixWord ++ tailWord_504481).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_504481).length < 2 ^ (prefixWord ++ tailWord_504481).sum := by decide
  have hdescent : baseEnd_504481 < baseStart_504481 := by decide
  rcases family_descends (prefixWord ++ tailWord_504481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_504526 : List Nat := [4, 1, 1, 1, 3, 4, 1, 2, 4]
def baseStart_504526 : Nat := 118140960795 + 504526 * 2 ^ 59
def prefixEnd_504526 : Nat := 4983230072969 + 3 ^ 40 * 504526 * 2
def baseEnd_504526 : Nat := 115139706973510343735437

theorem tailTrace_504526 : CollatzResearch.WordTrace tailWord_504526 prefixEnd_504526 115139706973510343735437 := by
  unfold tailWord_504526
  simp only [CollatzResearch.WordTrace]
  refine ⟨2300196871274492878233679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12267716646797295350579621 2300196871274492878233679)
  ·
    refine ⟨3450295306911739317350519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2300196871274492878233679 3450295306911739317350519)
    ·
      refine ⟨5175442960367608976025779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3450295306911739317350519 5175442960367608976025779)
      ·
        refine ⟨7763164440551413464038669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5175442960367608976025779 7763164440551413464038669)
        ·
          refine ⟨2911186665206780049014501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7763164440551413464038669 2911186665206780049014501)
          ·
            refine ⟨545847499726271259190219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2911186665206780049014501 545847499726271259190219)
            ·
              refine ⟨818771249589406888785329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 545847499726271259190219 818771249589406888785329)
              ·
                refine ⟨614078437192055166588997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 818771249589406888785329 614078437192055166588997)
                ·
                  refine ⟨115139706973510343735437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 614078437192055166588997 115139706973510343735437)
                  ·
                    rfl

theorem cell21_504526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 4, 1, 2, 4].length) (baseStart_504526 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_504526 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_504526 prefixEnd_504526 := by exact prefixLift 504526
  have htrace : WordTrace (prefixWord ++ tailWord_504526) baseStart_504526 baseEnd_504526 := by
    simpa [prefixWord, tailWord_504526, baseEnd_504526] using wordTrace_append hprefix tailTrace_504526
  have hstable : (prefixWord ++ tailWord_504526).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_504526).length < 2 ^ (prefixWord ++ tailWord_504526).sum := by decide
  have hdescent : baseEnd_504526 < baseStart_504526 := by decide
  rcases family_descends (prefixWord ++ tailWord_504526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_504613 : List Nat := [1, 3, 1, 2, 3, 1, 2, 1, 7]
def baseStart_504613 : Nat := 118140960795 + 504613 * 2 ^ 59
def prefixEnd_504613 : Nat := 4983230072969 + 3 ^ 40 * 504613 * 2
def baseEnd_504613 : Nat := 115159561558817525785259

theorem tailTrace_504613 : CollatzResearch.WordTrace tailWord_504613 prefixEnd_504613 115159561558817525785259 := by
  unfold tailWord_504613
  simp only [CollatzResearch.WordTrace]
  refine ⟨18404748120880756884286493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12269832080587171256190995 18404748120880756884286493)
  ·
    refine ⟨6901780545330283831607435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18404748120880756884286493 6901780545330283831607435)
    ·
      refine ⟨10352670817995425747411153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6901780545330283831607435 10352670817995425747411153)
      ·
        refine ⟨7764503113496569310558365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10352670817995425747411153 7764503113496569310558365)
        ·
          refine ⟨2911688667561213491459387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7764503113496569310558365 2911688667561213491459387)
          ·
            refine ⟨4367533001341820237189081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2911688667561213491459387 4367533001341820237189081)
            ·
              refine ⟨3275649751006365177891811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4367533001341820237189081 3275649751006365177891811)
              ·
                refine ⟨4913474626509547766837717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3275649751006365177891811 4913474626509547766837717)
                ·
                  refine ⟨115159561558817525785259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4913474626509547766837717 115159561558817525785259)
                  ·
                    rfl

theorem cell21_504613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 2, 1, 7].length) (baseStart_504613 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_504613 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_504613 prefixEnd_504613 := by exact prefixLift 504613
  have htrace : WordTrace (prefixWord ++ tailWord_504613) baseStart_504613 baseEnd_504613 := by
    simpa [prefixWord, tailWord_504613, baseEnd_504613] using wordTrace_append hprefix tailTrace_504613
  have hstable : (prefixWord ++ tailWord_504613).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_504613).length < 2 ^ (prefixWord ++ tailWord_504613).sum := by decide
  have hdescent : baseEnd_504613 < baseStart_504613 := by decide
  rcases family_descends (prefixWord ++ tailWord_504613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_504726 : List Nat := [5, 3, 1, 1, 1, 1, 4, 5]
def baseStart_504726 : Nat := 118140960795 + 504726 * 2 ^ 59
def prefixEnd_504726 : Nat := 4983230072969 + 3 ^ 40 * 504726 * 2
def baseEnd_504726 : Nat := 38395116566118146800565

theorem tailTrace_504726 : CollatzResearch.WordTrace tailWord_504726 prefixEnd_504726 38395116566118146800565 := by
  unfold tailWord_504726
  simp only [CollatzResearch.WordTrace]
  refine ⟨1150554348091961073946877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 12272579712980918122100021 1150554348091961073946877)
  ·
    refine ⟨431457880534485402730079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1150554348091961073946877 431457880534485402730079)
    ·
      refine ⟨647186820801728104095119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 431457880534485402730079 647186820801728104095119)
      ·
        refine ⟨970780231202592156142679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 647186820801728104095119 970780231202592156142679)
        ·
          refine ⟨1456170346803888234214019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 970780231202592156142679 1456170346803888234214019)
          ·
            refine ⟨2184255520205832351321029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1456170346803888234214019 2184255520205832351321029)
            ·
              refine ⟨409547910038593565872693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2184255520205832351321029 409547910038593565872693)
              ·
                refine ⟨38395116566118146800565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 409547910038593565872693 38395116566118146800565)
                ·
                  rfl

theorem cell21_504726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 4, 5].length) (baseStart_504726 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_504726 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_504726 prefixEnd_504726 := by exact prefixLift 504726
  have htrace : WordTrace (prefixWord ++ tailWord_504726) baseStart_504726 baseEnd_504726 := by
    simpa [prefixWord, tailWord_504726, baseEnd_504726] using wordTrace_append hprefix tailTrace_504726
  have hstable : (prefixWord ++ tailWord_504726).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_504726).length < 2 ^ (prefixWord ++ tailWord_504726).sum := by decide
  have hdescent : baseEnd_504726 < baseStart_504726 := by decide
  rcases family_descends (prefixWord ++ tailWord_504726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_504810 : List Nat := [3, 1, 3, 1, 2, 11]
def baseStart_504810 : Nat := 118140960795 + 504810 * 2 ^ 59
def prefixEnd_504810 : Nat := 4983230072969 + 3 ^ 40 * 504810 * 2
def baseEnd_504810 : Nat := 4266834060844035592649

theorem tailTrace_504810 : CollatzResearch.WordTrace tailWord_504810 prefixEnd_504810 4266834060844035592649 := by
  unfold tailWord_504810
  simp only [CollatzResearch.WordTrace]
  refine ⟨4602983325291764882301971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12274622200778039686138589 4602983325291764882301971)
  ·
    refine ⟨6904474987937647323452957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4602983325291764882301971 6904474987937647323452957)
    ·
      refine ⟨2589178120476617746294859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6904474987937647323452957 2589178120476617746294859)
      ·
        refine ⟨3883767180714926619442289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2589178120476617746294859 3883767180714926619442289)
        ·
          refine ⟨2912825385536194964581717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3883767180714926619442289 2912825385536194964581717)
          ·
            refine ⟨4266834060844035592649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 2912825385536194964581717 4266834060844035592649)
            ·
              rfl

theorem cell21_504810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 11].length) (baseStart_504810 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_504810 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_504810 prefixEnd_504810 := by exact prefixLift 504810
  have htrace : WordTrace (prefixWord ++ tailWord_504810) baseStart_504810 baseEnd_504810 := by
    simpa [prefixWord, tailWord_504810, baseEnd_504810] using wordTrace_append hprefix tailTrace_504810
  have hstable : (prefixWord ++ tailWord_504810).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_504810).length < 2 ^ (prefixWord ++ tailWord_504810).sum := by decide
  have hdescent : baseEnd_504810 < baseStart_504810 := by decide
  rcases family_descends (prefixWord ++ tailWord_504810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_504850 : List Nat := [3, 2, 5, 1, 1, 1, 2, 3, 3]
def baseStart_504850 : Nat := 118140960795 + 504850 * 2 ^ 59
def prefixEnd_504850 : Nat := 4983230072969 + 3 ^ 40 * 504850 * 2
def baseEnd_504850 : Nat := 115213648187757780334775

theorem tailTrace_504850 : CollatzResearch.WordTrace tailWord_504850 prefixEnd_504850 115213648187757780334775 := by
  unfold tailWord_504850
  simp only [CollatzResearch.WordTrace]
  refine ⟨4603348055255536590166001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12275594814014764240442669 4603348055255536590166001)
  ·
    refine ⟨3452511041441652442624501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4603348055255536590166001 3452511041441652442624501)
    ·
      refine ⟨323672910135154916496047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3452511041441652442624501 323672910135154916496047)
      ·
        refine ⟨485509365202732374744071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 323672910135154916496047 485509365202732374744071)
        ·
          refine ⟨728264047804098562116107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 485509365202732374744071 728264047804098562116107)
          ·
            refine ⟨1092396071706147843174161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 728264047804098562116107 1092396071706147843174161)
            ·
              refine ⟨819297053779610882380621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1092396071706147843174161 819297053779610882380621)
              ·
                refine ⟨307236395167354080892733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 819297053779610882380621 307236395167354080892733)
                ·
                  refine ⟨115213648187757780334775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 307236395167354080892733 115213648187757780334775)
                  ·
                    rfl

theorem cell21_504850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 2, 3, 3].length) (baseStart_504850 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_504850 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_504850 prefixEnd_504850 := by exact prefixLift 504850
  have htrace : WordTrace (prefixWord ++ tailWord_504850) baseStart_504850 baseEnd_504850 := by
    simpa [prefixWord, tailWord_504850, baseEnd_504850] using wordTrace_append hprefix tailTrace_504850
  have hstable : (prefixWord ++ tailWord_504850).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_504850).length < 2 ^ (prefixWord ++ tailWord_504850).sum := by decide
  have hdescent : baseEnd_504850 < baseStart_504850 := by decide
  rcases family_descends (prefixWord ++ tailWord_504850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_504903 : List Nat := [1, 1, 4, 1, 3, 2, 4, 5]
def baseStart_504903 : Nat := 118140960795 + 504903 * 2 ^ 59
def prefixEnd_504903 : Nat := 4983230072969 + 3 ^ 40 * 504903 * 2
def baseEnd_504903 : Nat := 38408581169947155317111

theorem tailTrace_504903 : CollatzResearch.WordTrace tailWord_504903 prefixEnd_504903 38408581169947155317111 := by
  unfold tailWord_504903
  simp only [CollatzResearch.WordTrace]
  refine ⟨18415325289830136412343363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12276883526553424274895575 18415325289830136412343363)
  ·
    refine ⟨27622987934745204618515045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18415325289830136412343363 27622987934745204618515045)
    ·
      refine ⟨5179310237764725865971571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27622987934745204618515045 5179310237764725865971571)
      ·
        refine ⟨7768965356647088798957357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5179310237764725865971571 7768965356647088798957357)
        ·
          refine ⟨2913362008742658299609009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7768965356647088798957357 2913362008742658299609009)
          ·
            refine ⟨2185021506556993724706757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2913362008742658299609009 2185021506556993724706757)
            ·
              refine ⟨409691532479436323382517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2185021506556993724706757 409691532479436323382517)
              ·
                refine ⟨38408581169947155317111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 409691532479436323382517 38408581169947155317111)
                ·
                  rfl

theorem cell21_504903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 4, 5].length) (baseStart_504903 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_504903 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_504903 prefixEnd_504903 := by exact prefixLift 504903
  have htrace : WordTrace (prefixWord ++ tailWord_504903) baseStart_504903 baseEnd_504903 := by
    simpa [prefixWord, tailWord_504903, baseEnd_504903] using wordTrace_append hprefix tailTrace_504903
  have hstable : (prefixWord ++ tailWord_504903).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_504903).length < 2 ^ (prefixWord ++ tailWord_504903).sum := by decide
  have hdescent : baseEnd_504903 < baseStart_504903 := by decide
  rcases family_descends (prefixWord ++ tailWord_504903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_504926 : List Nat := [4, 4, 1, 1, 1, 2, 3, 2, 3]
def baseStart_504926 : Nat := 118140960795 + 504926 * 2 ^ 59
def prefixEnd_504926 : Nat := 4983230072969 + 3 ^ 40 * 504926 * 2
def baseEnd_504926 : Nat := 115230992423198537067953

theorem tailTrace_504926 : CollatzResearch.WordTrace tailWord_504926 prefixEnd_504926 115230992423198537067953 := by
  unfold tailWord_504926
  simp only [CollatzResearch.WordTrace]
  refine ⟨2302020521093351417553829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12277442779164540893620421 2302020521093351417553829)
  ·
    refine ⟨431628847705003390791343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2302020521093351417553829 431628847705003390791343)
    ·
      refine ⟨647443271557505086187015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 431628847705003390791343 647443271557505086187015)
      ·
        refine ⟨971164907336257629280523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 647443271557505086187015 971164907336257629280523)
        ·
          refine ⟨1456747361004386443920785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 971164907336257629280523 1456747361004386443920785)
          ·
            refine ⟨1092560520753289832940589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1456747361004386443920785 1092560520753289832940589)
            ·
              refine ⟨409710195282483687352721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1092560520753289832940589 409710195282483687352721)
              ·
                refine ⟨307282646461862765514541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 409710195282483687352721 307282646461862765514541)
                ·
                  refine ⟨115230992423198537067953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 307282646461862765514541 115230992423198537067953)
                  ·
                    rfl

theorem cell21_504926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 3, 2, 3].length) (baseStart_504926 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_504926 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_504926 prefixEnd_504926 := by exact prefixLift 504926
  have htrace : WordTrace (prefixWord ++ tailWord_504926) baseStart_504926 baseEnd_504926 := by
    simpa [prefixWord, tailWord_504926, baseEnd_504926] using wordTrace_append hprefix tailTrace_504926
  have hstable : (prefixWord ++ tailWord_504926).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_504926).length < 2 ^ (prefixWord ++ tailWord_504926).sum := by decide
  have hdescent : baseEnd_504926 < baseStart_504926 := by decide
  rcases family_descends (prefixWord ++ tailWord_504926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_504976 : List Nat := [2, 1, 1, 1, 1, 1, 4, 1, 9]
def baseStart_504976 : Nat := 118140960795 + 504976 * 2 ^ 59
def prefixEnd_504976 : Nat := 4983230072969 + 3 ^ 40 * 504976 * 2
def baseEnd_504976 : Nat := 115242403104409561234517

theorem tailTrace_504976 : CollatzResearch.WordTrace tailWord_504976 prefixEnd_504976 115242403104409561234517 := by
  unfold tailWord_504976
  simp only [CollatzResearch.WordTrace]
  refine ⟨9208993909282834939875391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12278658545710446586500521 9208993909282834939875391)
  ·
    refine ⟨13813490863924252409813087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9208993909282834939875391 13813490863924252409813087)
    ·
      refine ⟨20720236295886378614719631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13813490863924252409813087 20720236295886378614719631)
      ·
        refine ⟨31080354443829567922079447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20720236295886378614719631 31080354443829567922079447)
        ·
          refine ⟨46620531665744351883119171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31080354443829567922079447 46620531665744351883119171)
          ·
            refine ⟨69930797498616527824678757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46620531665744351883119171 69930797498616527824678757)
            ·
              refine ⟨13112024530990598967127267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 69930797498616527824678757 13112024530990598967127267)
              ·
                refine ⟨19668036796485898450690901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13112024530990598967127267 19668036796485898450690901)
                ·
                  refine ⟨115242403104409561234517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 19668036796485898450690901 115242403104409561234517)
                  ·
                    rfl

theorem cell21_504976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 1, 9].length) (baseStart_504976 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_504976 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_504976 prefixEnd_504976 := by exact prefixLift 504976
  have htrace : WordTrace (prefixWord ++ tailWord_504976) baseStart_504976 baseEnd_504976 := by
    simpa [prefixWord, tailWord_504976, baseEnd_504976] using wordTrace_append hprefix tailTrace_504976
  have hstable : (prefixWord ++ tailWord_504976).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_504976).length < 2 ^ (prefixWord ++ tailWord_504976).sum := by decide
  have hdescent : baseEnd_504976 < baseStart_504976 := by decide
  rcases family_descends (prefixWord ++ tailWord_504976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_504993 : List Nat := [1, 2, 3, 3, 1, 1, 2, 3, 5]
def baseStart_504993 : Nat := 118140960795 + 504993 * 2 ^ 59
def prefixEnd_504993 : Nat := 4983230072969 + 3 ^ 40 * 504993 * 2
def baseEnd_504993 : Nat := 115246282736021309451149

theorem tailTrace_504993 : CollatzResearch.WordTrace tailWord_504993 prefixEnd_504993 115246282736021309451149 := by
  unfold tailWord_504993
  simp only [CollatzResearch.WordTrace]
  refine ⟨18418607859504081783119633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12279071906336054522079755 18418607859504081783119633)
  ·
    refine ⟨13813955894628061337339725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18418607859504081783119633 13813955894628061337339725)
    ·
      refine ⟨5180233460485523001502397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13813955894628061337339725 5180233460485523001502397)
      ·
        refine ⟨1942587547682071125563399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5180233460485523001502397 1942587547682071125563399)
        ·
          refine ⟨2913881321523106688345099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1942587547682071125563399 2913881321523106688345099)
          ·
            refine ⟨4370821982284660032517649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2913881321523106688345099 4370821982284660032517649)
            ·
              refine ⟨3278116486713495024388237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4370821982284660032517649 3278116486713495024388237)
              ·
                refine ⟨1229293682517560634145589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3278116486713495024388237 1229293682517560634145589)
                ·
                  refine ⟨115246282736021309451149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1229293682517560634145589 115246282736021309451149)
                  ·
                    rfl

theorem cell21_504993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 2, 3, 5].length) (baseStart_504993 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_504993 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_504993 prefixEnd_504993 := by exact prefixLift 504993
  have htrace : WordTrace (prefixWord ++ tailWord_504993) baseStart_504993 baseEnd_504993 := by
    simpa [prefixWord, tailWord_504993, baseEnd_504993] using wordTrace_append hprefix tailTrace_504993
  have hstable : (prefixWord ++ tailWord_504993).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_504993).length < 2 ^ (prefixWord ++ tailWord_504993).sum := by decide
  have hdescent : baseEnd_504993 < baseStart_504993 := by decide
  rcases family_descends (prefixWord ++ tailWord_504993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_505114 : List Nat := [3, 1, 1, 3, 3, 1, 1, 8]
def baseStart_505114 : Nat := 118140960795 + 505114 * 2 ^ 59
def prefixEnd_505114 : Nat := 4983230072969 + 3 ^ 40 * 505114 * 2
def baseEnd_505114 : Nat := 38424632194850662644745

theorem tailTrace_505114 : CollatzResearch.WordTrace tailWord_505114 prefixEnd_505114 38424632194850662644745 := by
  unfold tailWord_505114
  simp only [CollatzResearch.WordTrace]
  refine ⟨4605755273016429862068599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12282014061377146298849597 4605755273016429862068599)
  ·
    refine ⟨6908632909524644793102899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4605755273016429862068599 6908632909524644793102899)
    ·
      refine ⟨10362949364286967189654349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6908632909524644793102899 10362949364286967189654349)
      ·
        refine ⟨3886106011607612696120381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10362949364286967189654349 3886106011607612696120381)
        ·
          refine ⟨1457289754352854761045143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3886106011607612696120381 1457289754352854761045143)
          ·
            refine ⟨2185934631529282141567715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1457289754352854761045143 2185934631529282141567715)
            ·
              refine ⟨3278901947293923212351573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2185934631529282141567715 3278901947293923212351573)
              ·
                refine ⟨38424632194850662644745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3278901947293923212351573 38424632194850662644745)
                ·
                  rfl

theorem cell21_505114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 1, 8].length) (baseStart_505114 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_505114 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_505114 prefixEnd_505114 := by exact prefixLift 505114
  have htrace : WordTrace (prefixWord ++ tailWord_505114) baseStart_505114 baseEnd_505114 := by
    simpa [prefixWord, tailWord_505114, baseEnd_505114] using wordTrace_append hprefix tailTrace_505114
  have hstable : (prefixWord ++ tailWord_505114).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_505114).length < 2 ^ (prefixWord ++ tailWord_505114).sum := by decide
  have hdescent : baseEnd_505114 < baseStart_505114 := by decide
  rcases family_descends (prefixWord ++ tailWord_505114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_505117 : List Nat := [1, 4, 2, 3, 1, 2, 1, 3, 4]
def baseStart_505117 : Nat := 118140960795 + 505117 * 2 ^ 59
def prefixEnd_505117 : Nat := 4983230072969 + 3 ^ 40 * 505117 * 2
def baseEnd_505117 : Nat := 115274581225424649384229

theorem tailTrace_505117 : CollatzResearch.WordTrace tailWord_505117 prefixEnd_505117 115274581225424649384229 := by
  unfold tailWord_505117
  simp only [CollatzResearch.WordTrace]
  refine ⟨18423130511054850960633605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12282087007369900640422403 18423130511054850960633605)
  ·
    refine ⟨3454336970822784555118801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18423130511054850960633605 3454336970822784555118801)
    ·
      refine ⟨2590752728117088416339101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3454336970822784555118801 2590752728117088416339101)
      ·
        refine ⟨971532273043908156127163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2590752728117088416339101 971532273043908156127163)
        ·
          refine ⟨1457298409565862234190745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 971532273043908156127163 1457298409565862234190745)
          ·
            refine ⟨1092973807174396675643059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1457298409565862234190745 1092973807174396675643059)
            ·
              refine ⟨1639460710761595013464589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1092973807174396675643059 1639460710761595013464589)
              ·
                refine ⟨614797766535598130049221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1639460710761595013464589 614797766535598130049221)
                ·
                  refine ⟨115274581225424649384229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 614797766535598130049221 115274581225424649384229)
                  ·
                    rfl

theorem cell21_505117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 1, 3, 4].length) (baseStart_505117 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_505117 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_505117 prefixEnd_505117 := by exact prefixLift 505117
  have htrace : WordTrace (prefixWord ++ tailWord_505117) baseStart_505117 baseEnd_505117 := by
    simpa [prefixWord, tailWord_505117, baseEnd_505117] using wordTrace_append hprefix tailTrace_505117
  have hstable : (prefixWord ++ tailWord_505117).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_505117).length < 2 ^ (prefixWord ++ tailWord_505117).sum := by decide
  have hdescent : baseEnd_505117 < baseStart_505117 := by decide
  rcases family_descends (prefixWord ++ tailWord_505117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_505165 : List Nat := [1, 6, 1, 3, 1, 2, 1, 6]
def baseStart_505165 : Nat := 118140960795 + 505165 * 2 ^ 59
def prefixEnd_505165 : Nat := 4983230072969 + 3 ^ 40 * 505165 * 2
def baseEnd_505165 : Nat := 38428511826462410861377

theorem tailTrace_505165 : CollatzResearch.WordTrace tailWord_505165 prefixEnd_505165 38428511826462410861377 := by
  unfold tailWord_505165
  simp only [CollatzResearch.WordTrace]
  refine ⟨18424881214880955158380949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12283254143253970105587299 18424881214880955158380949)
  ·
    refine ⟨863666306947544773049107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 18424881214880955158380949 863666306947544773049107)
    ·
      refine ⟨1295499460421317159573661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 863666306947544773049107 1295499460421317159573661)
      ·
        refine ⟨485812297657993934840123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1295499460421317159573661 485812297657993934840123)
        ·
          refine ⟨728718446486990902260185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 485812297657993934840123 728718446486990902260185)
          ·
            refine ⟨546538834865243176695139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 728718446486990902260185 546538834865243176695139)
            ·
              refine ⟨819808252297864765042709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 546538834865243176695139 819808252297864765042709)
              ·
                refine ⟨38428511826462410861377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 819808252297864765042709 38428511826462410861377)
                ·
                  rfl

theorem cell21_505165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 2, 1, 6].length) (baseStart_505165 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_505165 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_505165 prefixEnd_505165 := by exact prefixLift 505165
  have htrace : WordTrace (prefixWord ++ tailWord_505165) baseStart_505165 baseEnd_505165 := by
    simpa [prefixWord, tailWord_505165, baseEnd_505165] using wordTrace_append hprefix tailTrace_505165
  have hstable : (prefixWord ++ tailWord_505165).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_505165).length < 2 ^ (prefixWord ++ tailWord_505165).sum := by decide
  have hdescent : baseEnd_505165 < baseStart_505165 := by decide
  rcases family_descends (prefixWord ++ tailWord_505165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_505328 : List Nat := [2, 1, 1, 1, 3, 5, 2, 2, 4]
def baseStart_505328 : Nat := 118140960795 + 505328 * 2 ^ 59
def prefixEnd_505328 : Nat := 4983230072969 + 3 ^ 40 * 505328 * 2
def baseEnd_505328 : Nat := 115322734300135171367131

theorem tailTrace_505328 : CollatzResearch.WordTrace tailWord_505328 prefixEnd_505328 115322734300135171367131 := by
  unfold tailWord_505328
  simp only [CollatzResearch.WordTrace]
  refine ⟨9215413156645216998282319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12287217542193622664376425 9215413156645216998282319)
  ·
    refine ⟨13823119734967825497423479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9215413156645216998282319 13823119734967825497423479)
    ·
      refine ⟨20734679602451738246135219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13823119734967825497423479 20734679602451738246135219)
      ·
        refine ⟨31102019403677607369202829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20734679602451738246135219 31102019403677607369202829)
        ·
          refine ⟨11663257276379102763451061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31102019403677607369202829 11663257276379102763451061)
          ·
            refine ⟨1093430369660540884073537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11663257276379102763451061 1093430369660540884073537)
            ·
              refine ⟨820072777245405663055153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1093430369660540884073537 820072777245405663055153)
              ·
                refine ⟨615054582934054247291365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 820072777245405663055153 615054582934054247291365)
                ·
                  refine ⟨115322734300135171367131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 615054582934054247291365 115322734300135171367131)
                  ·
                    rfl

theorem cell21_505328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 2, 2, 4].length) (baseStart_505328 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_505328 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_505328 prefixEnd_505328 := by exact prefixLift 505328
  have htrace : WordTrace (prefixWord ++ tailWord_505328) baseStart_505328 baseEnd_505328 := by
    simpa [prefixWord, tailWord_505328, baseEnd_505328] using wordTrace_append hprefix tailTrace_505328
  have hstable : (prefixWord ++ tailWord_505328).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_505328).length < 2 ^ (prefixWord ++ tailWord_505328).sum := by decide
  have hdescent : baseEnd_505328 < baseStart_505328 := by decide
  rcases family_descends (prefixWord ++ tailWord_505328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_505390 : List Nat := [4, 1, 3, 1, 2, 2, 2, 1, 5]
def baseStart_505390 : Nat := 118140960795 + 505390 * 2 ^ 59
def prefixEnd_505390 : Nat := 4983230072969 + 3 ^ 40 * 505390 * 2
def baseEnd_505390 : Nat := 115336883544836841333671

theorem tailTrace_505390 : CollatzResearch.WordTrace tailWord_505390 prefixEnd_505390 115336883544836841333671 := by
  unfold tailWord_505390
  simp only [CollatzResearch.WordTrace]
  refine ⟨2304135954883227323165203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12288725092710545723547749 2304135954883227323165203)
  ·
    refine ⟨3456203932324840984747805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2304135954883227323165203 3456203932324840984747805)
    ·
      refine ⟨1296076474621815369280427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3456203932324840984747805 1296076474621815369280427)
      ·
        refine ⟨1944114711932723053920641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1296076474621815369280427 1944114711932723053920641)
        ·
          refine ⟨1458086033949542290440481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1944114711932723053920641 1458086033949542290440481)
          ·
            refine ⟨1093564525462156717830361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1458086033949542290440481 1093564525462156717830361)
            ·
              refine ⟨820173394096617538372771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1093564525462156717830361 820173394096617538372771)
              ·
                refine ⟨1230260091144926307559157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 820173394096617538372771 1230260091144926307559157)
                ·
                  refine ⟨115336883544836841333671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1230260091144926307559157 115336883544836841333671)
                  ·
                    rfl

theorem cell21_505390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 2, 1, 5].length) (baseStart_505390 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_505390 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_505390 prefixEnd_505390 := by exact prefixLift 505390
  have htrace : WordTrace (prefixWord ++ tailWord_505390) baseStart_505390 baseEnd_505390 := by
    simpa [prefixWord, tailWord_505390, baseEnd_505390] using wordTrace_append hprefix tailTrace_505390
  have hstable : (prefixWord ++ tailWord_505390).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_505390).length < 2 ^ (prefixWord ++ tailWord_505390).sum := by decide
  have hdescent : baseEnd_505390 < baseStart_505390 := by decide
  rcases family_descends (prefixWord ++ tailWord_505390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_505449 : List Nat := [1, 2, 1, 1, 1, 4, 2, 6, 3]
def baseStart_505449 : Nat := 118140960795 + 505449 * 2 ^ 59
def prefixEnd_505449 : Nat := 4983230072969 + 3 ^ 40 * 505449 * 2
def baseEnd_505449 : Nat := 115350348148665849850217

theorem tailTrace_505449 : CollatzResearch.WordTrace tailWord_505449 prefixEnd_505449 115350348148665849850217 := by
  unfold tailWord_505449
  simp only [CollatzResearch.WordTrace]
  refine ⟨18435239545852071661719401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12290159697234714441146267 18435239545852071661719401)
  ·
    refine ⟨13826429659389053746289551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18435239545852071661719401 13826429659389053746289551)
    ·
      refine ⟨20739644489083580619434327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13826429659389053746289551 20739644489083580619434327)
      ·
        refine ⟨31109466733625370929151491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20739644489083580619434327 31109466733625370929151491)
        ·
          refine ⟨46664200100438056393727237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31109466733625370929151491 46664200100438056393727237)
          ·
            refine ⟨8749537518832135573823857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46664200100438056393727237 8749537518832135573823857)
            ·
              refine ⟨6562153139124101680367893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8749537518832135573823857 6562153139124101680367893)
              ·
                refine ⟨307600928396442266267245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 6562153139124101680367893 307600928396442266267245)
                ·
                  refine ⟨115350348148665849850217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 307600928396442266267245 115350348148665849850217)
                  ·
                    rfl

theorem cell21_505449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 6, 3].length) (baseStart_505449 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_505449 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_505449 prefixEnd_505449 := by exact prefixLift 505449
  have htrace : WordTrace (prefixWord ++ tailWord_505449) baseStart_505449 baseEnd_505449 := by
    simpa [prefixWord, tailWord_505449, baseEnd_505449] using wordTrace_append hprefix tailTrace_505449
  have hstable : (prefixWord ++ tailWord_505449).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_505449).length < 2 ^ (prefixWord ++ tailWord_505449).sum := by decide
  have hdescent : baseEnd_505449 < baseStart_505449 := by decide
  rcases family_descends (prefixWord ++ tailWord_505449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_505477 : List Nat := [1, 3, 1, 1, 4, 1, 1, 9]
def baseStart_505477 : Nat := 118140960795 + 505477 * 2 ^ 59
def prefixEnd_505477 : Nat := 4983230072969 + 3 ^ 40 * 505477 * 2
def baseEnd_505477 : Nat := 38452246043381341127831

theorem tailTrace_505477 : CollatzResearch.WordTrace tailWord_505477 prefixEnd_505477 38452246043381341127831 := by
  unfold tailWord_505477
  simp only [CollatzResearch.WordTrace]
  refine ⟨18436260789750632443738685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12290840526500421629159123 18436260789750632443738685)
  ·
    refine ⟨6913597796156487166402007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18436260789750632443738685 6913597796156487166402007)
    ·
      refine ⟨10370396694234730749603011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6913597796156487166402007 10370396694234730749603011)
      ·
        refine ⟨15555595041352096124404517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10370396694234730749603011 15555595041352096124404517)
        ·
          refine ⟨2916674070253518023325847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15555595041352096124404517 2916674070253518023325847)
          ·
            refine ⟨4375011105380277034988771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2916674070253518023325847 4375011105380277034988771)
            ·
              refine ⟨6562516658070415552483157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4375011105380277034988771 6562516658070415552483157)
              ·
                refine ⟨38452246043381341127831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 6562516658070415552483157 38452246043381341127831)
                ·
                  rfl

theorem cell21_505477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 9].length) (baseStart_505477 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_505477 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_505477 prefixEnd_505477 := by exact prefixLift 505477
  have htrace : WordTrace (prefixWord ++ tailWord_505477) baseStart_505477 baseEnd_505477 := by
    simpa [prefixWord, tailWord_505477, baseEnd_505477] using wordTrace_append hprefix tailTrace_505477
  have hstable : (prefixWord ++ tailWord_505477).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_505477).length < 2 ^ (prefixWord ++ tailWord_505477).sum := by decide
  have hdescent : baseEnd_505477 < baseStart_505477 := by decide
  rcases family_descends (prefixWord ++ tailWord_505477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_505494 : List Nat := [5, 3, 13]
def baseStart_505494 : Nat := 118140960795 + 505494 * 2 ^ 59
def prefixEnd_505494 : Nat := 4983230072969 + 3 ^ 40 * 505494 * 2
def baseEnd_505494 : Nat := 158245017505837821125

theorem tailTrace_505494 : CollatzResearch.WordTrace tailWord_505494 prefixEnd_505494 158245017505837821125 := by
  unfold tailWord_505494
  simp only [CollatzResearch.WordTrace]
  refine ⟨1152305051918065271694221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 12291253887126029564738357 1152305051918065271694221)
  ·
    refine ⟨432114394469274476885333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1152305051918065271694221 432114394469274476885333)
    ·
      refine ⟨158245017505837821125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 13 432114394469274476885333 158245017505837821125)
      ·
        rfl

theorem cell21_505494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 13].length) (baseStart_505494 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_505494 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_505494 prefixEnd_505494 := by exact prefixLift 505494
  have htrace : WordTrace (prefixWord ++ tailWord_505494) baseStart_505494 baseEnd_505494 := by
    simpa [prefixWord, tailWord_505494, baseEnd_505494] using wordTrace_append hprefix tailTrace_505494
  have hstable : (prefixWord ++ tailWord_505494).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_505494).length < 2 ^ (prefixWord ++ tailWord_505494).sum := by decide
  have hdescent : baseEnd_505494 < baseStart_505494 := by decide
  rcases family_descends (prefixWord ++ tailWord_505494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_505500 : List Nat := [2, 2, 3, 2, 3, 2, 2, 2, 3]
def baseStart_505500 : Nat := 118140960795 + 505500 * 2 ^ 59
def prefixEnd_505500 : Nat := 4983230072969 + 3 ^ 40 * 505500 * 2
def baseEnd_505500 : Nat := 115361987043501094500113

theorem tailTrace_505500 : CollatzResearch.WordTrace tailWord_505500 prefixEnd_505500 115361987043501094500113 := by
  unfold tailWord_505500
  simp only [CollatzResearch.WordTrace]
  refine ⟨9218549834333653685912977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12291399779111538247883969 9218549834333653685912977)
  ·
    refine ⟨6913912375750240264434733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9218549834333653685912977 6913912375750240264434733)
    ·
      refine ⟨2592717140906340099163025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6913912375750240264434733 2592717140906340099163025)
      ·
        refine ⟨1944537855679755074372269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2592717140906340099163025 1944537855679755074372269)
        ·
          refine ⟨729201695879908152889601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1944537855679755074372269 729201695879908152889601)
          ·
            refine ⟨546901271909931114667201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 729201695879908152889601 546901271909931114667201)
            ·
              refine ⟨410175953932448336000401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 546901271909931114667201 410175953932448336000401)
              ·
                refine ⟨307631965449336252000301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 410175953932448336000401 307631965449336252000301)
                ·
                  refine ⟨115361987043501094500113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 307631965449336252000301 115361987043501094500113)
                  ·
                    rfl

theorem cell21_505500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 2, 2, 2, 3].length) (baseStart_505500 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_505500 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_505500 prefixEnd_505500 := by exact prefixLift 505500
  have htrace : WordTrace (prefixWord ++ tailWord_505500) baseStart_505500 baseEnd_505500 := by
    simpa [prefixWord, tailWord_505500, baseEnd_505500] using wordTrace_append hprefix tailTrace_505500
  have hstable : (prefixWord ++ tailWord_505500).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_505500).length < 2 ^ (prefixWord ++ tailWord_505500).sum := by decide
  have hdescent : baseEnd_505500 < baseStart_505500 := by decide
  rcases family_descends (prefixWord ++ tailWord_505500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_505553 : List Nat := [1, 2, 2, 1, 2, 5, 8]
def baseStart_505553 : Nat := 118140960795 + 505553 * 2 ^ 59
def prefixEnd_505553 : Nat := 4983230072969 + 3 ^ 40 * 505553 * 2
def baseEnd_505553 : Nat := 12819342485064975568519

theorem tailTrace_505553 : CollatzResearch.WordTrace tailWord_505553 prefixEnd_505553 12819342485064975568519 := by
  unfold tailWord_505553
  simp only [CollatzResearch.WordTrace]
  refine ⟨18439032737475297423505313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12292688491650198282336875 18439032737475297423505313)
  ·
    refine ⟨13829274553106473067628985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18439032737475297423505313 13829274553106473067628985)
    ·
      refine ⟨10371955914829854800721739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13829274553106473067628985 10371955914829854800721739)
      ·
        refine ⟨15557933872244782201082609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10371955914829854800721739 15557933872244782201082609)
        ·
          refine ⟨11668450404183586650811957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15557933872244782201082609 11668450404183586650811957)
          ·
            refine ⟨1093917225392211248513621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11668450404183586650811957 1093917225392211248513621)
            ·
              refine ⟨12819342485064975568519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1093917225392211248513621 12819342485064975568519)
              ·
                rfl

theorem cell21_505553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 8].length) (baseStart_505553 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_505553 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_505553 prefixEnd_505553 := by exact prefixLift 505553
  have htrace : WordTrace (prefixWord ++ tailWord_505553) baseStart_505553 baseEnd_505553 := by
    simpa [prefixWord, tailWord_505553, baseEnd_505553] using wordTrace_append hprefix tailTrace_505553
  have hstable : (prefixWord ++ tailWord_505553).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_505553).length < 2 ^ (prefixWord ++ tailWord_505553).sum := by decide
  have hdescent : baseEnd_505553 < baseStart_505553 := by decide
  rcases family_descends (prefixWord ++ tailWord_505553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_505556 : List Nat := [2, 4, 1, 3, 1, 2, 1, 1, 6]
def baseStart_505556 : Nat := 118140960795 + 505556 * 2 ^ 59
def prefixEnd_505556 : Nat := 4983230072969 + 3 ^ 40 * 505556 * 2
def baseEnd_505556 : Nat := 115374767006457441566665

theorem tailTrace_505556 : CollatzResearch.WordTrace tailWord_505556 prefixEnd_505556 115374767006457441566665 := by
  unfold tailWord_505556
  simp only [CollatzResearch.WordTrace]
  refine ⟨9219571078232214467932261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12292761437642952623909681 9219571078232214467932261)
  ·
    refine ⟨1728669577168540212737299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9219571078232214467932261 1728669577168540212737299)
    ·
      refine ⟨2593004365752810319105949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1728669577168540212737299 2593004365752810319105949)
      ·
        refine ⟨972376637157303869664731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2593004365752810319105949 972376637157303869664731)
        ·
          refine ⟨1458564955735955804497097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 972376637157303869664731 1458564955735955804497097)
          ·
            refine ⟨1093923716801966853372823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1458564955735955804497097 1093923716801966853372823)
            ·
              refine ⟨1640885575202950280059235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1093923716801966853372823 1640885575202950280059235)
              ·
                refine ⟨2461328362804425420088853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1640885575202950280059235 2461328362804425420088853)
                ·
                  refine ⟨115374767006457441566665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2461328362804425420088853 115374767006457441566665)
                  ·
                    rfl

theorem cell21_505556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 1, 1, 6].length) (baseStart_505556 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_505556 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_505556 prefixEnd_505556 := by exact prefixLift 505556
  have htrace : WordTrace (prefixWord ++ tailWord_505556) baseStart_505556 baseEnd_505556 := by
    simpa [prefixWord, tailWord_505556, baseEnd_505556] using wordTrace_append hprefix tailTrace_505556
  have hstable : (prefixWord ++ tailWord_505556).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_505556).length < 2 ^ (prefixWord ++ tailWord_505556).sum := by decide
  have hdescent : baseEnd_505556 < baseStart_505556 := by decide
  rcases family_descends (prefixWord ++ tailWord_505556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_505618 : List Nat := [3, 2, 4, 1, 1, 1, 3, 1, 5]
def baseStart_505618 : Nat := 118140960795 + 505618 * 2 ^ 59
def prefixEnd_505618 : Nat := 4983230072969 + 3 ^ 40 * 505618 * 2
def baseEnd_505618 : Nat := 115388916251159111533205

theorem tailTrace_505618 : CollatzResearch.WordTrace tailWord_505618 prefixEnd_505618 115388916251159111533205 := by
  unfold tailWord_505618
  simp only [CollatzResearch.WordTrace]
  refine ⟨4610350870559953381155377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12294268988159875683081005 4610350870559953381155377)
  ·
    refine ⟨3457763152919965035866533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4610350870559953381155377 3457763152919965035866533)
    ·
      refine ⟨648330591172493444224975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3457763152919965035866533 648330591172493444224975)
      ·
        refine ⟨972495886758740166337463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 648330591172493444224975 972495886758740166337463)
        ·
          refine ⟨1458743830138110249506195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 972495886758740166337463 1458743830138110249506195)
          ·
            refine ⟨2188115745207165374259293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1458743830138110249506195 2188115745207165374259293)
            ·
              refine ⟨820543404452687015347235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2188115745207165374259293 820543404452687015347235)
              ·
                refine ⟨1230815106679030523020853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 820543404452687015347235 1230815106679030523020853)
                ·
                  refine ⟨115388916251159111533205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1230815106679030523020853 115388916251159111533205)
                  ·
                    rfl

theorem cell21_505618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 3, 1, 5].length) (baseStart_505618 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_505618 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_505618 prefixEnd_505618 := by exact prefixLift 505618
  have htrace : WordTrace (prefixWord ++ tailWord_505618) baseStart_505618 baseEnd_505618 := by
    simpa [prefixWord, tailWord_505618, baseEnd_505618] using wordTrace_append hprefix tailTrace_505618
  have hstable : (prefixWord ++ tailWord_505618).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_505618).length < 2 ^ (prefixWord ++ tailWord_505618).sum := by decide
  have hdescent : baseEnd_505618 < baseStart_505618 := by decide
  rcases family_descends (prefixWord ++ tailWord_505618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_505742 : List Nat := [4, 1, 1, 5, 1, 1, 3, 1, 4]
def baseStart_505742 : Nat := 118140960795 + 505742 * 2 ^ 59
def prefixEnd_505742 : Nat := 4983230072969 + 3 ^ 40 * 505742 * 2
def baseEnd_505742 : Nat := 115417214740562451466285

theorem tailTrace_505742 : CollatzResearch.WordTrace tailWord_505742 prefixEnd_505742 115417214740562451466285 := by
  unfold tailWord_505742
  simp only [CollatzResearch.WordTrace]
  refine ⟨2305740766723822837766935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12297284089193721801423653 2305740766723822837766935)
  ·
    refine ⟨3458611150085734256650403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2305740766723822837766935 3458611150085734256650403)
    ·
      refine ⟨5187916725128601384975605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3458611150085734256650403 5187916725128601384975605)
      ·
        refine ⟨486367192980806379841463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 5187916725128601384975605 486367192980806379841463)
        ·
          refine ⟨729550789471209569762195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 486367192980806379841463 729550789471209569762195)
          ·
            refine ⟨1094326184206814354643293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 729550789471209569762195 1094326184206814354643293)
            ·
              refine ⟨410372319077555382991235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1094326184206814354643293 410372319077555382991235)
              ·
                refine ⟨615558478616333074486853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 410372319077555382991235 615558478616333074486853)
                ·
                  refine ⟨115417214740562451466285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 615558478616333074486853 115417214740562451466285)
                  ·
                    rfl

theorem cell21_505742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 3, 1, 4].length) (baseStart_505742 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_505742 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_505742 prefixEnd_505742 := by exact prefixLift 505742
  have htrace : WordTrace (prefixWord ++ tailWord_505742) baseStart_505742 baseEnd_505742 := by
    simpa [prefixWord, tailWord_505742, baseEnd_505742] using wordTrace_append hprefix tailTrace_505742
  have hstable : (prefixWord ++ tailWord_505742).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_505742).length < 2 ^ (prefixWord ++ tailWord_505742).sum := by decide
  have hdescent : baseEnd_505742 < baseStart_505742 := by decide
  rcases family_descends (prefixWord ++ tailWord_505742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_505767 : List Nat := [1, 1, 6, 1, 2, 1, 1, 2, 6]
def baseStart_505767 : Nat := 118140960795 + 505767 * 2 ^ 59
def prefixEnd_505767 : Nat := 4983230072969 + 3 ^ 40 * 505767 * 2
def baseEnd_505767 : Nat := 115422920081167963549567

theorem tailTrace_505767 : CollatzResearch.WordTrace tailWord_505767 prefixEnd_505767 115422920081167963549567 := by
  unfold tailWord_505767
  simp only [CollatzResearch.WordTrace]
  refine ⟨18446837958700011971795555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12297891972466674647863703 18446837958700011971795555)
  ·
    refine ⟨27670256938050017957693333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18446837958700011971795555 27670256938050017957693333)
    ·
      refine ⟨1297043293971094591766875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 27670256938050017957693333 1297043293971094591766875)
      ·
        refine ⟨1945564940956641887650313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1297043293971094591766875 1945564940956641887650313)
        ·
          refine ⟨1459173705717481415737735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1945564940956641887650313 1459173705717481415737735)
          ·
            refine ⟨2188760558576222123606603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1459173705717481415737735 2188760558576222123606603)
            ·
              refine ⟨3283140837864333185409905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2188760558576222123606603 3283140837864333185409905)
              ·
                refine ⟨2462355628398249889057429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3283140837864333185409905 2462355628398249889057429)
                ·
                  refine ⟨115422920081167963549567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2462355628398249889057429 115422920081167963549567)
                  ·
                    rfl

theorem cell21_505767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 1, 2, 6].length) (baseStart_505767 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_505767 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_505767 prefixEnd_505767 := by exact prefixLift 505767
  have htrace : WordTrace (prefixWord ++ tailWord_505767) baseStart_505767 baseEnd_505767 := by
    simpa [prefixWord, tailWord_505767, baseEnd_505767] using wordTrace_append hprefix tailTrace_505767
  have hstable : (prefixWord ++ tailWord_505767).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_505767).length < 2 ^ (prefixWord ++ tailWord_505767).sum := by decide
  have hdescent : baseEnd_505767 < baseStart_505767 := by decide
  rcases family_descends (prefixWord ++ tailWord_505767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_505781 : List Nat := [1, 3, 3, 2, 1, 2, 9]
def baseStart_505781 : Nat := 118140960795 + 505781 * 2 ^ 59
def prefixEnd_505781 : Nat := 4983230072969 + 3 ^ 40 * 505781 * 2
def baseEnd_505781 : Nat := 12825123896878561146245

theorem tailTrace_505781 : CollatzResearch.WordTrace tailWord_505781 prefixEnd_505781 12825123896878561146245 := by
  unfold tailWord_505781
  simp only [CollatzResearch.WordTrace]
  refine ⟨18447348580649292362805197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12298232387099528241870131 18447348580649292362805197)
  ·
    refine ⟨6917755717743484636051949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18447348580649292362805197 6917755717743484636051949)
    ·
      refine ⟨2594158394153806738519481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6917755717743484636051949 2594158394153806738519481)
      ·
        refine ⟨1945618795615355053889611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2594158394153806738519481 1945618795615355053889611)
        ·
          refine ⟨2918428193423032580834417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1945618795615355053889611 2918428193423032580834417)
          ·
            refine ⟨2188821145067274435625813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2918428193423032580834417 2188821145067274435625813)
            ·
              refine ⟨12825123896878561146245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2188821145067274435625813 12825123896878561146245)
              ·
                rfl

theorem cell21_505781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 9].length) (baseStart_505781 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_505781 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_505781 prefixEnd_505781 := by exact prefixLift 505781
  have htrace : WordTrace (prefixWord ++ tailWord_505781) baseStart_505781 baseEnd_505781 := by
    simpa [prefixWord, tailWord_505781, baseEnd_505781] using wordTrace_append hprefix tailTrace_505781
  have hstable : (prefixWord ++ tailWord_505781).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_505781).length < 2 ^ (prefixWord ++ tailWord_505781).sum := by decide
  have hdescent : baseEnd_505781 < baseStart_505781 := by decide
  rcases family_descends (prefixWord ++ tailWord_505781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_505812 : List Nat := [2, 4, 1, 2, 1, 1, 2, 1, 7]
def baseStart_505812 : Nat := 118140960795 + 505812 * 2 ^ 59
def prefixEnd_505812 : Nat := 4983230072969 + 3 ^ 40 * 505812 * 2
def baseEnd_505812 : Nat := 115433189694257885299475

theorem tailTrace_505812 : CollatzResearch.WordTrace tailWord_505812 prefixEnd_505812 115433189694257885299475 := by
  unfold tailWord_505812
  simp only [CollatzResearch.WordTrace]
  refine ⟨9224239621768492328591845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12298986162357989771455793 9224239621768492328591845)
  ·
    refine ⟨1729544929081592311610971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9224239621768492328591845 1729544929081592311610971)
    ·
      refine ⟨2594317393622388467416457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1729544929081592311610971 2594317393622388467416457)
      ·
        refine ⟨1945738045216791350562343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2594317393622388467416457 1945738045216791350562343)
        ·
          refine ⟨2918607067825187025843515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1945738045216791350562343 2918607067825187025843515)
          ·
            refine ⟨4377910601737780538765273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2918607067825187025843515 4377910601737780538765273)
            ·
              refine ⟨3283432951303335404073955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4377910601737780538765273 3283432951303335404073955)
              ·
                refine ⟨4925149426955003106110933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3283432951303335404073955 4925149426955003106110933)
                ·
                  refine ⟨115433189694257885299475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4925149426955003106110933 115433189694257885299475)
                  ·
                    rfl

theorem cell21_505812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 2, 1, 7].length) (baseStart_505812 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_505812 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_505812 prefixEnd_505812 := by exact prefixLift 505812
  have htrace : WordTrace (prefixWord ++ tailWord_505812) baseStart_505812 baseEnd_505812 := by
    simpa [prefixWord, tailWord_505812, baseEnd_505812] using wordTrace_append hprefix tailTrace_505812
  have hstable : (prefixWord ++ tailWord_505812).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_505812).length < 2 ^ (prefixWord ++ tailWord_505812).sum := by decide
  have hdescent : baseEnd_505812 < baseStart_505812 := by decide
  rcases family_descends (prefixWord ++ tailWord_505812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_505905 : List Nat := [1, 2, 2, 3, 1, 3, 2, 4, 3]
def baseStart_505905 : Nat := 118140960795 + 505905 * 2 ^ 59
def prefixEnd_505905 : Nat := 4983230072969 + 3 ^ 40 * 505905 * 2
def baseEnd_505905 : Nat := 115454413561310390249285

theorem tailTrace_505905 : CollatzResearch.WordTrace tailWord_505905 prefixEnd_505905 115454413561310390249285 := by
  unfold tailWord_505905
  simp only [CollatzResearch.WordTrace]
  refine ⟨18451871232200061540319169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12301247488133374360212779 18451871232200061540319169)
  ·
    refine ⟨13838903424150046155239377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18451871232200061540319169 13838903424150046155239377)
    ·
      refine ⟨10379177568112534616429533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13838903424150046155239377 10379177568112534616429533)
      ·
        refine ⟨3892191588042200481161075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10379177568112534616429533 3892191588042200481161075)
        ·
          refine ⟨5838287382063300721741613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3892191588042200481161075 5838287382063300721741613)
          ·
            refine ⟨2189357768273737770653105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5838287382063300721741613 2189357768273737770653105)
            ·
              refine ⟨1642018326205303327989829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2189357768273737770653105 1642018326205303327989829)
              ·
                refine ⟨307878436163494373998093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1642018326205303327989829 307878436163494373998093)
                ·
                  refine ⟨115454413561310390249285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 307878436163494373998093 115454413561310390249285)
                  ·
                    rfl

theorem cell21_505905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 2, 4, 3].length) (baseStart_505905 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_505905 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_505905 prefixEnd_505905 := by exact prefixLift 505905
  have htrace : WordTrace (prefixWord ++ tailWord_505905) baseStart_505905 baseEnd_505905 := by
    simpa [prefixWord, tailWord_505905, baseEnd_505905] using wordTrace_append hprefix tailTrace_505905
  have hstable : (prefixWord ++ tailWord_505905).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_505905).length < 2 ^ (prefixWord ++ tailWord_505905).sum := by decide
  have hdescent : baseEnd_505905 < baseStart_505905 := by decide
  rcases family_descends (prefixWord ++ tailWord_505905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_505964 : List Nat := [2, 2, 1, 1, 3, 3, 3, 1, 5]
def baseStart_505964 : Nat := 118140960795 + 505964 * 2 ^ 59
def prefixEnd_505964 : Nat := 4983230072969 + 3 ^ 40 * 505964 * 2
def baseEnd_505964 : Nat := 115467878165139398765831

theorem tailTrace_505964 : CollatzResearch.WordTrace tailWord_505964 prefixEnd_505964 115467878165139398765831 := by
  unfold tailWord_505964
  simp only [CollatzResearch.WordTrace]
  refine ⟨9227011569493157308358473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12302682092657543077811297 9227011569493157308358473)
  ·
    refine ⟨6920258677119867981268855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9227011569493157308358473 6920258677119867981268855)
    ·
      refine ⟨10380388015679801971903283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6920258677119867981268855 10380388015679801971903283)
      ·
        refine ⟨15570582023519702957854925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10380388015679801971903283 15570582023519702957854925)
        ·
          refine ⟨5838968258819888609195597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15570582023519702957854925 5838968258819888609195597)
          ·
            refine ⟨2189613097057458228448349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5838968258819888609195597 2189613097057458228448349)
            ·
              refine ⟨821104911396546835668131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2189613097057458228448349 821104911396546835668131)
              ·
                refine ⟨1231657367094820253502197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 821104911396546835668131 1231657367094820253502197)
                ·
                  refine ⟨115467878165139398765831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1231657367094820253502197 115467878165139398765831)
                  ·
                    rfl

theorem cell21_505964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 5].length) (baseStart_505964 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_505964 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_505964 prefixEnd_505964 := by exact prefixLift 505964
  have htrace : WordTrace (prefixWord ++ tailWord_505964) baseStart_505964 baseEnd_505964 := by
    simpa [prefixWord, tailWord_505964, baseEnd_505964] using wordTrace_append hprefix tailTrace_505964
  have hstable : (prefixWord ++ tailWord_505964).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_505964).length < 2 ^ (prefixWord ++ tailWord_505964).sum := by decide
  have hdescent : baseEnd_505964 < baseStart_505964 := by decide
  rcases family_descends (prefixWord ++ tailWord_505964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_506015 : List Nat := [1, 1, 2, 6, 1, 3, 2, 2, 3]
def baseStart_506015 : Nat := 118140960795 + 506015 * 2 ^ 59
def prefixEnd_506015 : Nat := 4983230072969 + 3 ^ 40 * 506015 * 2
def baseEnd_506015 : Nat := 115479517059974643415727

theorem tailTrace_506015 : CollatzResearch.WordTrace tailWord_506015 prefixEnd_506015 115479517059974643415727 := by
  unfold tailWord_506015
  simp only [CollatzResearch.WordTrace]
  refine ⟨18455883261801550326823499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12303922174534366884548999 18455883261801550326823499)
  ·
    refine ⟨27683824892702325490235249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18455883261801550326823499 27683824892702325490235249)
    ·
      refine ⟨20762868669526744117676437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27683824892702325490235249 20762868669526744117676437)
      ·
        refine ⟨973259468884066130516083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 20762868669526744117676437 973259468884066130516083)
        ·
          refine ⟨1459889203326099195774125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 973259468884066130516083 1459889203326099195774125)
          ·
            refine ⟨547458451247287198415297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1459889203326099195774125 547458451247287198415297)
            ·
              refine ⟨410593838435465398811473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 547458451247287198415297 410593838435465398811473)
              ·
                refine ⟨307945378826599049108605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 410593838435465398811473 307945378826599049108605)
                ·
                  refine ⟨115479517059974643415727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 307945378826599049108605 115479517059974643415727)
                  ·
                    rfl

theorem cell21_506015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 3, 2, 2, 3].length) (baseStart_506015 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_506015 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_506015 prefixEnd_506015 := by exact prefixLift 506015
  have htrace : WordTrace (prefixWord ++ tailWord_506015) baseStart_506015 baseEnd_506015 := by
    simpa [prefixWord, tailWord_506015, baseEnd_506015] using wordTrace_append hprefix tailTrace_506015
  have hstable : (prefixWord ++ tailWord_506015).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_506015).length < 2 ^ (prefixWord ++ tailWord_506015).sum := by decide
  have hdescent : baseEnd_506015 < baseStart_506015 := by decide
  rcases family_descends (prefixWord ++ tailWord_506015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_506088 : List Nat := [2, 1, 4, 1, 2, 3, 3, 1, 4]
def baseStart_506088 : Nat := 118140960795 + 506088 * 2 ^ 59
def prefixEnd_506088 : Nat := 4983230072969 + 3 ^ 40 * 506088 * 2
def baseEnd_506088 : Nat := 115496176654542738698911

theorem tailTrace_506088 : CollatzResearch.WordTrace tailWord_506088 prefixEnd_506088 115496176654542738698911 := by
  unfold tailWord_506088
  simp only [CollatzResearch.WordTrace]
  refine ⟨9229272895268541897115459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12305697193691389196153945 9229272895268541897115459)
  ·
    refine ⟨13843909342902812845673189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9229272895268541897115459 13843909342902812845673189)
    ·
      refine ⟨2595733001794277408563723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13843909342902812845673189 2595733001794277408563723)
      ·
        refine ⟨3893599502691416112845585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2595733001794277408563723 3893599502691416112845585)
        ·
          refine ⟨2920199627018562084634189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3893599502691416112845585 2920199627018562084634189)
          ·
            refine ⟨1095074860131960781737821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2920199627018562084634189 1095074860131960781737821)
            ·
              refine ⟨410653072549485293151683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1095074860131960781737821 410653072549485293151683)
              ·
                refine ⟨615979608824227939727525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 410653072549485293151683 615979608824227939727525)
                ·
                  refine ⟨115496176654542738698911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 615979608824227939727525 115496176654542738698911)
                  ·
                    rfl

theorem cell21_506088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 3, 1, 4].length) (baseStart_506088 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_506088 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_506088 prefixEnd_506088 := by exact prefixLift 506088
  have htrace : WordTrace (prefixWord ++ tailWord_506088) baseStart_506088 baseEnd_506088 := by
    simpa [prefixWord, tailWord_506088, baseEnd_506088] using wordTrace_append hprefix tailTrace_506088
  have hstable : (prefixWord ++ tailWord_506088).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_506088).length < 2 ^ (prefixWord ++ tailWord_506088).sum := by decide
  have hdescent : baseEnd_506088 < baseStart_506088 := by decide
  rcases family_descends (prefixWord ++ tailWord_506088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_506099 : List Nat := [1, 1, 1, 2, 2, 4, 1, 4, 5]
def baseStart_506099 : Nat := 118140960795 + 506099 * 2 ^ 59
def prefixEnd_506099 : Nat := 4983230072969 + 3 ^ 40 * 506099 * 2
def baseEnd_506099 : Nat := 115498687004409164015555

theorem tailTrace_506099 : CollatzResearch.WordTrace tailWord_506099 prefixEnd_506099 115498687004409164015555 := by
  unfold tailWord_506099
  simp only [CollatzResearch.WordTrace]
  refine ⟨18458946993497232672881351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12305964662331488448587567 18458946993497232672881351)
  ·
    refine ⟨27688420490245849009322027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18458946993497232672881351 27688420490245849009322027)
    ·
      refine ⟨41532630735368773513983041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27688420490245849009322027 41532630735368773513983041)
      ·
        refine ⟨31149473051526580135487281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41532630735368773513983041 31149473051526580135487281)
        ·
          refine ⟨23362104788644935101615461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31149473051526580135487281 23362104788644935101615461)
          ·
            refine ⟨4380394647870925331552899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23362104788644935101615461 4380394647870925331552899)
            ·
              refine ⟨6570591971806387997329349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4380394647870925331552899 6570591971806387997329349)
              ·
                refine ⟨1231985994713697749499253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6570591971806387997329349 1231985994713697749499253)
                ·
                  refine ⟨115498687004409164015555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1231985994713697749499253 115498687004409164015555)
                  ·
                    rfl

theorem cell21_506099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 4, 5].length) (baseStart_506099 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_506099 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_506099 prefixEnd_506099 := by exact prefixLift 506099
  have htrace : WordTrace (prefixWord ++ tailWord_506099) baseStart_506099 baseEnd_506099 := by
    simpa [prefixWord, tailWord_506099, baseEnd_506099] using wordTrace_append hprefix tailTrace_506099
  have hstable : (prefixWord ++ tailWord_506099).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_506099).length < 2 ^ (prefixWord ++ tailWord_506099).sum := by decide
  have hdescent : baseEnd_506099 < baseStart_506099 := by decide
  rcases family_descends (prefixWord ++ tailWord_506099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_506102 : List Nat := [5, 1, 1, 1, 1, 1, 6, 5]
def baseStart_506102 : Nat := 118140960795 + 506102 * 2 ^ 59
def prefixEnd_506102 : Nat := 4983230072969 + 3 ^ 40 * 506102 * 2
def baseEnd_506102 : Nat := 38499790548427275155183

theorem tailTrace_506102 : CollatzResearch.WordTrace tailWord_506102 prefixEnd_506102 38499790548427275155183 := by
  unfold tailWord_506102
  simp only [CollatzResearch.WordTrace]
  refine ⟨1153691025780397761577535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 12306037608324242790160373 1153691025780397761577535)
  ·
    refine ⟨1730536538670596642366303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1153691025780397761577535 1730536538670596642366303)
    ·
      refine ⟨2595804808005894963549455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1730536538670596642366303 2595804808005894963549455)
      ·
        refine ⟨3893707212008842445324183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2595804808005894963549455 3893707212008842445324183)
        ·
          refine ⟨5840560818013263667986275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3893707212008842445324183 5840560818013263667986275)
          ·
            refine ⟨8760841227019895501979413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5840560818013263667986275 8760841227019895501979413)
            ·
              refine ⟨410664432516557601655285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 8760841227019895501979413 410664432516557601655285)
              ·
                refine ⟨38499790548427275155183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 410664432516557601655285 38499790548427275155183)
                ·
                  rfl

theorem cell21_506102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 6, 5].length) (baseStart_506102 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_506102 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_506102 prefixEnd_506102 := by exact prefixLift 506102
  have htrace : WordTrace (prefixWord ++ tailWord_506102) baseStart_506102 baseEnd_506102 := by
    simpa [prefixWord, tailWord_506102, baseEnd_506102] using wordTrace_append hprefix tailTrace_506102
  have hstable : (prefixWord ++ tailWord_506102).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_506102).length < 2 ^ (prefixWord ++ tailWord_506102).sum := by decide
  have hdescent : baseEnd_506102 < baseStart_506102 := by decide
  rcases family_descends (prefixWord ++ tailWord_506102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_506119 : List Nat := [1, 1, 4, 5, 2, 1, 7]
def baseStart_506119 : Nat := 118140960795 + 506119 * 2 ^ 59
def prefixEnd_506119 : Nat := 4983230072969 + 3 ^ 40 * 506119 * 2
def baseEnd_506119 : Nat := 12833694586321508186909

theorem tailTrace_506119 : CollatzResearch.WordTrace tailWord_506119 prefixEnd_506119 12833694586321508186909 := by
  unfold tailWord_506119
  simp only [CollatzResearch.WordTrace]
  refine ⟨18459676453424776088609411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12306450968949850725739607 18459676453424776088609411)
  ·
    refine ⟨27689514680137164132914117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18459676453424776088609411 27689514680137164132914117)
    ·
      refine ⟨5191784002525718274921397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27689514680137164132914117 5191784002525718274921397)
      ·
        refine ⟨486729750236786088273881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 5191784002525718274921397 486729750236786088273881)
        ·
          refine ⟨365047312677589566205411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 486729750236786088273881 365047312677589566205411)
          ·
            refine ⟨547570969016384349308117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 365047312677589566205411 547570969016384349308117)
            ·
              refine ⟨12833694586321508186909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 547570969016384349308117 12833694586321508186909)
              ·
                rfl

theorem cell21_506119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 2, 1, 7].length) (baseStart_506119 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_506119 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_506119 prefixEnd_506119 := by exact prefixLift 506119
  have htrace : WordTrace (prefixWord ++ tailWord_506119) baseStart_506119 baseEnd_506119 := by
    simpa [prefixWord, tailWord_506119, baseEnd_506119] using wordTrace_append hprefix tailTrace_506119
  have hstable : (prefixWord ++ tailWord_506119).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_506119).length < 2 ^ (prefixWord ++ tailWord_506119).sum := by decide
  have hdescent : baseEnd_506119 < baseStart_506119 := by decide
  rcases family_descends (prefixWord ++ tailWord_506119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_506251 : List Nat := [1, 1, 1, 1, 4, 4, 1, 3, 5]
def baseStart_506251 : Nat := 118140960795 + 506251 * 2 ^ 59
def prefixEnd_506251 : Nat := 4983230072969 + 3 ^ 40 * 506251 * 2
def baseEnd_506251 : Nat := 115533375475290677481911

theorem tailTrace_506251 : CollatzResearch.WordTrace tailWord_506251 prefixEnd_506251 115533375475290677481911 := by
  unfold tailWord_506251
  simp only [CollatzResearch.WordTrace]
  refine ⟨18464490888946562632414607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12309660592631041754943071 18464490888946562632414607)
  ·
    refine ⟨27696736333419843948621911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18464490888946562632414607 27696736333419843948621911)
    ·
      refine ⟨41545104500129765922932867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27696736333419843948621911 41545104500129765922932867)
      ·
        refine ⟨62317656750194648884399301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41545104500129765922932867 62317656750194648884399301)
        ·
          refine ⟨11684560640661496665824869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62317656750194648884399301 11684560640661496665824869)
          ·
            refine ⟨2190855120124030624842163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11684560640661496665824869 2190855120124030624842163)
            ·
              refine ⟨3286282680186045937263245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2190855120124030624842163 3286282680186045937263245)
              ·
                refine ⟨1232356005069767226473717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3286282680186045937263245 1232356005069767226473717)
                ·
                  refine ⟨115533375475290677481911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1232356005069767226473717 115533375475290677481911)
                  ·
                    rfl

theorem cell21_506251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 1, 3, 5].length) (baseStart_506251 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_506251 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_506251 prefixEnd_506251 := by exact prefixLift 506251
  have htrace : WordTrace (prefixWord ++ tailWord_506251) baseStart_506251 baseEnd_506251 := by
    simpa [prefixWord, tailWord_506251, baseEnd_506251] using wordTrace_append hprefix tailTrace_506251
  have hstable : (prefixWord ++ tailWord_506251).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_506251).length < 2 ^ (prefixWord ++ tailWord_506251).sum := by decide
  have hdescent : baseEnd_506251 < baseStart_506251 := by decide
  rcases family_descends (prefixWord ++ tailWord_506251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_506361 : List Nat := [1, 2, 1, 3, 1, 2, 6, 2, 3]
def baseStart_506361 : Nat := 118140960795 + 506361 * 2 ^ 59
def prefixEnd_506361 : Nat := 4983230072969 + 3 ^ 40 * 506361 * 2
def baseEnd_506361 : Nat := 115558478973954930648353

theorem tailTrace_506361 : CollatzResearch.WordTrace tailWord_506361 prefixEnd_506361 115558478973954930648353 := by
  unfold tailWord_506361
  simp only [CollatzResearch.WordTrace]
  refine ⟨18468502918548051418918937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12312335279032034279279291 18468502918548051418918937)
  ·
    refine ⟨13851377188911038564189203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18468502918548051418918937 13851377188911038564189203)
    ·
      refine ⟨20777065783366557846283805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13851377188911038564189203 20777065783366557846283805)
      ·
        refine ⟨7791399668762459192356427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20777065783366557846283805 7791399668762459192356427)
        ·
          refine ⟨11687099503143688788534641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7791399668762459192356427 11687099503143688788534641)
          ·
            refine ⟨8765324627357766591400981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11687099503143688788534641 8765324627357766591400981)
            ·
              refine ⟨410874591907395308971921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 8765324627357766591400981 410874591907395308971921)
              ·
                refine ⟨308155943930546481728941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 410874591907395308971921 308155943930546481728941)
                ·
                  refine ⟨115558478973954930648353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 308155943930546481728941 115558478973954930648353)
                  ·
                    rfl

theorem cell21_506361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 6, 2, 3].length) (baseStart_506361 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_506361 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_506361 prefixEnd_506361 := by exact prefixLift 506361
  have htrace : WordTrace (prefixWord ++ tailWord_506361) baseStart_506361 baseEnd_506361 := by
    simpa [prefixWord, tailWord_506361, baseEnd_506361] using wordTrace_append hprefix tailTrace_506361
  have hstable : (prefixWord ++ tailWord_506361).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_506361).length < 2 ^ (prefixWord ++ tailWord_506361).sum := by decide
  have hdescent : baseEnd_506361 < baseStart_506361 := by decide
  rcases family_descends (prefixWord ++ tailWord_506361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_506389 : List Nat := [1, 3, 2, 1, 3, 1, 5, 5]
def baseStart_506389 : Nat := 118140960795 + 506389 * 2 ^ 59
def prefixEnd_506389 : Nat := 4983230072969 + 3 ^ 40 * 506389 * 2
def baseEnd_506389 : Nat := 38521622985144368060543

theorem tailTrace_506389 : CollatzResearch.WordTrace tailWord_506389 prefixEnd_506389 38521622985144368060543 := by
  unfold tailWord_506389
  simp only [CollatzResearch.WordTrace]
  refine ⟨18469524162446612200938221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12313016108297741467292147 18469524162446612200938221)
  ·
    refine ⟨6926071560917479575351833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18469524162446612200938221 6926071560917479575351833)
    ·
      refine ⟨5194553670688109681513875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6926071560917479575351833 5194553670688109681513875)
      ·
        refine ⟨7791830506032164522270813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5194553670688109681513875 7791830506032164522270813)
        ·
          refine ⟨2921936439762061695851555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7791830506032164522270813 2921936439762061695851555)
          ·
            refine ⟨4382904659643092543777333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2921936439762061695851555 4382904659643092543777333)
            ·
              refine ⟨410897311841539925979125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4382904659643092543777333 410897311841539925979125)
              ·
                refine ⟨38521622985144368060543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 410897311841539925979125 38521622985144368060543)
                ·
                  rfl

theorem cell21_506389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 5, 5].length) (baseStart_506389 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_506389 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_506389 prefixEnd_506389 := by exact prefixLift 506389
  have htrace : WordTrace (prefixWord ++ tailWord_506389) baseStart_506389 baseEnd_506389 := by
    simpa [prefixWord, tailWord_506389, baseEnd_506389] using wordTrace_append hprefix tailTrace_506389
  have hstable : (prefixWord ++ tailWord_506389).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_506389).length < 2 ^ (prefixWord ++ tailWord_506389).sum := by decide
  have hdescent : baseEnd_506389 < baseStart_506389 := by decide
  rcases family_descends (prefixWord ++ tailWord_506389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_506479 : List Nat := [1, 1, 2, 1, 3, 2, 5, 1, 5]
def baseStart_506479 : Nat := 118140960795 + 506479 * 2 ^ 59
def prefixEnd_506479 : Nat := 4983230072969 + 3 ^ 40 * 506479 * 2
def baseEnd_506479 : Nat := 115585408181612947681445

theorem tailTrace_506479 : CollatzResearch.WordTrace tailWord_506479 prefixEnd_506479 115585408181612947681445 := by
  unfold tailWord_506479
  simp only [CollatzResearch.WordTrace]
  refine ⟨18472806732120557571714491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12315204488080371714476327 18472806732120557571714491)
  ·
    refine ⟨27709210098180836357571737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18472806732120557571714491 27709210098180836357571737)
    ·
      refine ⟨20781907573635627268178803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27709210098180836357571737 20781907573635627268178803)
      ·
        refine ⟨31172861360453440902268205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20781907573635627268178803 31172861360453440902268205)
        ·
          refine ⟨11689823010170040338350577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31172861360453440902268205 11689823010170040338350577)
          ·
            refine ⟨8767367257627530253762933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11689823010170040338350577 8767367257627530253762933)
            ·
              refine ⟨821940680402580961290275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8767367257627530253762933 821940680402580961290275)
              ·
                refine ⟨1232911020603871441935413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 821940680402580961290275 1232911020603871441935413)
                ·
                  refine ⟨115585408181612947681445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1232911020603871441935413 115585408181612947681445)
                  ·
                    rfl

theorem cell21_506479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 5, 1, 5].length) (baseStart_506479 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_506479 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_506479 prefixEnd_506479 := by exact prefixLift 506479
  have htrace : WordTrace (prefixWord ++ tailWord_506479) baseStart_506479 baseEnd_506479 := by
    simpa [prefixWord, tailWord_506479, baseEnd_506479] using wordTrace_append hprefix tailTrace_506479
  have hstable : (prefixWord ++ tailWord_506479).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_506479).length < 2 ^ (prefixWord ++ tailWord_506479).sum := by decide
  have hdescent : baseEnd_506479 < baseStart_506479 := by decide
  rcases family_descends (prefixWord ++ tailWord_506479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_506485 : List Nat := [1, 3, 4, 2, 2, 2, 2, 1, 4]
def baseStart_506485 : Nat := 118140960795 + 506485 * 2 ^ 59
def prefixEnd_506485 : Nat := 4983230072969 + 3 ^ 40 * 506485 * 2
def baseEnd_506485 : Nat := 115586777463358270581433

theorem tailTrace_506485 : CollatzResearch.WordTrace tailWord_506485 prefixEnd_506485 115586777463358270581433 := by
  unfold tailWord_506485
  simp only [CollatzResearch.WordTrace]
  refine ⟨18473025570098820596432909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12315350380065880397621939 18473025570098820596432909)
  ·
    refine ⟨6927384588787057723662341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18473025570098820596432909 6927384588787057723662341)
    ·
      refine ⟨1298884610397573323186689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6927384588787057723662341 1298884610397573323186689)
      ·
        refine ⟨974163457798179992390017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1298884610397573323186689 974163457798179992390017)
        ·
          refine ⟨730622593348634994292513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 974163457798179992390017 730622593348634994292513)
          ·
            refine ⟨547966945011476245719385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 730622593348634994292513 547966945011476245719385)
            ·
              refine ⟨410975208758607184289539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 547966945011476245719385 410975208758607184289539)
              ·
                refine ⟨616462813137910776434309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 410975208758607184289539 616462813137910776434309)
                ·
                  refine ⟨115586777463358270581433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 616462813137910776434309 115586777463358270581433)
                  ·
                    rfl

theorem cell21_506485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 2, 2, 1, 4].length) (baseStart_506485 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_506485 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_506485 prefixEnd_506485 := by exact prefixLift 506485
  have htrace : WordTrace (prefixWord ++ tailWord_506485) baseStart_506485 baseEnd_506485 := by
    simpa [prefixWord, tailWord_506485, baseEnd_506485] using wordTrace_append hprefix tailTrace_506485
  have hstable : (prefixWord ++ tailWord_506485).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_506485).length < 2 ^ (prefixWord ++ tailWord_506485).sum := by decide
  have hdescent : baseEnd_506485 < baseStart_506485 := by decide
  rcases family_descends (prefixWord ++ tailWord_506485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_506524 : List Nat := [2, 2, 3, 2, 2, 10]
def baseStart_506524 : Nat := 118140960795 + 506524 * 2 ^ 59
def prefixEnd_506524 : Nat := 4983230072969 + 3 ^ 40 * 506524 * 2
def baseEnd_506524 : Nat := 4281321399803809978939

theorem tailTrace_506524 : CollatzResearch.WordTrace tailWord_506524 prefixEnd_506524 4281321399803809978939 := by
  unfold tailWord_506524
  simp only [CollatzResearch.WordTrace]
  refine ⟨9237224008478765128551313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12316298677971686838068417 9237224008478765128551313)
  ·
    refine ⟨6927918006359073846413485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9237224008478765128551313 6927918006359073846413485)
    ·
      refine ⟨2597969252384652692405057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6927918006359073846413485 2597969252384652692405057)
      ·
        refine ⟨1948476939288489519303793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2597969252384652692405057 1948476939288489519303793)
        ·
          refine ⟨1461357704466367139477845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1948476939288489519303793 1461357704466367139477845)
          ·
            refine ⟨4281321399803809978939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 1461357704466367139477845 4281321399803809978939)
            ·
              rfl

theorem cell21_506524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 10].length) (baseStart_506524 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_506524 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_506524 prefixEnd_506524 := by exact prefixLift 506524
  have htrace : WordTrace (prefixWord ++ tailWord_506524) baseStart_506524 baseEnd_506524 := by
    simpa [prefixWord, tailWord_506524, baseEnd_506524] using wordTrace_append hprefix tailTrace_506524
  have hstable : (prefixWord ++ tailWord_506524).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_506524).length < 2 ^ (prefixWord ++ tailWord_506524).sum := by decide
  have hdescent : baseEnd_506524 < baseStart_506524 := by decide
  rcases family_descends (prefixWord ++ tailWord_506524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_506541 : List Nat := [1, 5, 2, 1, 1, 2, 3, 6]
def baseStart_506541 : Nat := 118140960795 + 506541 * 2 ^ 59
def prefixEnd_506541 : Nat := 4983230072969 + 3 ^ 40 * 506541 * 2
def baseEnd_506541 : Nat := 38533185808771539215995

theorem tailTrace_506541 : CollatzResearch.WordTrace tailWord_506541 prefixEnd_506541 38533185808771539215995 := by
  unfold tailWord_506541
  simp only [CollatzResearch.WordTrace]
  refine ⟨18475068057895942160471477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12316712038597294773647651 18475068057895942160471477)
  ·
    refine ⟨1732037630427744577544201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 18475068057895942160471477 1732037630427744577544201)
    ·
      refine ⟨1299028222820808433158151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1732037630427744577544201 1299028222820808433158151)
      ·
        refine ⟨1948542334231212649737227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1299028222820808433158151 1948542334231212649737227)
        ·
          refine ⟨2922813501346818974605841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1948542334231212649737227 2922813501346818974605841)
          ·
            refine ⟨2192110126010114230954381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2922813501346818974605841 2192110126010114230954381)
            ·
              refine ⟨822041297253792836607893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2192110126010114230954381 822041297253792836607893)
              ·
                refine ⟨38533185808771539215995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 822041297253792836607893 38533185808771539215995)
                ·
                  rfl

theorem cell21_506541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 3, 6].length) (baseStart_506541 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_506541 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_506541 prefixEnd_506541 := by exact prefixLift 506541
  have htrace : WordTrace (prefixWord ++ tailWord_506541) baseStart_506541 baseEnd_506541 := by
    simpa [prefixWord, tailWord_506541, baseEnd_506541] using wordTrace_append hprefix tailTrace_506541
  have hstable : (prefixWord ++ tailWord_506541).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_506541).length < 2 ^ (prefixWord ++ tailWord_506541).sum := by decide
  have hdescent : baseEnd_506541 < baseStart_506541 := by decide
  rcases family_descends (prefixWord ++ tailWord_506541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_506645 : List Nat := [1, 3, 2, 1, 2, 2, 1, 3, 6]
def baseStart_506645 : Nat := 118140960795 + 506645 * 2 ^ 59
def prefixEnd_506645 : Nat := 4983230072969 + 3 ^ 40 * 506645 * 2
def baseEnd_506645 : Nat := 115623291643233547914439

theorem tailTrace_506645 : CollatzResearch.WordTrace tailWord_506645 prefixEnd_506645 115623291643233547914439 := by
  unfold tailWord_506645
  simp only [CollatzResearch.WordTrace]
  refine ⟨18478861249519167922257389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12319240833012778614838259 18478861249519167922257389)
  ·
    refine ⟨6929572968569687970846521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18478861249519167922257389 6929572968569687970846521)
    ·
      refine ⟨5197179726427265978134891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6929572968569687970846521 5197179726427265978134891)
      ·
        refine ⟨7795769589640898967202337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5197179726427265978134891 7795769589640898967202337)
        ·
          refine ⟨5846827192230674225401753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7795769589640898967202337 5846827192230674225401753)
          ·
            refine ⟨4385120394173005669051315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5846827192230674225401753 4385120394173005669051315)
            ·
              refine ⟨6577680591259508503576973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4385120394173005669051315 6577680591259508503576973)
              ·
                refine ⟨2466630221722315688841365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6577680591259508503576973 2466630221722315688841365)
                ·
                  refine ⟨115623291643233547914439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2466630221722315688841365 115623291643233547914439)
                  ·
                    rfl

theorem cell21_506645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 3, 6].length) (baseStart_506645 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_506645 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_506645 prefixEnd_506645 := by exact prefixLift 506645
  have htrace : WordTrace (prefixWord ++ tailWord_506645) baseStart_506645 baseEnd_506645 := by
    simpa [prefixWord, tailWord_506645, baseEnd_506645] using wordTrace_append hprefix tailTrace_506645
  have hstable : (prefixWord ++ tailWord_506645).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_506645).length < 2 ^ (prefixWord ++ tailWord_506645).sum := by decide
  have hdescent : baseEnd_506645 < baseStart_506645 := by decide
  rcases family_descends (prefixWord ++ tailWord_506645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_506735 : List Nat := [1, 1, 2, 1, 3, 1, 1, 11]
def baseStart_506735 : Nat := 118140960795 + 506735 * 2 ^ 59
def prefixEnd_506735 : Nat := 4983230072969 + 3 ^ 40 * 506735 * 2
def baseEnd_506735 : Nat := 38547943623137797138085

theorem tailTrace_506735 : CollatzResearch.WordTrace tailWord_506735 prefixEnd_506735 38547943623137797138085 := by
  unfold tailWord_506735
  simp only [CollatzResearch.WordTrace]
  refine ⟨18482143819193113293033659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12321429212795408862022439 18482143819193113293033659)
  ·
    refine ⟨27723215728789669939550489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18482143819193113293033659 27723215728789669939550489)
    ·
      refine ⟨20792411796592252454662867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27723215728789669939550489 20792411796592252454662867)
      ·
        refine ⟨31188617694888378681994301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20792411796592252454662867 31188617694888378681994301)
        ·
          refine ⟨11695731635583142005747863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31188617694888378681994301 11695731635583142005747863)
          ·
            refine ⟨17543597453374713008621795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11695731635583142005747863 17543597453374713008621795)
            ·
              refine ⟨26315396180062069512932693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17543597453374713008621795 26315396180062069512932693)
              ·
                refine ⟨38547943623137797138085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 26315396180062069512932693 38547943623137797138085)
                ·
                  rfl

theorem cell21_506735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 11].length) (baseStart_506735 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_506735 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_506735 prefixEnd_506735 := by exact prefixLift 506735
  have htrace : WordTrace (prefixWord ++ tailWord_506735) baseStart_506735 baseEnd_506735 := by
    simpa [prefixWord, tailWord_506735, baseEnd_506735] using wordTrace_append hprefix tailTrace_506735
  have hstable : (prefixWord ++ tailWord_506735).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_506735).length < 2 ^ (prefixWord ++ tailWord_506735).sum := by decide
  have hdescent : baseEnd_506735 < baseStart_506735 := by decide
  rcases family_descends (prefixWord ++ tailWord_506735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_506741 : List Nat := [1, 3, 4, 1, 1, 3, 2, 3, 3]
def baseStart_506741 : Nat := 118140960795 + 506741 * 2 ^ 59
def prefixEnd_506741 : Nat := 4983230072969 + 3 ^ 40 * 506741 * 2
def baseEnd_506741 : Nat := 115645200151158714314243

theorem tailTrace_506741 : CollatzResearch.WordTrace tailWord_506741 prefixEnd_506741 115645200151158714314243 := by
  unfold tailWord_506741
  simp only [CollatzResearch.WordTrace]
  refine ⟨18482362657171376317752077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12321575104780917545168051 18482362657171376317752077)
  ·
    refine ⟨6930885996439266119157029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18482362657171376317752077 6930885996439266119157029)
    ·
      refine ⟨1299541124332362397341943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6930885996439266119157029 1299541124332362397341943)
      ·
        refine ⟨1949311686498543596012915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1299541124332362397341943 1949311686498543596012915)
        ·
          refine ⟨2923967529747815394019373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1949311686498543596012915 2923967529747815394019373)
          ·
            refine ⟨1096487823655430772757265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2923967529747815394019373 1096487823655430772757265)
            ·
              refine ⟨822365867741573079567949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1096487823655430772757265 822365867741573079567949)
              ·
                refine ⟨308387200403089904837981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 822365867741573079567949 308387200403089904837981)
                ·
                  refine ⟨115645200151158714314243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 308387200403089904837981 115645200151158714314243)
                  ·
                    rfl

theorem cell21_506741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 2, 3, 3].length) (baseStart_506741 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_506741 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_506741 prefixEnd_506741 := by exact prefixLift 506741
  have htrace : WordTrace (prefixWord ++ tailWord_506741) baseStart_506741 baseEnd_506741 := by
    simpa [prefixWord, tailWord_506741, baseEnd_506741] using wordTrace_append hprefix tailTrace_506741
  have hstable : (prefixWord ++ tailWord_506741).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_506741).length < 2 ^ (prefixWord ++ tailWord_506741).sum := by decide
  have hdescent : baseEnd_506741 < baseStart_506741 := by decide
  rcases family_descends (prefixWord ++ tailWord_506741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_506783 : List Nat := [1, 1, 2, 5, 2, 1, 2, 2, 5]
def baseStart_506783 : Nat := 118140960795 + 506783 * 2 ^ 59
def prefixEnd_506783 : Nat := 4983230072969 + 3 ^ 40 * 506783 * 2
def baseEnd_506783 : Nat := 115654785123375974614157

theorem tailTrace_506783 : CollatzResearch.WordTrace tailWord_506783 prefixEnd_506783 115654785123375974614157 := by
  unfold tailWord_506783
  simp only [CollatzResearch.WordTrace]
  refine ⟨18483894523019217490781003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12322596348679478327187335 18483894523019217490781003)
  ·
    refine ⟨27725841784528826236171505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18483894523019217490781003 27725841784528826236171505)
    ·
      refine ⟨20794381338396619677128629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27725841784528826236171505 20794381338396619677128629)
      ·
        refine ⟨1949473250474683094730809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 20794381338396619677128629 1949473250474683094730809)
        ·
          refine ⟨1462104937856012321048107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1949473250474683094730809 1462104937856012321048107)
          ·
            refine ⟨2193157406784018481572161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1462104937856012321048107 2193157406784018481572161)
            ·
              refine ⟨1644868055088013861179121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2193157406784018481572161 1644868055088013861179121)
              ·
                refine ⟨1233651041316010395884341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1644868055088013861179121 1233651041316010395884341)
                ·
                  refine ⟨115654785123375974614157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1233651041316010395884341 115654785123375974614157)
                  ·
                    rfl

theorem cell21_506783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 2, 2, 5].length) (baseStart_506783 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_506783 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_506783 prefixEnd_506783 := by exact prefixLift 506783
  have htrace : WordTrace (prefixWord ++ tailWord_506783) baseStart_506783 baseEnd_506783 := by
    simpa [prefixWord, tailWord_506783, baseEnd_506783] using wordTrace_append hprefix tailTrace_506783
  have hstable : (prefixWord ++ tailWord_506783).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_506783).length < 2 ^ (prefixWord ++ tailWord_506783).sum := by decide
  have hdescent : baseEnd_506783 < baseStart_506783 := by decide
  rcases family_descends (prefixWord ++ tailWord_506783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_506786 : List Nat := [3, 3, 1, 2, 2, 3, 2, 5]
def baseStart_506786 : Nat := 118140960795 + 506786 * 2 ^ 59
def prefixEnd_506786 : Nat := 4983230072969 + 3 ^ 40 * 506786 * 2
def baseEnd_506786 : Nat := 38551823254749545354717

theorem tailTrace_506786 : CollatzResearch.WordTrace tailWord_506786 prefixEnd_506786 38551823254749545354717 := by
  unfold tailWord_506786
  simp only [CollatzResearch.WordTrace]
  refine ⟨4621000985502087250785053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12322669294672232668760141 4621000985502087250785053)
  ·
    refine ⟨1732875369563282719044395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4621000985502087250785053 1732875369563282719044395)
    ·
      refine ⟨2599313054344924078566593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1732875369563282719044395 2599313054344924078566593)
      ·
        refine ⟨1949484790758693058924945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2599313054344924078566593 1949484790758693058924945)
        ·
          refine ⟨1462113593069019794193709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1949484790758693058924945 1462113593069019794193709)
          ·
            refine ⟨548292597400882422822641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1462113593069019794193709 548292597400882422822641)
            ·
              refine ⟨411219448050661817116981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 548292597400882422822641 411219448050661817116981)
              ·
                refine ⟨38551823254749545354717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 411219448050661817116981 38551823254749545354717)
                ·
                  rfl

theorem cell21_506786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 3, 2, 5].length) (baseStart_506786 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_506786 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_506786 prefixEnd_506786 := by exact prefixLift 506786
  have htrace : WordTrace (prefixWord ++ tailWord_506786) baseStart_506786 baseEnd_506786 := by
    simpa [prefixWord, tailWord_506786, baseEnd_506786] using wordTrace_append hprefix tailTrace_506786
  have hstable : (prefixWord ++ tailWord_506786).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_506786).length < 2 ^ (prefixWord ++ tailWord_506786).sum := by decide
  have hdescent : baseEnd_506786 < baseStart_506786 := by decide
  rcases family_descends (prefixWord ++ tailWord_506786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_506814 : List Nat := [4, 2, 1, 1, 1, 2, 2, 4, 4]
def baseStart_506814 : Nat := 118140960795 + 506814 * 2 ^ 59
def prefixEnd_506814 : Nat := 4983230072969 + 3 ^ 40 * 506814 * 2
def baseEnd_506814 : Nat := 115661859745726809597427

theorem tailTrace_506814 : CollatzResearch.WordTrace tailWord_506814 prefixEnd_506814 115661859745726809597427 := by
  unfold tailWord_506814
  simp only [CollatzResearch.WordTrace]
  refine ⟨2310628148238363723144937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12323350123937939856772997 2310628148238363723144937)
  ·
    refine ⟨1732971111178772792358703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2310628148238363723144937 1732971111178772792358703)
    ·
      refine ⟨2599456666768159188538055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1732971111178772792358703 2599456666768159188538055)
      ·
        refine ⟨3899185000152238782807083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2599456666768159188538055 3899185000152238782807083)
        ·
          refine ⟨5848777500228358174210625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3899185000152238782807083 5848777500228358174210625)
          ·
            refine ⟨4386583125171268630657969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5848777500228358174210625 4386583125171268630657969)
            ·
              refine ⟨3289937343878451472993477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4386583125171268630657969 3289937343878451472993477)
              ·
                refine ⟨616863251977209651186277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3289937343878451472993477 616863251977209651186277)
                ·
                  refine ⟨115661859745726809597427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 616863251977209651186277 115661859745726809597427)
                  ·
                    rfl

theorem cell21_506814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 2, 4, 4].length) (baseStart_506814 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_506814 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_506814 prefixEnd_506814 := by exact prefixLift 506814
  have htrace : WordTrace (prefixWord ++ tailWord_506814) baseStart_506814 baseEnd_506814 := by
    simpa [prefixWord, tailWord_506814, baseEnd_506814] using wordTrace_append hprefix tailTrace_506814
  have hstable : (prefixWord ++ tailWord_506814).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_506814).length < 2 ^ (prefixWord ++ tailWord_506814).sum := by decide
  have hdescent : baseEnd_506814 < baseStart_506814 := by decide
  rcases family_descends (prefixWord ++ tailWord_506814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_506828 : List Nat := [2, 2, 1, 4, 1, 1, 4, 6]
def baseStart_506828 : Nat := 118140960795 + 506828 * 2 ^ 59
def prefixEnd_506828 : Nat := 4983230072969 + 3 ^ 40 * 506828 * 2
def baseEnd_506828 : Nat := 38555018245488632121355

theorem tailTrace_506828 : CollatzResearch.WordTrace tailWord_506828 prefixEnd_506828 38555018245488632121355 := by
  unfold tailWord_506828
  simp only [CollatzResearch.WordTrace]
  refine ⟨9242767903928095088084569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12323690538570793450779425 9242767903928095088084569)
  ·
    refine ⟨6932075927946071316063427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9242767903928095088084569 6932075927946071316063427)
    ·
      refine ⟨10398113891919106974095141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6932075927946071316063427 10398113891919106974095141)
      ·
        refine ⟨1949646354734832557642839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10398113891919106974095141 1949646354734832557642839)
        ·
          refine ⟨2924469532102248836464259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1949646354734832557642839 2924469532102248836464259)
          ·
            refine ⟨4386704298153373254696389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2924469532102248836464259 4386704298153373254696389)
            ·
              refine ⟨822507055903757485255573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4386704298153373254696389 822507055903757485255573)
              ·
                refine ⟨38555018245488632121355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 822507055903757485255573 38555018245488632121355)
                ·
                  rfl

theorem cell21_506828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 4, 6].length) (baseStart_506828 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_506828 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_506828 prefixEnd_506828 := by exact prefixLift 506828
  have htrace : WordTrace (prefixWord ++ tailWord_506828) baseStart_506828 baseEnd_506828 := by
    simpa [prefixWord, tailWord_506828, baseEnd_506828] using wordTrace_append hprefix tailTrace_506828
  have hstable : (prefixWord ++ tailWord_506828).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_506828).length < 2 ^ (prefixWord ++ tailWord_506828).sum := by decide
  have hdescent : baseEnd_506828 < baseStart_506828 := by decide
  rcases family_descends (prefixWord ++ tailWord_506828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_506831 : List Nat := [1, 1, 2, 1, 1, 8, 2, 1, 4]
def baseStart_506831 : Nat := 118140960795 + 506831 * 2 ^ 59
def prefixEnd_506831 : Nat := 4983230072969 + 3 ^ 40 * 506831 * 2
def baseEnd_506831 : Nat := 115665739377338557814059

theorem tailTrace_506831 : CollatzResearch.WordTrace tailWord_506831 prefixEnd_506831 115665739377338557814059 := by
  unfold tailWord_506831
  simp only [CollatzResearch.WordTrace]
  refine ⟨18485645226845321688528347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12323763484563547792352231 18485645226845321688528347)
  ·
    refine ⟨27728467840267982532792521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18485645226845321688528347 27728467840267982532792521)
    ·
      refine ⟨20796350880200986899594391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27728467840267982532792521 20796350880200986899594391)
      ·
        refine ⟨31194526320301480349391587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20796350880200986899594391 31194526320301480349391587)
        ·
          refine ⟨46791789480452220524087381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31194526320301480349391587 46791789480452220524087381)
          ·
            refine ⟨548341282974049459266649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 46791789480452220524087381 548341282974049459266649)
            ·
              refine ⟨411255962230537094449987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 548341282974049459266649 411255962230537094449987)
              ·
                refine ⟨616883943345805641674981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 411255962230537094449987 616883943345805641674981)
                ·
                  refine ⟨115665739377338557814059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 616883943345805641674981 115665739377338557814059)
                  ·
                    rfl

theorem cell21_506831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 8, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 8, 2, 1, 4].length) (baseStart_506831 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_506831 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_506831 prefixEnd_506831 := by exact prefixLift 506831
  have htrace : WordTrace (prefixWord ++ tailWord_506831) baseStart_506831 baseEnd_506831 := by
    simpa [prefixWord, tailWord_506831, baseEnd_506831] using wordTrace_append hprefix tailTrace_506831
  have hstable : (prefixWord ++ tailWord_506831).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_506831).length < 2 ^ (prefixWord ++ tailWord_506831).sum := by decide
  have hdescent : baseEnd_506831 < baseStart_506831 := by decide
  rcases family_descends (prefixWord ++ tailWord_506831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_506868 : List Nat := [2, 6, 2, 1, 1, 1, 1, 4, 3]
def baseStart_506868 : Nat := 118140960795 + 506868 * 2 ^ 59
def prefixEnd_506868 : Nat := 4983230072969 + 3 ^ 40 * 506868 * 2
def baseEnd_506868 : Nat := 115674183281434715697317

theorem tailTrace_506868 : CollatzResearch.WordTrace tailWord_506868 prefixEnd_506868 115674183281434715697317 := by
  unfold tailWord_506868
  simp only [CollatzResearch.WordTrace]
  refine ⟨9243497363855638503812629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12324663151807518005083505 9243497363855638503812629)
  ·
    refine ⟨433288938930733054866217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 9243497363855638503812629 433288938930733054866217)
    ·
      refine ⟨324966704198049791149663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 433288938930733054866217 324966704198049791149663)
      ·
        refine ⟨487450056297074686724495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 324966704198049791149663 487450056297074686724495)
        ·
          refine ⟨731175084445612030086743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 487450056297074686724495 731175084445612030086743)
          ·
            refine ⟨1096762626668418045130115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 731175084445612030086743 1096762626668418045130115)
            ·
              refine ⟨1645143940002627067695173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1096762626668418045130115 1645143940002627067695173)
              ·
                refine ⟨308464488750492575192845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1645143940002627067695173 308464488750492575192845)
                ·
                  refine ⟨115674183281434715697317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 308464488750492575192845 115674183281434715697317)
                  ·
                    rfl

theorem cell21_506868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 1, 4, 3].length) (baseStart_506868 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_506868 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_506868 prefixEnd_506868 := by exact prefixLift 506868
  have htrace : WordTrace (prefixWord ++ tailWord_506868) baseStart_506868 baseEnd_506868 := by
    simpa [prefixWord, tailWord_506868, baseEnd_506868] using wordTrace_append hprefix tailTrace_506868
  have hstable : (prefixWord ++ tailWord_506868).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_506868).length < 2 ^ (prefixWord ++ tailWord_506868).sum := by decide
  have hdescent : baseEnd_506868 < baseStart_506868 := by decide
  rcases family_descends (prefixWord ++ tailWord_506868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_506876 : List Nat := [2, 2, 2, 1, 2, 4, 1, 4, 3]
def baseStart_506876 : Nat := 118140960795 + 506876 * 2 ^ 59
def prefixEnd_506876 : Nat := 4983230072969 + 3 ^ 40 * 506876 * 2
def baseEnd_506876 : Nat := 115676008990428479563967

theorem tailTrace_506876 : CollatzResearch.WordTrace tailWord_506876 prefixEnd_506876 115676008990428479563967 := by
  unfold tailWord_506876
  simp only [CollatzResearch.WordTrace]
  refine ⟨9243643255841147186958241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12324857674454862915944321 9243643255841147186958241)
  ·
    refine ⟨6932732441880860390218681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9243643255841147186958241 6932732441880860390218681)
    ·
      refine ⟨5199549331410645292664011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6932732441880860390218681 5199549331410645292664011)
      ·
        refine ⟨7799323997115967938996017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5199549331410645292664011 7799323997115967938996017)
        ·
          refine ⟨5849492997836975954247013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7799323997115967938996017 5849492997836975954247013)
          ·
            refine ⟨1096779937094432991421315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5849492997836975954247013 1096779937094432991421315)
            ·
              refine ⟨1645169905641649487131973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1096779937094432991421315 1645169905641649487131973)
              ·
                refine ⟨308469357307809278837245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1645169905641649487131973 308469357307809278837245)
                ·
                  refine ⟨115676008990428479563967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 308469357307809278837245 115676008990428479563967)
                  ·
                    rfl

theorem cell21_506876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 1, 4, 3].length) (baseStart_506876 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_506876 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_506876 prefixEnd_506876 := by exact prefixLift 506876
  have htrace : WordTrace (prefixWord ++ tailWord_506876) baseStart_506876 baseEnd_506876 := by
    simpa [prefixWord, tailWord_506876, baseEnd_506876] using wordTrace_append hprefix tailTrace_506876
  have hstable : (prefixWord ++ tailWord_506876).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_506876).length < 2 ^ (prefixWord ++ tailWord_506876).sum := by decide
  have hdescent : baseEnd_506876 < baseStart_506876 := by decide
  rcases family_descends (prefixWord ++ tailWord_506876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_506890 : List Nat := [3, 1, 2, 2, 3, 1, 2, 3, 4]
def baseStart_506890 : Nat := 118140960795 + 506890 * 2 ^ 59
def prefixEnd_506890 : Nat := 4983230072969 + 3 ^ 40 * 506890 * 2
def baseEnd_506890 : Nat := 115679203981167566330605

theorem tailTrace_506890 : CollatzResearch.WordTrace tailWord_506890 prefixEnd_506890 115679203981167566330605 := by
  unfold tailWord_506890
  simp only [CollatzResearch.WordTrace]
  refine ⟨4621949283407893691231531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12325198089087716509950749 4621949283407893691231531)
  ·
    refine ⟨6932923925111840536847297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4621949283407893691231531 6932923925111840536847297)
    ·
      refine ⟨5199692943833880402635473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6932923925111840536847297 5199692943833880402635473)
      ·
        refine ⟨3899769707875410301976605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5199692943833880402635473 3899769707875410301976605)
        ·
          refine ⟨1462413640453278863241227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3899769707875410301976605 1462413640453278863241227)
          ·
            refine ⟨2193620460679918294861841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1462413640453278863241227 2193620460679918294861841)
            ·
              refine ⟨1645215345509938721146381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2193620460679918294861841 1645215345509938721146381)
              ·
                refine ⟨616955754566227020429893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1645215345509938721146381 616955754566227020429893)
                ·
                  refine ⟨115679203981167566330605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 616955754566227020429893 115679203981167566330605)
                  ·
                    rfl

theorem cell21_506890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 2, 3, 4].length) (baseStart_506890 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_506890 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_506890 prefixEnd_506890 := by exact prefixLift 506890
  have htrace : WordTrace (prefixWord ++ tailWord_506890) baseStart_506890 baseEnd_506890 := by
    simpa [prefixWord, tailWord_506890, baseEnd_506890] using wordTrace_append hprefix tailTrace_506890
  have hstable : (prefixWord ++ tailWord_506890).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_506890).length < 2 ^ (prefixWord ++ tailWord_506890).sum := by decide
  have hdescent : baseEnd_506890 < baseStart_506890 := by decide
  rcases family_descends (prefixWord ++ tailWord_506890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_506949 : List Nat := [1, 3, 1, 1, 1, 3, 2, 5, 4]
def baseStart_506949 : Nat := 118140960795 + 506949 * 2 ^ 59
def prefixEnd_506949 : Nat := 4983230072969 + 3 ^ 40 * 506949 * 2
def baseEnd_506949 : Nat := 115692668584996574847151

theorem tailTrace_506949 : CollatzResearch.WordTrace tailWord_506949 prefixEnd_506949 115692668584996574847151 := by
  unfold tailWord_506949
  simp only [CollatzResearch.WordTrace]
  refine ⟨18489949040417827841323901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12326632693611885227549267 18489949040417827841323901)
  ·
    refine ⟨6933730890156685440496463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18489949040417827841323901 6933730890156685440496463)
    ·
      refine ⟨10400596335235028160744695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6933730890156685440496463 10400596335235028160744695)
      ·
        refine ⟨15600894502852542241117043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10400596335235028160744695 15600894502852542241117043)
        ·
          refine ⟨23401341754278813361675565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15600894502852542241117043 23401341754278813361675565)
          ·
            refine ⟨8775503157854555010628337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23401341754278813361675565 8775503157854555010628337)
            ·
              refine ⟨6581627368390916257971253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8775503157854555010628337 6581627368390916257971253)
              ·
                refine ⟨617027565786648399184805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6581627368390916257971253 617027565786648399184805)
                ·
                  refine ⟨115692668584996574847151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 617027565786648399184805 115692668584996574847151)
                  ·
                    rfl

theorem cell21_506949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 5, 4].length) (baseStart_506949 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_506949 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_506949 prefixEnd_506949 := by exact prefixLift 506949
  have htrace : WordTrace (prefixWord ++ tailWord_506949) baseStart_506949 baseEnd_506949 := by
    simpa [prefixWord, tailWord_506949, baseEnd_506949] using wordTrace_append hprefix tailTrace_506949
  have hstable : (prefixWord ++ tailWord_506949).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_506949).length < 2 ^ (prefixWord ++ tailWord_506949).sum := by decide
  have hdescent : baseEnd_506949 < baseStart_506949 := by decide
  rcases family_descends (prefixWord ++ tailWord_506949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_507039 : List Nat := [1, 1, 2, 6, 11]
def baseStart_507039 : Nat := 118140960795 + 507039 * 2 ^ 59
def prefixEnd_507039 : Nat := 4983230072969 + 3 ^ 40 * 507039 * 2
def baseEnd_507039 : Nat := 1428558121125634794407

theorem tailTrace_507039 : CollatzResearch.WordTrace tailWord_507039 prefixEnd_507039 1428558121125634794407 := by
  unfold tailWord_507039
  simp only [CollatzResearch.WordTrace]
  refine ⟨18493231610091773212100171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12328821073394515474733447 18493231610091773212100171)
  ·
    refine ⟨27739847415137659818150257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18493231610091773212100171 27739847415137659818150257)
    ·
      refine ⟨20804885561353244863612693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27739847415137659818150257 20804885561353244863612693)
      ·
        refine ⟨975229010688433352981845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 20804885561353244863612693 975229010688433352981845)
        ·
          refine ⟨1428558121125634794407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 975229010688433352981845 1428558121125634794407)
          ·
            rfl

theorem cell21_507039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 11].length) (baseStart_507039 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_507039 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_507039 prefixEnd_507039 := by exact prefixLift 507039
  have htrace : WordTrace (prefixWord ++ tailWord_507039) baseStart_507039 baseEnd_507039 := by
    simpa [prefixWord, tailWord_507039, baseEnd_507039] using wordTrace_append hprefix tailTrace_507039
  have hstable : (prefixWord ++ tailWord_507039).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_507039).length < 2 ^ (prefixWord ++ tailWord_507039).sum := by decide
  have hdescent : baseEnd_507039 < baseStart_507039 := by decide
  rcases family_descends (prefixWord ++ tailWord_507039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_507045 : List Nat := [1, 3, 1, 2, 1, 6, 2, 2, 3]
def baseStart_507045 : Nat := 118140960795 + 507045 * 2 ^ 59
def prefixEnd_507045 : Nat := 4983230072969 + 3 ^ 40 * 507045 * 2
def baseEnd_507045 : Nat := 115714577092921741246955

theorem tailTrace_507045 : CollatzResearch.WordTrace tailWord_507045 prefixEnd_507045 115714577092921741246955 := by
  unfold tailWord_507045
  simp only [CollatzResearch.WordTrace]
  refine ⟨18493450448070036236818589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12328966965380024157879059 18493450448070036236818589)
  ·
    refine ⟨6935043918026263588806971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18493450448070036236818589 6935043918026263588806971)
    ·
      refine ⟨10402565877039395383210457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6935043918026263588806971 10402565877039395383210457)
      ·
        refine ⟨7801924407779546537407843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10402565877039395383210457 7801924407779546537407843)
        ·
          refine ⟨11702886611669319806111765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7801924407779546537407843 11702886611669319806111765)
          ·
            refine ⟨548572809921999365911489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 11702886611669319806111765 548572809921999365911489)
            ·
              refine ⟨411429607441499524433617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 548572809921999365911489 411429607441499524433617)
              ·
                refine ⟨308572205581124643325213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 411429607441499524433617 308572205581124643325213)
                ·
                  refine ⟨115714577092921741246955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 308572205581124643325213 115714577092921741246955)
                  ·
                    rfl

theorem cell21_507045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 6, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 6, 2, 2, 3].length) (baseStart_507045 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_507045 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_507045 prefixEnd_507045 := by exact prefixLift 507045
  have htrace : WordTrace (prefixWord ++ tailWord_507045) baseStart_507045 baseEnd_507045 := by
    simpa [prefixWord, tailWord_507045, baseEnd_507045] using wordTrace_append hprefix tailTrace_507045
  have hstable : (prefixWord ++ tailWord_507045).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_507045).length < 2 ^ (prefixWord ++ tailWord_507045).sum := by decide
  have hdescent : baseEnd_507045 < baseStart_507045 := by decide
  rcases family_descends (prefixWord ++ tailWord_507045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_507124 : List Nat := [2, 6, 1, 2, 1, 2, 2, 5]
def baseStart_507124 : Nat := 118140960795 + 507124 * 2 ^ 59
def prefixEnd_507124 : Nat := 4983230072969 + 3 ^ 40 * 507124 * 2
def baseEnd_507124 : Nat := 38577535323078386476709

theorem tailTrace_507124 : CollatzResearch.WordTrace tailWord_507124 prefixEnd_507124 38577535323078386476709 := by
  unfold tailWord_507124
  simp only [CollatzResearch.WordTrace]
  refine ⟨9248165907391916364472213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12330887876522555152629617 9248165907391916364472213)
  ·
    refine ⟨433507776908996079584635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 9248165907391916364472213 433507776908996079584635)
    ·
      refine ⟨650261665363494119376953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 433507776908996079584635 650261665363494119376953)
      ·
        refine ⟨487696249022620589532715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 650261665363494119376953 487696249022620589532715)
        ·
          refine ⟨731544373533930884299073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 487696249022620589532715 731544373533930884299073)
          ·
            refine ⟨548658280150448163224305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 731544373533930884299073 548658280150448163224305)
            ·
              refine ⟨411493710112836122418229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 548658280150448163224305 411493710112836122418229)
              ·
                refine ⟨38577535323078386476709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 411493710112836122418229 38577535323078386476709)
                ·
                  rfl

theorem cell21_507124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 2, 2, 5].length) (baseStart_507124 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_507124 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_507124 prefixEnd_507124 := by exact prefixLift 507124
  have htrace : WordTrace (prefixWord ++ tailWord_507124) baseStart_507124 baseEnd_507124 := by
    simpa [prefixWord, tailWord_507124, baseEnd_507124] using wordTrace_append hprefix tailTrace_507124
  have hstable : (prefixWord ++ tailWord_507124).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_507124).length < 2 ^ (prefixWord ++ tailWord_507124).sum := by decide
  have hdescent : baseEnd_507124 < baseStart_507124 := by decide
  rcases family_descends (prefixWord ++ tailWord_507124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_507132 : List Nat := [2, 2, 2, 1, 5, 1, 1, 7]
def baseStart_507132 : Nat := 118140960795 + 507132 * 2 ^ 59
def prefixEnd_507132 : Nat := 4983230072969 + 3 ^ 40 * 507132 * 2
def baseEnd_507132 : Nat := 38578143892742974432259

theorem tailTrace_507132 : CollatzResearch.WordTrace tailWord_507132 prefixEnd_507132 38578143892742974432259 := by
  unfold tailWord_507132
  simp only [CollatzResearch.WordTrace]
  refine ⟨9248311799377425047617825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12331082399169900063490433 9248311799377425047617825)
  ·
    refine ⟨6936233849533068785713369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9248311799377425047617825 6936233849533068785713369)
    ·
      refine ⟨5202175387149801589285027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6936233849533068785713369 5202175387149801589285027)
      ·
        refine ⟨7803263080724702383927541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5202175387149801589285027 7803263080724702383927541)
        ·
          refine ⟨731555913817940848493207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7803263080724702383927541 731555913817940848493207)
          ·
            refine ⟨1097333870726911272739811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 731555913817940848493207 1097333870726911272739811)
            ·
              refine ⟨1646000806090366909109717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1097333870726911272739811 1646000806090366909109717)
              ·
                refine ⟨38578143892742974432259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1646000806090366909109717 38578143892742974432259)
                ·
                  rfl

theorem cell21_507132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 1, 7].length) (baseStart_507132 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_507132 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_507132 prefixEnd_507132 := by exact prefixLift 507132
  have htrace : WordTrace (prefixWord ++ tailWord_507132) baseStart_507132 baseEnd_507132 := by
    simpa [prefixWord, tailWord_507132, baseEnd_507132] using wordTrace_append hprefix tailTrace_507132
  have hstable : (prefixWord ++ tailWord_507132).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_507132).length < 2 ^ (prefixWord ++ tailWord_507132).sum := by decide
  have hdescent : baseEnd_507132 < baseStart_507132 := by decide
  rcases family_descends (prefixWord ++ tailWord_507132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_507138 : List Nat := [3, 4, 1, 1, 3, 2, 1, 3, 3]
def baseStart_507138 : Nat := 118140960795 + 507138 * 2 ^ 59
def prefixEnd_507138 : Nat := 4983230072969 + 3 ^ 40 * 507138 * 2
def baseEnd_507138 : Nat := 115735800959974246196765

theorem tailTrace_507138 : CollatzResearch.WordTrace tailWord_507138 prefixEnd_507138 115735800959974246196765 := by
  unfold tailWord_507138
  simp only [CollatzResearch.WordTrace]
  refine ⟨4624210609183278279988517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12331228291155408746636045 4624210609183278279988517)
  ·
    refine ⟨867039489221864677497847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4624210609183278279988517 867039489221864677497847)
    ·
      refine ⟨1300559233832797016246771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 867039489221864677497847 1300559233832797016246771)
      ·
        refine ⟨1950838850749195524370157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1300559233832797016246771 1950838850749195524370157)
        ·
          refine ⟨731564569030948321638809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1950838850749195524370157 731564569030948321638809)
          ·
            refine ⟨548673426773211241229107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 731564569030948321638809 548673426773211241229107)
            ·
              refine ⟨823010140159816861843661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 548673426773211241229107 823010140159816861843661)
              ·
                refine ⟨308628802559931323191373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 823010140159816861843661 308628802559931323191373)
                ·
                  refine ⟨115735800959974246196765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 308628802559931323191373 115735800959974246196765)
                  ·
                    rfl

theorem cell21_507138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 2, 1, 3, 3].length) (baseStart_507138 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_507138 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_507138 prefixEnd_507138 := by exact prefixLift 507138
  have htrace : WordTrace (prefixWord ++ tailWord_507138) baseStart_507138 baseEnd_507138 := by
    simpa [prefixWord, tailWord_507138, baseEnd_507138] using wordTrace_append hprefix tailTrace_507138
  have hstable : (prefixWord ++ tailWord_507138).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_507138).length < 2 ^ (prefixWord ++ tailWord_507138).sum := by decide
  have hdescent : baseEnd_507138 < baseStart_507138 := by decide
  rcases family_descends (prefixWord ++ tailWord_507138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_507166 : List Nat := [4, 3, 2, 1, 2, 1, 2, 6]
def baseStart_507166 : Nat := 118140960795 + 507166 * 2 ^ 59
def prefixEnd_507166 : Nat := 4983230072969 + 3 ^ 40 * 507166 * 2
def baseEnd_507166 : Nat := 38580730313817473243347

theorem tailTrace_507166 : CollatzResearch.WordTrace tailWord_507166 prefixEnd_507166 38580730313817473243347 := by
  unfold tailWord_507166
  simp only [CollatzResearch.WordTrace]
  refine ⟨2312232960078959237746669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12331909120421115934648901 2312232960078959237746669)
  ·
    refine ⟨867087360029609714155001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2312232960078959237746669 867087360029609714155001)
    ·
      refine ⟨650315520022207285616251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 867087360029609714155001 650315520022207285616251)
      ·
        refine ⟨975473280033310928424377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 650315520022207285616251 975473280033310928424377)
        ·
          refine ⟨731604960024983196318283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 975473280033310928424377 731604960024983196318283)
          ·
            refine ⟨1097407440037474794477425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 731604960024983196318283 1097407440037474794477425)
            ·
              refine ⟨823055580028106095858069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1097407440037474794477425 823055580028106095858069)
              ·
                refine ⟨38580730313817473243347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 823055580028106095858069 38580730313817473243347)
                ·
                  rfl

theorem cell21_507166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 2, 6].length) (baseStart_507166 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_507166 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_507166 prefixEnd_507166 := by exact prefixLift 507166
  have htrace : WordTrace (prefixWord ++ tailWord_507166) baseStart_507166 baseEnd_507166 := by
    simpa [prefixWord, tailWord_507166, baseEnd_507166] using wordTrace_append hprefix tailTrace_507166
  have hstable : (prefixWord ++ tailWord_507166).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_507166).length < 2 ^ (prefixWord ++ tailWord_507166).sum := by decide
  have hdescent : baseEnd_507166 < baseStart_507166 := by decide
  rcases family_descends (prefixWord ++ tailWord_507166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_507239 : List Nat := [1, 1, 5, 1, 4, 1, 1, 2, 5]
def baseStart_507239 : Nat := 118140960795 + 507239 * 2 ^ 59
def prefixEnd_507239 : Nat := 4983230072969 + 3 ^ 40 * 507239 * 2
def baseEnd_507239 : Nat := 115758850536020515013225

theorem tailTrace_507239 : CollatzResearch.WordTrace tailWord_507239 prefixEnd_507239 115758850536020515013225 := by
  unfold tailWord_507239
  simp only [CollatzResearch.WordTrace]
  refine ⟨18500526209367207369380771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12333684139578138246253847 18500526209367207369380771)
  ·
    refine ⟨27750789314050811054071157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18500526209367207369380771 27750789314050811054071157)
    ·
      refine ⟨2601636498192263536319171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 27750789314050811054071157 2601636498192263536319171)
      ·
        refine ⟨3902454747288395304478757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2601636498192263536319171 3902454747288395304478757)
        ·
          refine ⟨731710265116574119589767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3902454747288395304478757 731710265116574119589767)
          ·
            refine ⟨1097565397674861179384651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 731710265116574119589767 1097565397674861179384651)
            ·
              refine ⟨1646348096512291769076977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1097565397674861179384651 1646348096512291769076977)
              ·
                refine ⟨1234761072384218826807733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1646348096512291769076977 1234761072384218826807733)
                ·
                  refine ⟨115758850536020515013225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1234761072384218826807733 115758850536020515013225)
                  ·
                    rfl

theorem cell21_507239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 1, 2, 5].length) (baseStart_507239 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_507239 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_507239 prefixEnd_507239 := by exact prefixLift 507239
  have htrace : WordTrace (prefixWord ++ tailWord_507239) baseStart_507239 baseEnd_507239 := by
    simpa [prefixWord, tailWord_507239, baseEnd_507239] using wordTrace_append hprefix tailTrace_507239
  have hstable : (prefixWord ++ tailWord_507239).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_507239).length < 2 ^ (prefixWord ++ tailWord_507239).sum := by decide
  have hdescent : baseEnd_507239 < baseStart_507239 := by decide
  rcases family_descends (prefixWord ++ tailWord_507239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_507267 : List Nat := [1, 1, 1, 3, 5, 2, 8]
def baseStart_507267 : Nat := 118140960795 + 507267 * 2 ^ 59
def prefixEnd_507267 : Nat := 4983230072969 + 3 ^ 40 * 507267 * 2
def baseEnd_507267 : Nat := 12862804501944298727389

theorem tailTrace_507267 : CollatzResearch.WordTrace tailWord_507267 prefixEnd_507267 12862804501944298727389 := by
  unfold tailWord_507267
  simp only [CollatzResearch.WordTrace]
  refine ⟨18501547453265768151400055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12334364968843845434266703 18501547453265768151400055)
  ·
    refine ⟨27752321179898652227100083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18501547453265768151400055 27752321179898652227100083)
    ·
      refine ⟨41628481769847978340650125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27752321179898652227100083 41628481769847978340650125)
      ·
        refine ⟨15610680663692991877743797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41628481769847978340650125 15610680663692991877743797)
        ·
          refine ⟨1463501312221217988538481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 15610680663692991877743797 1463501312221217988538481)
          ·
            refine ⟨1097625984165913491403861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1463501312221217988538481 1097625984165913491403861)
            ·
              refine ⟨12862804501944298727389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1097625984165913491403861 12862804501944298727389)
              ·
                rfl

theorem cell21_507267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 8].length) (baseStart_507267 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_507267 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_507267 prefixEnd_507267 := by exact prefixLift 507267
  have htrace : WordTrace (prefixWord ++ tailWord_507267) baseStart_507267 baseEnd_507267 := by
    simpa [prefixWord, tailWord_507267, baseEnd_507267] using wordTrace_append hprefix tailTrace_507267
  have hstable : (prefixWord ++ tailWord_507267).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_507267).length < 2 ^ (prefixWord ++ tailWord_507267).sum := by decide
  have hdescent : baseEnd_507267 < baseStart_507267 := by decide
  rcases family_descends (prefixWord ++ tailWord_507267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_507281 : List Nat := [1, 2, 2, 1, 1, 1, 2, 2, 9]
def baseStart_507281 : Nat := 118140960795 + 507281 * 2 ^ 59
def prefixEnd_507281 : Nat := 4983230072969 + 3 ^ 40 * 507281 * 2
def baseEnd_507281 : Nat := 115768435508237775313139

theorem tailTrace_507281 : CollatzResearch.WordTrace tailWord_507281 prefixEnd_507281 115768435508237775313139 := by
  unfold tailWord_507281
  simp only [CollatzResearch.WordTrace]
  refine ⟨18502058075215048542409697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12334705383476699028273131 18502058075215048542409697)
  ·
    refine ⟨13876543556411286406807273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18502058075215048542409697 13876543556411286406807273)
    ·
      refine ⟨10407407667308464805105455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13876543556411286406807273 10407407667308464805105455)
      ·
        refine ⟨15611111500962697207658183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10407407667308464805105455 15611111500962697207658183)
        ·
          refine ⟨23416667251444045811487275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15611111500962697207658183 23416667251444045811487275)
          ·
            refine ⟨35125000877166068717230913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23416667251444045811487275 35125000877166068717230913)
            ·
              refine ⟨26343750657874551537923185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35125000877166068717230913 26343750657874551537923185)
              ·
                refine ⟨19757812993405913653442389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26343750657874551537923185 19757812993405913653442389)
                ·
                  refine ⟨115768435508237775313139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 19757812993405913653442389 115768435508237775313139)
                  ·
                    rfl

theorem cell21_507281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 2, 9].length) (baseStart_507281 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_507281 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_507281 prefixEnd_507281 := by exact prefixLift 507281
  have htrace : WordTrace (prefixWord ++ tailWord_507281) baseStart_507281 baseEnd_507281 := by
    simpa [prefixWord, tailWord_507281, baseEnd_507281] using wordTrace_append hprefix tailTrace_507281
  have hstable : (prefixWord ++ tailWord_507281).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_507281).length < 2 ^ (prefixWord ++ tailWord_507281).sum := by decide
  have hdescent : baseEnd_507281 < baseStart_507281 := by decide
  rcases family_descends (prefixWord ++ tailWord_507281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_507332 : List Nat := [2, 3, 3, 2, 1, 3, 1, 1, 5]
def baseStart_507332 : Nat := 118140960795 + 507332 * 2 ^ 59
def prefixEnd_507332 : Nat := 4983230072969 + 3 ^ 40 * 507332 * 2
def baseEnd_507332 : Nat := 115780074403073019963035

theorem tailTrace_507332 : CollatzResearch.WordTrace tailWord_507332 prefixEnd_507332 115780074403073019963035 := by
  unfold tailWord_507332
  simp only [CollatzResearch.WordTrace]
  refine ⟨9251959099015142126258125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12335945465353522835010833 9251959099015142126258125)
  ·
    refine ⟨3469484662130678297346797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9251959099015142126258125 3469484662130678297346797)
    ·
      refine ⟨1301056748299004361505049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3469484662130678297346797 1301056748299004361505049)
      ·
        refine ⟨975792561224253271128787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1301056748299004361505049 975792561224253271128787)
        ·
          refine ⟨1463688841836379906693181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 975792561224253271128787 1463688841836379906693181)
          ·
            refine ⟨548883315688642465009943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1463688841836379906693181 548883315688642465009943)
            ·
              refine ⟨823324973532963697514915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 548883315688642465009943 823324973532963697514915)
              ·
                refine ⟨1234987460299445546272373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 823324973532963697514915 1234987460299445546272373)
                ·
                  refine ⟨115780074403073019963035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1234987460299445546272373 115780074403073019963035)
                  ·
                    rfl

theorem cell21_507332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 3, 1, 1, 5].length) (baseStart_507332 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_507332 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_507332 prefixEnd_507332 := by exact prefixLift 507332
  have htrace : WordTrace (prefixWord ++ tailWord_507332) baseStart_507332 baseEnd_507332 := by
    simpa [prefixWord, tailWord_507332, baseEnd_507332] using wordTrace_append hprefix tailTrace_507332
  have hstable : (prefixWord ++ tailWord_507332).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_507332).length < 2 ^ (prefixWord ++ tailWord_507332).sum := by decide
  have hdescent : baseEnd_507332 < baseStart_507332 := by decide
  rcases family_descends (prefixWord ++ tailWord_507332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_507388 : List Nat := [2, 2, 2, 1, 2, 1, 2, 3, 6]
def baseStart_507388 : Nat := 118140960795 + 507388 * 2 ^ 59
def prefixEnd_507388 : Nat := 4983230072969 + 3 ^ 40 * 507388 * 2
def baseEnd_507388 : Nat := 115792854366029367029587

theorem tailTrace_507388 : CollatzResearch.WordTrace tailWord_507388 prefixEnd_507388 115792854366029367029587 := by
  unfold tailWord_507388
  simp only [CollatzResearch.WordTrace]
  refine ⟨9252980342913702908277409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12337307123884937211036545 9252980342913702908277409)
  ·
    refine ⟨6939735257185277181208057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9252980342913702908277409 6939735257185277181208057)
    ·
      refine ⟨5204801442888957885906043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6939735257185277181208057 5204801442888957885906043)
      ·
        refine ⟨7807202164333436828859065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5204801442888957885906043 7807202164333436828859065)
        ·
          refine ⟨5855401623250077621644299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7807202164333436828859065 5855401623250077621644299)
          ·
            refine ⟨8783102434875116432466449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5855401623250077621644299 8783102434875116432466449)
            ·
              refine ⟨6587326826156337324349837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8783102434875116432466449 6587326826156337324349837)
              ·
                refine ⟨2470247559808626496631189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6587326826156337324349837 2470247559808626496631189)
                ·
                  refine ⟨115792854366029367029587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2470247559808626496631189 115792854366029367029587)
                  ·
                    rfl

theorem cell21_507388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 3, 6].length) (baseStart_507388 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_507388 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_507388 prefixEnd_507388 := by exact prefixLift 507388
  have htrace : WordTrace (prefixWord ++ tailWord_507388) baseStart_507388 baseEnd_507388 := by
    simpa [prefixWord, tailWord_507388, baseEnd_507388] using wordTrace_append hprefix tailTrace_507388
  have hstable : (prefixWord ++ tailWord_507388).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_507388).length < 2 ^ (prefixWord ++ tailWord_507388).sum := by decide
  have hdescent : baseEnd_507388 < baseStart_507388 := by decide
  rcases family_descends (prefixWord ++ tailWord_507388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_507450 : List Nat := [3, 1, 1, 1, 3, 2, 4, 1, 5]
def baseStart_507450 : Nat := 118140960795 + 507450 * 2 ^ 59
def prefixEnd_507450 : Nat := 4983230072969 + 3 ^ 40 * 507450 * 2
def baseEnd_507450 : Nat := 115807003610731036996127

theorem tailTrace_507450 : CollatzResearch.WordTrace tailWord_507450 prefixEnd_507450 115807003610731036996127 := by
  unfold tailWord_507450
  simp only [CollatzResearch.WordTrace]
  refine ⟨4627055502900697601327951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12338814674401860270207869 4627055502900697601327951)
  ·
    refine ⟨6940583254351046401991927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4627055502900697601327951 6940583254351046401991927)
    ·
      refine ⟨10410874881526569602987891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6940583254351046401991927 10410874881526569602987891)
      ·
        refine ⟨15616312322289854404481837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10410874881526569602987891 15616312322289854404481837)
        ·
          refine ⟨5856117120858695401680689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15616312322289854404481837 5856117120858695401680689)
          ·
            refine ⟨4392087840644021551260517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5856117120858695401680689 4392087840644021551260517)
            ·
              refine ⟨823516470120754040861347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4392087840644021551260517 823516470120754040861347)
              ·
                refine ⟨1235274705181131061292021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 823516470120754040861347 1235274705181131061292021)
                ·
                  refine ⟨115807003610731036996127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1235274705181131061292021 115807003610731036996127)
                  ·
                    rfl

theorem cell21_507450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 4, 1, 5].length) (baseStart_507450 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_507450 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_507450 prefixEnd_507450 := by exact prefixLift 507450
  have htrace : WordTrace (prefixWord ++ tailWord_507450) baseStart_507450 baseEnd_507450 := by
    simpa [prefixWord, tailWord_507450, baseEnd_507450] using wordTrace_append hprefix tailTrace_507450
  have hstable : (prefixWord ++ tailWord_507450).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_507450).length < 2 ^ (prefixWord ++ tailWord_507450).sum := by decide
  have hdescent : baseEnd_507450 < baseStart_507450 := by decide
  rcases family_descends (prefixWord ++ tailWord_507450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_507484 : List Nat := [2, 2, 4, 1, 2, 1, 3, 3, 3]
def baseStart_507484 : Nat := 118140960795 + 507484 * 2 ^ 59
def prefixEnd_507484 : Nat := 4983230072969 + 3 ^ 40 * 507484 * 2
def baseEnd_507484 : Nat := 115814762873954533429391

theorem tailTrace_507484 : CollatzResearch.WordTrace tailWord_507484 prefixEnd_507484 115814762873954533429391 := by
  unfold tailWord_507484
  simp only [CollatzResearch.WordTrace]
  refine ⟨9254731046739807106024753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12339641395653076141366337 9254731046739807106024753)
  ·
    refine ⟨6941048285054855329518565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9254731046739807106024753 6941048285054855329518565)
    ·
      refine ⟨1301446553447785374284731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6941048285054855329518565 1301446553447785374284731)
      ·
        refine ⟨1952169830171678061427097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1301446553447785374284731 1952169830171678061427097)
        ·
          refine ⟨1464127372628758546070323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1952169830171678061427097 1464127372628758546070323)
          ·
            refine ⟨2196191058943137819105485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1464127372628758546070323 2196191058943137819105485)
            ·
              refine ⟨823571647103676682164557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2196191058943137819105485 823571647103676682164557)
              ·
                refine ⟨308839367663878755811709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 823571647103676682164557 308839367663878755811709)
                ·
                  refine ⟨115814762873954533429391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 308839367663878755811709 115814762873954533429391)
                  ·
                    rfl

theorem cell21_507484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 3, 3, 3].length) (baseStart_507484 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_507484 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_507484 prefixEnd_507484 := by exact prefixLift 507484
  have htrace : WordTrace (prefixWord ++ tailWord_507484) baseStart_507484 baseEnd_507484 := by
    simpa [prefixWord, tailWord_507484, baseEnd_507484] using wordTrace_append hprefix tailTrace_507484
  have hstable : (prefixWord ++ tailWord_507484).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_507484).length < 2 ^ (prefixWord ++ tailWord_507484).sum := by decide
  have hdescent : baseEnd_507484 < baseStart_507484 := by decide
  rcases family_descends (prefixWord ++ tailWord_507484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_507501 : List Nat := [1, 5, 1, 1, 4, 1, 3, 2, 3]
def baseStart_507501 : Nat := 118140960795 + 507501 * 2 ^ 59
def prefixEnd_507501 : Nat := 4983230072969 + 3 ^ 40 * 507501 * 2
def baseEnd_507501 : Nat := 115818642505566281646023

theorem tailTrace_507501 : CollatzResearch.WordTrace tailWord_507501 prefixEnd_507501 115818642505566281646023 := by
  unfold tailWord_507501
  simp only [CollatzResearch.WordTrace]
  refine ⟨18510082134418026115418357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12340054756278684076945571 18510082134418026115418357)
  ·
    refine ⟨1735320200101689948320471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 18510082134418026115418357 1735320200101689948320471)
    ·
      refine ⟨2602980300152534922480707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1735320200101689948320471 2602980300152534922480707)
      ·
        refine ⟨3904470450228802383721061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2602980300152534922480707 3904470450228802383721061)
        ·
          refine ⟨732088209417900446947699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3904470450228802383721061 732088209417900446947699)
          ·
            refine ⟨1098132314126850670421549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 732088209417900446947699 1098132314126850670421549)
            ·
              refine ⟨411799617797569001408081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1098132314126850670421549 411799617797569001408081)
              ·
                refine ⟨308849713348176751056061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 411799617797569001408081 308849713348176751056061)
                ·
                  refine ⟨115818642505566281646023, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 308849713348176751056061 115818642505566281646023)
                  ·
                    rfl

theorem cell21_507501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 3, 2, 3].length) (baseStart_507501 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_507501 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_507501 prefixEnd_507501 := by exact prefixLift 507501
  have htrace : WordTrace (prefixWord ++ tailWord_507501) baseStart_507501 baseEnd_507501 := by
    simpa [prefixWord, tailWord_507501, baseEnd_507501] using wordTrace_append hprefix tailTrace_507501
  have hstable : (prefixWord ++ tailWord_507501).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_507501).length < 2 ^ (prefixWord ++ tailWord_507501).sum := by decide
  have hdescent : baseEnd_507501 < baseStart_507501 := by decide
  rcases family_descends (prefixWord ++ tailWord_507501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_507588 : List Nat := [2, 3, 3, 1, 1, 1, 5, 5]
def baseStart_507588 : Nat := 118140960795 + 507588 * 2 ^ 59
def prefixEnd_507588 : Nat := 4983230072969 + 3 ^ 40 * 507588 * 2
def baseEnd_507588 : Nat := 38612832363624487898615

theorem tailTrace_507588 : CollatzResearch.WordTrace tailWord_507588 prefixEnd_507588 38612832363624487898615 := by
  unfold tailWord_507588
  simp only [CollatzResearch.WordTrace]
  refine ⟨9256627642551419986917709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12342170190068559982556945 9256627642551419986917709)
  ·
    refine ⟨3471235365956782495094141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9256627642551419986917709 3471235365956782495094141)
    ·
      refine ⟨1301713262233793435660303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3471235365956782495094141 1301713262233793435660303)
      ·
        refine ⟨1952569893350690153490455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1301713262233793435660303 1952569893350690153490455)
        ·
          refine ⟨2928854840026035230235683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1952569893350690153490455 2928854840026035230235683)
          ·
            refine ⟨4393282260039052845353525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2928854840026035230235683 4393282260039052845353525)
            ·
              refine ⟨411870211878661204251893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4393282260039052845353525 411870211878661204251893)
              ·
                refine ⟨38612832363624487898615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 411870211878661204251893 38612832363624487898615)
                ·
                  rfl

theorem cell21_507588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 5, 5].length) (baseStart_507588 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_507588 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_507588 prefixEnd_507588 := by exact prefixLift 507588
  have htrace : WordTrace (prefixWord ++ tailWord_507588) baseStart_507588 baseEnd_507588 := by
    simpa [prefixWord, tailWord_507588, baseEnd_507588] using wordTrace_append hprefix tailTrace_507588
  have hstable : (prefixWord ++ tailWord_507588).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_507588).length < 2 ^ (prefixWord ++ tailWord_507588).sum := by decide
  have hdescent : baseEnd_507588 < baseStart_507588 := by decide
  rcases family_descends (prefixWord ++ tailWord_507588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_507619 : List Nat := [1, 1, 1, 7, 2, 1, 2, 1, 5]
def baseStart_507619 : Nat := 118140960795 + 507619 * 2 ^ 59
def prefixEnd_507619 : Nat := 4983230072969 + 3 ^ 40 * 507619 * 2
def baseEnd_507619 : Nat := 115845571713224298679115

theorem tailTrace_507619 : CollatzResearch.WordTrace tailWord_507619 prefixEnd_507619 115845571713224298679115 := by
  unfold tailWord_507619
  simp only [CollatzResearch.WordTrace]
  refine ⟨18514385947990532268213911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12342923965327021512142607 18514385947990532268213911)
  ·
    refine ⟨27771578921985798402320867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18514385947990532268213911 27771578921985798402320867)
    ·
      refine ⟨41657368382978697603481301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27771578921985798402320867 41657368382978697603481301)
      ·
        refine ⟨976344571476063225081593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 41657368382978697603481301 976344571476063225081593)
        ·
          refine ⟨732258428607047418811195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 976344571476063225081593 732258428607047418811195)
          ·
            refine ⟨1098387642910571128216793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 732258428607047418811195 1098387642910571128216793)
            ·
              refine ⟨823790732182928346162595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1098387642910571128216793 823790732182928346162595)
              ·
                refine ⟨1235686098274392519243893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 823790732182928346162595 1235686098274392519243893)
                ·
                  refine ⟨115845571713224298679115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1235686098274392519243893 115845571713224298679115)
                  ·
                    rfl

theorem cell21_507619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 2, 1, 5].length) (baseStart_507619 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_507619 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_507619 prefixEnd_507619 := by exact prefixLift 507619
  have htrace : WordTrace (prefixWord ++ tailWord_507619) baseStart_507619 baseEnd_507619 := by
    simpa [prefixWord, tailWord_507619, baseEnd_507619] using wordTrace_append hprefix tailTrace_507619
  have hstable : (prefixWord ++ tailWord_507619).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_507619).length < 2 ^ (prefixWord ++ tailWord_507619).sum := by decide
  have hdescent : baseEnd_507619 < baseStart_507619 := by decide
  rcases family_descends (prefixWord ++ tailWord_507619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_507636 : List Nat := [2, 6, 1, 1, 1, 1, 2, 2, 5]
def baseStart_507636 : Nat := 118140960795 + 507636 * 2 ^ 59
def prefixEnd_507636 : Nat := 4983230072969 + 3 ^ 40 * 507636 * 2
def baseEnd_507636 : Nat := 115849451344836046895747

theorem tailTrace_507636 : CollatzResearch.WordTrace tailWord_507636 prefixEnd_507636 115849451344836046895747 := by
  unfold tailWord_507636
  simp only [CollatzResearch.WordTrace]
  refine ⟨9257502994464472085791381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12343337325952629447721841 9257502994464472085791381)
  ·
    refine ⟨433945452865522129021471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 9257502994464472085791381 433945452865522129021471)
    ·
      refine ⟨650918179298283193532207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 433945452865522129021471 650918179298283193532207)
      ·
        refine ⟨976377268947424790298311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 650918179298283193532207 976377268947424790298311)
        ·
          refine ⟨1464565903421137185447467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 976377268947424790298311 1464565903421137185447467)
          ·
            refine ⟨2196848855131705778171201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1464565903421137185447467 2196848855131705778171201)
            ·
              refine ⟨1647636641348779333628401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2196848855131705778171201 1647636641348779333628401)
              ·
                refine ⟨1235727481011584500221301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1647636641348779333628401 1235727481011584500221301)
                ·
                  refine ⟨115849451344836046895747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1235727481011584500221301 115849451344836046895747)
                  ·
                    rfl

theorem cell21_507636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 2, 2, 5].length) (baseStart_507636 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_507636 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_507636 prefixEnd_507636 := by exact prefixLift 507636
  have htrace : WordTrace (prefixWord ++ tailWord_507636) baseStart_507636 baseEnd_507636 := by
    simpa [prefixWord, tailWord_507636, baseEnd_507636] using wordTrace_append hprefix tailTrace_507636
  have hstable : (prefixWord ++ tailWord_507636).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_507636).length < 2 ^ (prefixWord ++ tailWord_507636).sum := by decide
  have hdescent : baseEnd_507636 < baseStart_507636 := by decide
  rcases family_descends (prefixWord ++ tailWord_507636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_507647 : List Nat := [1, 1, 2, 2, 1, 3, 6, 5]
def baseStart_507647 : Nat := 118140960795 + 507647 * 2 ^ 59
def prefixEnd_507647 : Nat := 4983230072969 + 3 ^ 40 * 507647 * 2
def baseEnd_507647 : Nat := 38617320564900824070797

theorem tailTrace_507647 : CollatzResearch.WordTrace tailWord_507647 prefixEnd_507647 38617320564900824070797 := by
  unfold tailWord_507647
  simp only [CollatzResearch.WordTrace]
  refine ⟨18515407191889093050233195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12343604794592728700155463 18515407191889093050233195)
  ·
    refine ⟨27773110787833639575349793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18515407191889093050233195 27773110787833639575349793)
    ·
      refine ⟨20829833090875229681512345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27773110787833639575349793 20829833090875229681512345)
      ·
        refine ⟨15622374818156422261134259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20829833090875229681512345 15622374818156422261134259)
        ·
          refine ⟨23433562227234633391701389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15622374818156422261134259 23433562227234633391701389)
          ·
            refine ⟨8787585835212987521888021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23433562227234633391701389 8787585835212987521888021)
            ·
              refine ⟨411918086025608790088501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 8787585835212987521888021 411918086025608790088501)
              ·
                refine ⟨38617320564900824070797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 411918086025608790088501 38617320564900824070797)
                ·
                  rfl

theorem cell21_507647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 6, 5].length) (baseStart_507647 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_507647 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_507647 prefixEnd_507647 := by exact prefixLift 507647
  have htrace : WordTrace (prefixWord ++ tailWord_507647) baseStart_507647 baseEnd_507647 := by
    simpa [prefixWord, tailWord_507647, baseEnd_507647] using wordTrace_append hprefix tailTrace_507647
  have hstable : (prefixWord ++ tailWord_507647).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_507647).length < 2 ^ (prefixWord ++ tailWord_507647).sum := by decide
  have hdescent : baseEnd_507647 < baseStart_507647 := by decide
  rcases family_descends (prefixWord ++ tailWord_507647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_507737 : List Nat := [1, 2, 1, 2, 2, 3, 2, 3, 5]
def baseStart_507737 : Nat := 118140960795 + 507737 * 2 ^ 59
def prefixEnd_507737 : Nat := 4983230072969 + 3 ^ 40 * 507737 * 2
def baseEnd_507737 : Nat := 115872500920882315712207

theorem tailTrace_507737 : CollatzResearch.WordTrace tailWord_507737 prefixEnd_507737 115872500920882315712207 := by
  unfold tailWord_507737
  simp only [CollatzResearch.WordTrace]
  refine ⟨18518689761563038421009465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12345793174375358947339643 18518689761563038421009465)
  ·
    refine ⟨13889017321172278815757099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18518689761563038421009465 13889017321172278815757099)
    ·
      refine ⟨20833525981758418223635649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13889017321172278815757099 20833525981758418223635649)
      ·
        refine ⟨15625144486318813667726737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20833525981758418223635649 15625144486318813667726737)
        ·
          refine ⟨11718858364739110250795053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15625144486318813667726737 11718858364739110250795053)
          ·
            refine ⟨4394571886777166344048145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11718858364739110250795053 4394571886777166344048145)
            ·
              refine ⟨3295928915082874758036109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4394571886777166344048145 3295928915082874758036109)
              ·
                refine ⟨1235973343156078034263541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3295928915082874758036109 1235973343156078034263541)
                ·
                  refine ⟨115872500920882315712207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1235973343156078034263541 115872500920882315712207)
                  ·
                    rfl

theorem cell21_507737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 2, 3, 5].length) (baseStart_507737 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_507737 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_507737 prefixEnd_507737 := by exact prefixLift 507737
  have htrace : WordTrace (prefixWord ++ tailWord_507737) baseStart_507737 baseEnd_507737 := by
    simpa [prefixWord, tailWord_507737, baseEnd_507737] using wordTrace_append hprefix tailTrace_507737
  have hstable : (prefixWord ++ tailWord_507737).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_507737).length < 2 ^ (prefixWord ++ tailWord_507737).sum := by decide
  have hdescent : baseEnd_507737 < baseStart_507737 := by decide
  rcases family_descends (prefixWord ++ tailWord_507737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_507802 : List Nat := [3, 1, 1, 4, 2, 2, 3, 1, 4]
def baseStart_507802 : Nat := 118140960795 + 507802 * 2 ^ 59
def prefixEnd_507802 : Nat := 4983230072969 + 3 ^ 40 * 507802 * 2
def baseEnd_507802 : Nat := 115887334806456647128741

theorem tailTrace_507802 : CollatzResearch.WordTrace tailWord_507802 prefixEnd_507802 115887334806456647128741 := by
  unfold tailWord_507802
  simp only [CollatzResearch.WordTrace]
  refine ⟨4630265126581888630531415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12347373670885036348083773 4630265126581888630531415)
  ·
    refine ⟨6945397689872832945797123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4630265126581888630531415 6945397689872832945797123)
    ·
      refine ⟨10418096534809249418695685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6945397689872832945797123 10418096534809249418695685)
      ·
        refine ⟨1953393100276734266005441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10418096534809249418695685 1953393100276734266005441)
        ·
          refine ⟨1465044825207550699504081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1953393100276734266005441 1465044825207550699504081)
          ·
            refine ⟨1098783618905663024628061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1465044825207550699504081 1098783618905663024628061)
            ·
              refine ⟨412043857089623634235523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1098783618905663024628061 412043857089623634235523)
              ·
                refine ⟨618065785634435451353285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 412043857089623634235523 618065785634435451353285)
                ·
                  refine ⟨115887334806456647128741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 618065785634435451353285 115887334806456647128741)
                  ·
                    rfl

theorem cell21_507802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 3, 1, 4].length) (baseStart_507802 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_507802 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_507802 prefixEnd_507802 := by exact prefixLift 507802
  have htrace : WordTrace (prefixWord ++ tailWord_507802) baseStart_507802 baseEnd_507802 := by
    simpa [prefixWord, tailWord_507802, baseEnd_507802] using wordTrace_append hprefix tailTrace_507802
  have hstable : (prefixWord ++ tailWord_507802).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_507802).length < 2 ^ (prefixWord ++ tailWord_507802).sum := by decide
  have hdescent : baseEnd_507802 < baseStart_507802 := by decide
  rcases family_descends (prefixWord ++ tailWord_507802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_507827 : List Nat := [1, 1, 1, 2, 3, 1, 3, 1, 8]
def baseStart_507827 : Nat := 118140960795 + 507827 * 2 ^ 59
def prefixEnd_507827 : Nat := 4983230072969 + 3 ^ 40 * 507827 * 2
def baseEnd_507827 : Nat := 115893040147062159212023

theorem tailTrace_507827 : CollatzResearch.WordTrace tailWord_507827 prefixEnd_507827 115893040147062159212023 := by
  unfold tailWord_507827
  simp only [CollatzResearch.WordTrace]
  refine ⟨18521972331236983791785735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12347981554157989194523823 18521972331236983791785735)
  ·
    refine ⟨27782958496855475687678603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18521972331236983791785735 27782958496855475687678603)
    ·
      refine ⟨41674437745283213531517905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27782958496855475687678603 41674437745283213531517905)
      ·
        refine ⟨31255828308962410148638429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41674437745283213531517905 31255828308962410148638429)
        ·
          refine ⟨11720935615860903805739411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31255828308962410148638429 11720935615860903805739411)
          ·
            refine ⟨17581403423791355708609117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11720935615860903805739411 17581403423791355708609117)
            ·
              refine ⟨6593026283921758390728419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17581403423791355708609117 6593026283921758390728419)
              ·
                refine ⟨9889539425882637586092629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6593026283921758390728419 9889539425882637586092629)
                ·
                  refine ⟨115893040147062159212023, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 9889539425882637586092629 115893040147062159212023)
                  ·
                    rfl

theorem cell21_507827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 1, 8].length) (baseStart_507827 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_507827 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_507827 prefixEnd_507827 := by exact prefixLift 507827
  have htrace : WordTrace (prefixWord ++ tailWord_507827) baseStart_507827 baseEnd_507827 := by
    simpa [prefixWord, tailWord_507827, baseEnd_507827] using wordTrace_append hprefix tailTrace_507827
  have hstable : (prefixWord ++ tailWord_507827).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_507827).length < 2 ^ (prefixWord ++ tailWord_507827).sum := by decide
  have hdescent : baseEnd_507827 < baseStart_507827 := by decide
  rcases family_descends (prefixWord ++ tailWord_507827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_507861 : List Nat := [1, 3, 2, 3, 2, 2, 1, 3, 4]
def baseStart_507861 : Nat := 118140960795 + 507861 * 2 ^ 59
def prefixEnd_507861 : Nat := 4983230072969 + 3 ^ 40 * 507861 * 2
def baseEnd_507861 : Nat := 115900799410285655645287

theorem tailTrace_507861 : CollatzResearch.WordTrace tailWord_507861 prefixEnd_507861 115900799410285655645287 := by
  unfold tailWord_507861
  simp only [CollatzResearch.WordTrace]
  refine ⟨18523212413113807598523437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12348808275409205065682291 18523212413113807598523437)
  ·
    refine ⟨6946204654917677849446289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18523212413113807598523437 6946204654917677849446289)
    ·
      refine ⟨5209653491188258387084717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6946204654917677849446289 5209653491188258387084717)
      ·
        refine ⟨1953620059195596895156769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5209653491188258387084717 1953620059195596895156769)
        ·
          refine ⟨1465215044396697671367577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1953620059195596895156769 1465215044396697671367577)
          ·
            refine ⟨1098911283297523253525683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1465215044396697671367577 1098911283297523253525683)
            ·
              refine ⟨1648366924946284880288525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1098911283297523253525683 1648366924946284880288525)
              ·
                refine ⟨618137596854856830108197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1648366924946284880288525 618137596854856830108197)
                ·
                  refine ⟨115900799410285655645287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 618137596854856830108197 115900799410285655645287)
                  ·
                    rfl

theorem cell21_507861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 1, 3, 4].length) (baseStart_507861 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_507861 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_507861 prefixEnd_507861 := by exact prefixLift 507861
  have htrace : WordTrace (prefixWord ++ tailWord_507861) baseStart_507861 baseEnd_507861 := by
    simpa [prefixWord, tailWord_507861, baseEnd_507861] using wordTrace_append hprefix tailTrace_507861
  have hstable : (prefixWord ++ tailWord_507861).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_507861).length < 2 ^ (prefixWord ++ tailWord_507861).sum := by decide
  have hdescent : baseEnd_507861 < baseStart_507861 := by decide
  rcases family_descends (prefixWord ++ tailWord_507861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_507892 : List Nat := [2, 6, 2, 11]
def baseStart_507892 : Nat := 118140960795 + 507892 * 2 ^ 59
def prefixEnd_507892 : Nat := 4983230072969 + 3 ^ 40 * 507892 * 2
def baseEnd_507892 : Nat := 476987135936775681599

theorem tailTrace_507892 : CollatzResearch.WordTrace tailWord_507892 prefixEnd_507892 476987135936775681599 := by
  unfold tailWord_507892
  simp only [CollatzResearch.WordTrace]
  refine ⟨9262171538000749946450965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12349562050667666595267953 9262171538000749946450965)
  ·
    refine ⟨434164290843785153739889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 9262171538000749946450965 434164290843785153739889)
    ·
      refine ⟨325623218132838865304917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 434164290843785153739889 325623218132838865304917)
      ·
        refine ⟨476987135936775681599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 11 325623218132838865304917 476987135936775681599)
        ·
          rfl

theorem cell21_507892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 11].length) (baseStart_507892 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_507892 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_507892 prefixEnd_507892 := by exact prefixLift 507892
  have htrace : WordTrace (prefixWord ++ tailWord_507892) baseStart_507892 baseEnd_507892 := by
    simpa [prefixWord, tailWord_507892, baseEnd_507892] using wordTrace_append hprefix tailTrace_507892
  have hstable : (prefixWord ++ tailWord_507892).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_507892).length < 2 ^ (prefixWord ++ tailWord_507892).sum := by decide
  have hdescent : baseEnd_507892 < baseStart_507892 := by decide
  rcases family_descends (prefixWord ++ tailWord_507892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_507903 : List Nat := [1, 1, 2, 2, 1, 2, 1, 5, 6]
def baseStart_507903 : Nat := 118140960795 + 507903 * 2 ^ 59
def prefixEnd_507903 : Nat := 4983230072969 + 3 ^ 40 * 507903 * 2
def baseEnd_507903 : Nat := 115910384382502915945201

theorem tailTrace_507903 : CollatzResearch.WordTrace tailWord_507903 prefixEnd_507903 115910384382502915945201 := by
  unfold tailWord_507903
  simp only [CollatzResearch.WordTrace]
  refine ⟨18524744278961648771552363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12349829519307765847701575 18524744278961648771552363)
  ·
    refine ⟨27787116418442473157328545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18524744278961648771552363 27787116418442473157328545)
    ·
      refine ⟨20840337313831854867996409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27787116418442473157328545 20840337313831854867996409)
      ·
        refine ⟨15630252985373891150997307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20840337313831854867996409 15630252985373891150997307)
        ·
          refine ⟨23445379478060836726495961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15630252985373891150997307 23445379478060836726495961)
          ·
            refine ⟨17584034608545627544871971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23445379478060836726495961 17584034608545627544871971)
            ·
              refine ⟨26376051912818441317307957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17584034608545627544871971 26376051912818441317307957)
              ·
                refine ⟨2472754866826728873497621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26376051912818441317307957 2472754866826728873497621)
                ·
                  refine ⟨115910384382502915945201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2472754866826728873497621 115910384382502915945201)
                  ·
                    rfl

theorem cell21_507903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 5, 6].length) (baseStart_507903 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_507903 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_507903 prefixEnd_507903 := by exact prefixLift 507903
  have htrace : WordTrace (prefixWord ++ tailWord_507903) baseStart_507903 baseEnd_507903 := by
    simpa [prefixWord, tailWord_507903, baseEnd_507903] using wordTrace_append hprefix tailTrace_507903
  have hstable : (prefixWord ++ tailWord_507903).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_507903).length < 2 ^ (prefixWord ++ tailWord_507903).sum := by decide
  have hdescent : baseEnd_507903 < baseStart_507903 := by decide
  rcases family_descends (prefixWord ++ tailWord_507903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_507940 : List Nat := [2, 3, 1, 4, 2, 1, 2, 3, 3]
def baseStart_507940 : Nat := 118140960795 + 507940 * 2 ^ 59
def prefixEnd_507940 : Nat := 4983230072969 + 3 ^ 40 * 507940 * 2
def baseEnd_507940 : Nat := 115918828286599073828459

theorem tailTrace_507940 : CollatzResearch.WordTrace tailWord_507940 prefixEnd_507940 115918828286599073828459 := by
  unfold tailWord_507940
  simp only [CollatzResearch.WordTrace]
  refine ⟨9263046889913802045324637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12350729186551736060432849 9263046889913802045324637)
  ·
    refine ⟨3473642583717675766996739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9263046889913802045324637 3473642583717675766996739)
    ·
      refine ⟨5210463875576513650495109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3473642583717675766996739 5210463875576513650495109)
      ·
        refine ⟨976961976670596309467833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5210463875576513650495109 976961976670596309467833)
        ·
          refine ⟨732721482502947232100875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 976961976670596309467833 732721482502947232100875)
          ·
            refine ⟨1099082223754420848151313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 732721482502947232100875 1099082223754420848151313)
            ·
              refine ⟨824311667815815636113485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1099082223754420848151313 824311667815815636113485)
              ·
                refine ⟨309116875430930863542557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 824311667815815636113485 309116875430930863542557)
                ·
                  refine ⟨115918828286599073828459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 309116875430930863542557 115918828286599073828459)
                  ·
                    rfl

theorem cell21_507940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 2, 3, 3].length) (baseStart_507940 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_507940 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_507940 prefixEnd_507940 := by exact prefixLift 507940
  have htrace : WordTrace (prefixWord ++ tailWord_507940) baseStart_507940 baseEnd_507940 := by
    simpa [prefixWord, tailWord_507940, baseEnd_507940] using wordTrace_append hprefix tailTrace_507940
  have hstable : (prefixWord ++ tailWord_507940).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_507940).length < 2 ^ (prefixWord ++ tailWord_507940).sum := by decide
  have hdescent : baseEnd_507940 < baseStart_507940 := by decide
  rcases family_descends (prefixWord ++ tailWord_507940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_507996 : List Nat := [2, 2, 4, 1, 1, 2, 1, 2, 6]
def baseStart_507996 : Nat := 118140960795 + 507996 * 2 ^ 59
def prefixEnd_507996 : Nat := 4983230072969 + 3 ^ 40 * 507996 * 2
def baseEnd_507996 : Nat := 115931608249555420895011

theorem tailTrace_507996 : CollatzResearch.WordTrace tailWord_507996 prefixEnd_507996 115931608249555420895011 := by
  unfold tailWord_507996
  simp only [CollatzResearch.WordTrace]
  refine ⟨9264068133812362827343921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12352090845083150436458561 9264068133812362827343921)
  ·
    refine ⟨6948051100359272120507941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9264068133812362827343921 6948051100359272120507941)
    ·
      refine ⟨1302759581317363522595239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6948051100359272120507941 1302759581317363522595239)
      ·
        refine ⟨1954139371976045283892859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1302759581317363522595239 1954139371976045283892859)
        ·
          refine ⟨2931209057964067925839289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1954139371976045283892859 2931209057964067925839289)
          ·
            refine ⟨2198406793473050944379467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2931209057964067925839289 2198406793473050944379467)
            ·
              refine ⟨3297610190209576416569201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2198406793473050944379467 3297610190209576416569201)
              ·
                refine ⟨2473207642657182312426901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3297610190209576416569201 2473207642657182312426901)
                ·
                  refine ⟨115931608249555420895011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2473207642657182312426901 115931608249555420895011)
                  ·
                    rfl

theorem cell21_507996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 1, 2, 6].length) (baseStart_507996 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_507996 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_507996 prefixEnd_507996 := by exact prefixLift 507996
  have htrace : WordTrace (prefixWord ++ tailWord_507996) baseStart_507996 baseEnd_507996 := by
    simpa [prefixWord, tailWord_507996, baseEnd_507996] using wordTrace_append hprefix tailTrace_507996
  have hstable : (prefixWord ++ tailWord_507996).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_507996).length < 2 ^ (prefixWord ++ tailWord_507996).sum := by decide
  have hdescent : baseEnd_507996 < baseStart_507996 := by decide
  rcases family_descends (prefixWord ++ tailWord_507996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_508078 : List Nat := [4, 1, 4, 2, 2, 1, 1, 6]
def baseStart_508078 : Nat := 118140960795 + 508078 * 2 ^ 59
def prefixEnd_508078 : Nat := 4983230072969 + 3 ^ 40 * 508078 * 2
def baseEnd_508078 : Nat := 38650107255580500176059

theorem tailTrace_508078 : CollatzResearch.WordTrace tailWord_508078 prefixEnd_508078 38650107255580500176059 := by
  unfold tailWord_508078
  simp only [CollatzResearch.WordTrace]
  refine ⟨2316390881665956707396611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12354084702218435772781925 2316390881665956707396611)
  ·
    refine ⟨3474586322498935061094917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2316390881665956707396611 3474586322498935061094917)
    ·
      refine ⟨651484935468550323955297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3474586322498935061094917 651484935468550323955297)
      ·
        refine ⟨488613701601412742966473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 651484935468550323955297 488613701601412742966473)
        ·
          refine ⟨366460276201059557224855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 488613701601412742966473 366460276201059557224855)
          ·
            refine ⟨549690414301589335837283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 366460276201059557224855 549690414301589335837283)
            ·
              refine ⟨824535621452384003755925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 549690414301589335837283 824535621452384003755925)
              ·
                refine ⟨38650107255580500176059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 824535621452384003755925 38650107255580500176059)
                ·
                  rfl

theorem cell21_508078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 2, 1, 1, 6].length) (baseStart_508078 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_508078 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_508078 prefixEnd_508078 := by exact prefixLift 508078
  have htrace : WordTrace (prefixWord ++ tailWord_508078) baseStart_508078 baseEnd_508078 := by
    simpa [prefixWord, tailWord_508078, baseEnd_508078] using wordTrace_append hprefix tailTrace_508078
  have hstable : (prefixWord ++ tailWord_508078).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_508078).length < 2 ^ (prefixWord ++ tailWord_508078).sum := by decide
  have hdescent : baseEnd_508078 < baseStart_508078 := by decide
  rcases family_descends (prefixWord ++ tailWord_508078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_508193 : List Nat := [1, 2, 3, 2, 1, 1, 5, 1, 5]
def baseStart_508193 : Nat := 118140960795 + 508193 * 2 ^ 59
def prefixEnd_508193 : Nat := 4983230072969 + 3 ^ 40 * 508193 * 2
def baseEnd_508193 : Nat := 115976566333526856111275

theorem tailTrace_508193 : CollatzResearch.WordTrace tailWord_508193 prefixEnd_508193 115976566333526856111275 := by
  unfold tailWord_508193
  simp only [CollatzResearch.WordTrace]
  refine ⟨18535321447911028299609233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12356880965274018866406155 18535321447911028299609233)
  ·
    refine ⟨13901491085933271224706925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18535321447911028299609233 13901491085933271224706925)
    ·
      refine ⟨5213059157224976709265097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13901491085933271224706925 5213059157224976709265097)
      ·
        refine ⟨3909794367918732531948823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5213059157224976709265097 3909794367918732531948823)
        ·
          refine ⟨5864691551878098797923235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3909794367918732531948823 5864691551878098797923235)
          ·
            refine ⟨8797037327817148196884853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5864691551878098797923235 8797037327817148196884853)
            ·
              refine ⟨824722249482857643457955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8797037327817148196884853 824722249482857643457955)
              ·
                refine ⟨1237083374224286465186933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 824722249482857643457955 1237083374224286465186933)
                ·
                  refine ⟨115976566333526856111275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1237083374224286465186933 115976566333526856111275)
                  ·
                    rfl

theorem cell21_508193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 5, 1, 5].length) (baseStart_508193 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_508193 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_508193 prefixEnd_508193 := by exact prefixLift 508193
  have htrace : WordTrace (prefixWord ++ tailWord_508193) baseStart_508193 baseEnd_508193 := by
    simpa [prefixWord, tailWord_508193, baseEnd_508193] using wordTrace_append hprefix tailTrace_508193
  have hstable : (prefixWord ++ tailWord_508193).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_508193).length < 2 ^ (prefixWord ++ tailWord_508193).sum := by decide
  have hdescent : baseEnd_508193 < baseStart_508193 := by decide
  rcases family_descends (prefixWord ++ tailWord_508193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_508199 : List Nat := [1, 1, 8, 1, 1, 1, 1, 3, 4]
def baseStart_508199 : Nat := 118140960795 + 508199 * 2 ^ 59
def prefixEnd_508199 : Nat := 4983230072969 + 3 ^ 40 * 508199 * 2
def baseEnd_508199 : Nat := 115977935615272179011263

theorem tailTrace_508199 : CollatzResearch.WordTrace tailWord_508199 prefixEnd_508199 115977935615272179011263 := by
  unfold tailWord_508199
  simp only [CollatzResearch.WordTrace]
  refine ⟨18535540285889291324327651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12357026857259527549551767 18535540285889291324327651)
  ·
    refine ⟨27803310428833936986491477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18535540285889291324327651 27803310428833936986491477)
    ·
      refine ⟨325820044087897699060447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 27803310428833936986491477 325820044087897699060447)
      ·
        refine ⟨488730066131846548590671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 325820044087897699060447 488730066131846548590671)
        ·
          refine ⟨733095099197769822886007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 488730066131846548590671 733095099197769822886007)
          ·
            refine ⟨1099642648796654734329011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 733095099197769822886007 1099642648796654734329011)
            ·
              refine ⟨1649463973194982101493517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1099642648796654734329011 1649463973194982101493517)
              ·
                refine ⟨618548989948118288060069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1649463973194982101493517 618548989948118288060069)
                ·
                  refine ⟨115977935615272179011263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 618548989948118288060069 115977935615272179011263)
                  ·
                    rfl

theorem cell21_508199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 1, 3, 4].length) (baseStart_508199 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_508199 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_508199 prefixEnd_508199 := by exact prefixLift 508199
  have htrace : WordTrace (prefixWord ++ tailWord_508199) baseStart_508199 baseEnd_508199 := by
    simpa [prefixWord, tailWord_508199, baseEnd_508199] using wordTrace_append hprefix tailTrace_508199
  have hstable : (prefixWord ++ tailWord_508199).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_508199).length < 2 ^ (prefixWord ++ tailWord_508199).sum := by decide
  have hdescent : baseEnd_508199 < baseStart_508199 := by decide
  rcases family_descends (prefixWord ++ tailWord_508199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_508244 : List Nat := [2, 4, 1, 1, 2, 4, 2, 2, 3]
def baseStart_508244 : Nat := 118140960795 + 508244 * 2 ^ 59
def prefixEnd_508244 : Nat := 4983230072969 + 3 ^ 40 * 508244 * 2
def baseEnd_508244 : Nat := 115988205228362100761171

theorem tailTrace_508244 : CollatzResearch.WordTrace tailWord_508244 prefixEnd_508244 115988205228362100761171 := by
  unfold tailWord_508244
  simp only [CollatzResearch.WordTrace]
  refine ⟨9268590785363132004857893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12358121047150842673143857 9268590785363132004857893)
  ·
    refine ⟨1737860772255587250910855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9268590785363132004857893 1737860772255587250910855)
    ·
      refine ⟨2606791158383380876366283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1737860772255587250910855 2606791158383380876366283)
      ·
        refine ⟨3910186737575071314549425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2606791158383380876366283 3910186737575071314549425)
        ·
          refine ⟨2932640053181303485912069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3910186737575071314549425 2932640053181303485912069)
          ·
            refine ⟨549870009971494403608513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2932640053181303485912069 549870009971494403608513)
            ·
              refine ⟨412402507478620802706385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 549870009971494403608513 412402507478620802706385)
              ·
                refine ⟨309301880608965602029789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 412402507478620802706385 309301880608965602029789)
                ·
                  refine ⟨115988205228362100761171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 309301880608965602029789 115988205228362100761171)
                  ·
                    rfl

theorem cell21_508244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 4, 2, 2, 3].length) (baseStart_508244 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_508244 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_508244 prefixEnd_508244 := by exact prefixLift 508244
  have htrace : WordTrace (prefixWord ++ tailWord_508244) baseStart_508244 baseEnd_508244 := by
    simpa [prefixWord, tailWord_508244, baseEnd_508244] using wordTrace_append hprefix tailTrace_508244
  have hstable : (prefixWord ++ tailWord_508244).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_508244).length < 2 ^ (prefixWord ++ tailWord_508244).sum := by decide
  have hdescent : baseEnd_508244 < baseStart_508244 := by decide
  rcases family_descends (prefixWord ++ tailWord_508244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_508269 : List Nat := [1, 5, 1, 1, 1, 2, 3, 2, 5]
def baseStart_508269 : Nat := 118140960795 + 508269 * 2 ^ 59
def prefixEnd_508269 : Nat := 4983230072969 + 3 ^ 40 * 508269 * 2
def baseEnd_508269 : Nat := 115993910568967612844453

theorem tailTrace_508269 : CollatzResearch.WordTrace tailWord_508269 prefixEnd_508269 115993910568967612844453 := by
  unfold tailWord_508269
  simp only [CollatzResearch.WordTrace]
  refine ⟨18538093395635693279375861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12358728930423795519583907 18538093395635693279375861)
  ·
    refine ⟨1737946255840846244941487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 18538093395635693279375861 1737946255840846244941487)
    ·
      refine ⟨2606919383761269367412231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1737946255840846244941487 2606919383761269367412231)
      ·
        refine ⟨3910379075641904051118347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2606919383761269367412231 3910379075641904051118347)
        ·
          refine ⟨5865568613462856076677521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3910379075641904051118347 5865568613462856076677521)
          ·
            refine ⟨4399176460097142057508141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5865568613462856076677521 4399176460097142057508141)
            ·
              refine ⟨1649691172536428271565553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4399176460097142057508141 1649691172536428271565553)
              ·
                refine ⟨1237268379402321203674165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1649691172536428271565553 1237268379402321203674165)
                ·
                  refine ⟨115993910568967612844453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1237268379402321203674165 115993910568967612844453)
                  ·
                    rfl

theorem cell21_508269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 3, 2, 5].length) (baseStart_508269 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_508269 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_508269 prefixEnd_508269 := by exact prefixLift 508269
  have htrace : WordTrace (prefixWord ++ tailWord_508269) baseStart_508269 baseEnd_508269 := by
    simpa [prefixWord, tailWord_508269, baseEnd_508269] using wordTrace_append hprefix tailTrace_508269
  have hstable : (prefixWord ++ tailWord_508269).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_508269).length < 2 ^ (prefixWord ++ tailWord_508269).sum := by decide
  have hdescent : baseEnd_508269 < baseStart_508269 := by decide
  rcases family_descends (prefixWord ++ tailWord_508269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_508300 : List Nat := [2, 2, 1, 2, 1, 4, 3, 2, 4]
def baseStart_508300 : Nat := 118140960795 + 508300 * 2 ^ 59
def prefixEnd_508300 : Nat := 4983230072969 + 3 ^ 40 * 508300 * 2
def baseEnd_508300 : Nat := 116000985191318447827723

theorem tailTrace_508300 : CollatzResearch.WordTrace tailWord_508300 prefixEnd_508300 116000985191318447827723 := by
  unfold tailWord_508300
  simp only [CollatzResearch.WordTrace]
  refine ⟨9269612029261692786877177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12359482705682257049169569 9269612029261692786877177)
  ·
    refine ⟨6952209021946269590157883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9269612029261692786877177 6952209021946269590157883)
    ·
      refine ⟨10428313532919404385236825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6952209021946269590157883 10428313532919404385236825)
      ·
        refine ⟨7821235149689553288927619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10428313532919404385236825 7821235149689553288927619)
        ·
          refine ⟨11731852724534329933391429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7821235149689553288927619 11731852724534329933391429)
          ·
            refine ⟨2199722385850186862510893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11731852724534329933391429 2199722385850186862510893)
            ·
              refine ⟨824895894693820073441585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2199722385850186862510893 824895894693820073441585)
              ·
                refine ⟨618671921020365055081189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 824895894693820073441585 618671921020365055081189)
                ·
                  refine ⟨116000985191318447827723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 618671921020365055081189 116000985191318447827723)
                  ·
                    rfl

theorem cell21_508300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 3, 2, 4].length) (baseStart_508300 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_508300 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_508300 prefixEnd_508300 := by exact prefixLift 508300
  have htrace : WordTrace (prefixWord ++ tailWord_508300) baseStart_508300 baseEnd_508300 := by
    simpa [prefixWord, tailWord_508300, baseEnd_508300] using wordTrace_append hprefix tailTrace_508300
  have hstable : (prefixWord ++ tailWord_508300).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_508300).length < 2 ^ (prefixWord ++ tailWord_508300).sum := by decide
  have hdescent : baseEnd_508300 < baseStart_508300 := by decide
  rcases family_descends (prefixWord ++ tailWord_508300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_508359 : List Nat := [1, 1, 4, 1, 1, 4, 2, 1, 6]
def baseStart_508359 : Nat := 118140960795 + 508359 * 2 ^ 59
def prefixEnd_508359 : Nat := 4983230072969 + 3 ^ 40 * 508359 * 2
def baseEnd_508359 : Nat := 116014449795147456344269

theorem tailTrace_508359 : CollatzResearch.WordTrace tailWord_508359 prefixEnd_508359 116014449795147456344269 := by
  unfold tailWord_508359
  simp only [CollatzResearch.WordTrace]
  refine ⟨18541375965309638650152131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12360917310206425766768087 18541375965309638650152131)
  ·
    refine ⟨27812063947964457975228197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18541375965309638650152131 27812063947964457975228197)
    ·
      refine ⟨5214761990243335870355287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27812063947964457975228197 5214761990243335870355287)
      ·
        refine ⟨7822142985365003805532931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5214761990243335870355287 7822142985365003805532931)
        ·
          refine ⟨11733214478047505708299397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7822142985365003805532931 11733214478047505708299397)
          ·
            refine ⟨2199977714633907320306137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11733214478047505708299397 2199977714633907320306137)
            ·
              refine ⟨1649983285975430490229603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2199977714633907320306137 1649983285975430490229603)
              ·
                refine ⟨2474974928963145735344405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1649983285975430490229603 2474974928963145735344405)
                ·
                  refine ⟨116014449795147456344269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2474974928963145735344405 116014449795147456344269)
                  ·
                    rfl

theorem cell21_508359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 2, 1, 6].length) (baseStart_508359 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_508359 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_508359 prefixEnd_508359 := by exact prefixLift 508359
  have htrace : WordTrace (prefixWord ++ tailWord_508359) baseStart_508359 baseEnd_508359 := by
    simpa [prefixWord, tailWord_508359, baseEnd_508359] using wordTrace_append hprefix tailTrace_508359
  have hstable : (prefixWord ++ tailWord_508359).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_508359).length < 2 ^ (prefixWord ++ tailWord_508359).sum := by decide
  have hdescent : baseEnd_508359 < baseStart_508359 := by decide
  rcases family_descends (prefixWord ++ tailWord_508359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_508435 : List Nat := [1, 1, 1, 2, 1, 5, 1, 5, 4]
def baseStart_508435 : Nat := 118140960795 + 508435 * 2 ^ 59
def prefixEnd_508435 : Nat := 4983230072969 + 3 ^ 40 * 508435 * 2
def baseEnd_508435 : Nat := 116031794030588213077447

theorem tailTrace_508435 : CollatzResearch.WordTrace tailWord_508435 prefixEnd_508435 116031794030588213077447 := by
  unfold tailWord_508435
  simp only [CollatzResearch.WordTrace]
  refine ⟨18544147913034303629918759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12362765275356202419945839 18544147913034303629918759)
  ·
    refine ⟨27816221869551455444878139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18544147913034303629918759 27816221869551455444878139)
    ·
      refine ⟨41724332804327183167317209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27816221869551455444878139 41724332804327183167317209)
      ·
        refine ⟨31293249603245387375487907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41724332804327183167317209 31293249603245387375487907)
        ·
          refine ⟨46939874404868081063231861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31293249603245387375487907 46939874404868081063231861)
          ·
            refine ⟨4400613225456382599677987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 46939874404868081063231861 4400613225456382599677987)
            ·
              refine ⟨6600919838184573899516981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4400613225456382599677987 6600919838184573899516981)
              ·
                refine ⟨618836234829803803079717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6600919838184573899516981 618836234829803803079717)
                ·
                  refine ⟨116031794030588213077447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 618836234829803803079717 116031794030588213077447)
                  ·
                    rfl

theorem cell21_508435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 5, 4].length) (baseStart_508435 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_508435 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_508435 prefixEnd_508435 := by exact prefixLift 508435
  have htrace : WordTrace (prefixWord ++ tailWord_508435) baseStart_508435 baseEnd_508435 := by
    simpa [prefixWord, tailWord_508435, baseEnd_508435] using wordTrace_append hprefix tailTrace_508435
  have hstable : (prefixWord ++ tailWord_508435).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_508435).length < 2 ^ (prefixWord ++ tailWord_508435).sum := by decide
  have hdescent : baseEnd_508435 < baseStart_508435 := by decide
  rcases family_descends (prefixWord ++ tailWord_508435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_508480 : List Nat := [2, 1, 1, 2, 2, 2, 3, 3, 5]
def baseStart_508480 : Nat := 118140960795 + 508480 * 2 ^ 59
def prefixEnd_508480 : Nat := 4983230072969 + 3 ^ 40 * 508480 * 2
def baseEnd_508480 : Nat := 116042063643678134827355

theorem tailTrace_508480 : CollatzResearch.WordTrace tailWord_508480 prefixEnd_508480 116042063643678134827355 := by
  unfold tailWord_508480
  simp only [CollatzResearch.WordTrace]
  refine ⟨9272894598935638157653447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12363859465247517543537929 9272894598935638157653447)
  ·
    refine ⟨13909341898403457236480171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9272894598935638157653447 13909341898403457236480171)
    ·
      refine ⟨20864012847605185854720257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13909341898403457236480171 20864012847605185854720257)
      ·
        refine ⟨15648009635703889391040193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20864012847605185854720257 15648009635703889391040193)
        ·
          refine ⟨11736007226777917043280145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15648009635703889391040193 11736007226777917043280145)
          ·
            refine ⟨8802005420083437782460109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11736007226777917043280145 8802005420083437782460109)
            ·
              refine ⟨3300752032531289168422541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8802005420083437782460109 3300752032531289168422541)
              ·
                refine ⟨1237782012199233438158453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3300752032531289168422541 1237782012199233438158453)
                ·
                  refine ⟨116042063643678134827355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1237782012199233438158453 116042063643678134827355)
                  ·
                    rfl

theorem cell21_508480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 3, 3, 5].length) (baseStart_508480 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_508480 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_508480 prefixEnd_508480 := by exact prefixLift 508480
  have htrace : WordTrace (prefixWord ++ tailWord_508480) baseStart_508480 baseEnd_508480 := by
    simpa [prefixWord, tailWord_508480, baseEnd_508480] using wordTrace_append hprefix tailTrace_508480
  have hstable : (prefixWord ++ tailWord_508480).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_508480).length < 2 ^ (prefixWord ++ tailWord_508480).sum := by decide
  have hdescent : baseEnd_508480 < baseStart_508480 := by decide
  rcases family_descends (prefixWord ++ tailWord_508480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_508649 : List Nat := [1, 2, 1, 1, 1, 2, 6, 4, 3]
def baseStart_508649 : Nat := 118140960795 + 508649 * 2 ^ 59
def prefixEnd_508649 : Nat := 4983230072969 + 3 ^ 40 * 508649 * 2
def baseEnd_508649 : Nat := 116080631746171396510343

theorem tailTrace_508649 : CollatzResearch.WordTrace tailWord_508649 prefixEnd_508649 116080631746171396510343 := by
  unfold tailWord_508649
  simp only [CollatzResearch.WordTrace]
  refine ⟨18551953134259018178209001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12367968756172678785472667 18551953134259018178209001)
  ·
    refine ⟨13913964850694263633656751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18551953134259018178209001 13913964850694263633656751)
    ·
      refine ⟨20870947276041395450485127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13913964850694263633656751 20870947276041395450485127)
      ·
        refine ⟨31306420914062093175727691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20870947276041395450485127 31306420914062093175727691)
        ·
          refine ⟨46959631371093139763591537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31306420914062093175727691 46959631371093139763591537)
          ·
            refine ⟨35219723528319854822693653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46959631371093139763591537 35219723528319854822693653)
            ·
              refine ⟨1650924540389993194813765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 35219723528319854822693653 1650924540389993194813765)
              ·
                refine ⟨309548351323123724027581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1650924540389993194813765 309548351323123724027581)
                ·
                  refine ⟨116080631746171396510343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 309548351323123724027581 116080631746171396510343)
                  ·
                    rfl

theorem cell21_508649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 6, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 6, 4, 3].length) (baseStart_508649 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_508649 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_508649 prefixEnd_508649 := by exact prefixLift 508649
  have htrace : WordTrace (prefixWord ++ tailWord_508649) baseStart_508649 baseEnd_508649 := by
    simpa [prefixWord, tailWord_508649, baseEnd_508649] using wordTrace_append hprefix tailTrace_508649
  have hstable : (prefixWord ++ tailWord_508649).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_508649).length < 2 ^ (prefixWord ++ tailWord_508649).sum := by decide
  have hdescent : baseEnd_508649 < baseStart_508649 := by decide
  rcases family_descends (prefixWord ++ tailWord_508649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_508753 : List Nat := [1, 2, 2, 1, 6, 9]
def baseStart_508753 : Nat := 118140960795 + 508753 * 2 ^ 59
def prefixEnd_508753 : Nat := 4983230072969 + 3 ^ 40 * 508753 * 2
def baseEnd_508753 : Nat := 4300161702336678769511

theorem tailTrace_508753 : CollatzResearch.WordTrace tailWord_508753 prefixEnd_508753 4300161702336678769511 := by
  unfold tailWord_508753
  simp only [CollatzResearch.WordTrace]
  refine ⟨18555746325882243939994913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12370497550588162626663275 18555746325882243939994913)
  ·
    refine ⟨13916809744411682954996185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18555746325882243939994913 13916809744411682954996185)
    ·
      refine ⟨10437607308308762216247139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13916809744411682954996185 10437607308308762216247139)
      ·
        refine ⟨15656410962463143324370709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10437607308308762216247139 15656410962463143324370709)
        ·
          refine ⟨733894263865459843329877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 15656410962463143324370709 733894263865459843329877)
          ·
            refine ⟨4300161702336678769511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 733894263865459843329877 4300161702336678769511)
            ·
              rfl

theorem cell21_508753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 9].length) (baseStart_508753 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_508753 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_508753 prefixEnd_508753 := by exact prefixLift 508753
  have htrace : WordTrace (prefixWord ++ tailWord_508753) baseStart_508753 baseEnd_508753 := by
    simpa [prefixWord, tailWord_508753, baseEnd_508753] using wordTrace_append hprefix tailTrace_508753
  have hstable : (prefixWord ++ tailWord_508753).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_508753).length < 2 ^ (prefixWord ++ tailWord_508753).sum := by decide
  have hdescent : baseEnd_508753 < baseStart_508753 := by decide
  rcases family_descends (prefixWord ++ tailWord_508753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_508759 : List Nat := [1, 1, 3, 2, 4, 3, 2, 2, 3]
def baseStart_508759 : Nat := 118140960795 + 508759 * 2 ^ 59
def prefixEnd_508759 : Nat := 4983230072969 + 3 ^ 40 * 508759 * 2
def baseEnd_508759 : Nat := 116105735244835649676785

theorem tailTrace_508759 : CollatzResearch.WordTrace tailWord_508759 prefixEnd_508759 116105735244835649676785 := by
  unfold tailWord_508759
  simp only [CollatzResearch.WordTrace]
  refine ⟨18555965163860506964713331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12370643442573671309808887 18555965163860506964713331)
  ·
    refine ⟨27833947745790760447069997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18555965163860506964713331 27833947745790760447069997)
    ·
      refine ⟨10437730404671535167651249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27833947745790760447069997 10437730404671535167651249)
      ·
        refine ⟨7828297803503651375738437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10437730404671535167651249 7828297803503651375738437)
        ·
          refine ⟨1467805838156934632950957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7828297803503651375738437 1467805838156934632950957)
          ·
            refine ⟨550427189308850487356609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1467805838156934632950957 550427189308850487356609)
            ·
              refine ⟨412820391981637865517457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 550427189308850487356609 412820391981637865517457)
              ·
                refine ⟨309615293986228399138093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 412820391981637865517457 309615293986228399138093)
                ·
                  refine ⟨116105735244835649676785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 309615293986228399138093 116105735244835649676785)
                  ·
                    rfl

theorem cell21_508759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 3, 2, 2, 3].length) (baseStart_508759 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_508759 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_508759 prefixEnd_508759 := by exact prefixLift 508759
  have htrace : WordTrace (prefixWord ++ tailWord_508759) baseStart_508759 baseEnd_508759 := by
    simpa [prefixWord, tailWord_508759, baseEnd_508759] using wordTrace_append hprefix tailTrace_508759
  have hstable : (prefixWord ++ tailWord_508759).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_508759).length < 2 ^ (prefixWord ++ tailWord_508759).sum := by decide
  have hdescent : baseEnd_508759 < baseStart_508759 := by decide
  rcases family_descends (prefixWord ++ tailWord_508759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan21Incremental
