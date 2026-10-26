import V185TrunkScan23Chunk1221

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_7241354 : List Nat := [3, 1, 2, 3, 2, 1, 1, 1, 2, 3, 4]
def baseStart_7241354 : Nat := 118140960795 + 7241354 * 2 ^ 59
def prefixEnd_7241354 : Nat := 4983230072969 + 3 ^ 40 * 7241354 * 2
def baseEnd_7241354 : Nat := 3718295191357966402872625

theorem tailTrace_7241354 : CollatzResearch.WordTrace tailWord_7241354 prefixEnd_7241354 3718295191357966402872625 := by
  unfold tailWord_7241354
  simp only [CollatzResearch.WordTrace]
  refine ⟨66028469551954664411904779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176075918805212438431746077 66028469551954664411904779)
  ·
    refine ⟨99042704327931996617857169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66028469551954664411904779 99042704327931996617857169)
    ·
      refine ⟨74282028245948997463392877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99042704327931996617857169 74282028245948997463392877)
      ·
        refine ⟨27855760592230874048772329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74282028245948997463392877 27855760592230874048772329)
        ·
          refine ⟨20891820444173155536579247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27855760592230874048772329 20891820444173155536579247)
          ·
            refine ⟨31337730666259733304868871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20891820444173155536579247 31337730666259733304868871)
            ·
              refine ⟨47006595999389599957303307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31337730666259733304868871 47006595999389599957303307)
              ·
                refine ⟨70509893999084399935954961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47006595999389599957303307 70509893999084399935954961)
                ·
                  refine ⟨52882420499313299951966221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 70509893999084399935954961 52882420499313299951966221)
                  ·
                    refine ⟨19830907687242487481987333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 52882420499313299951966221 19830907687242487481987333)
                    ·
                      refine ⟨3718295191357966402872625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19830907687242487481987333 3718295191357966402872625)
                      ·
                        rfl

theorem cell23_7241354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 1, 1, 2, 3, 4].length) (baseStart_7241354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7241354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7241354 prefixEnd_7241354 := by exact prefixLift 7241354
  have htrace : WordTrace (prefixWord ++ tailWord_7241354) baseStart_7241354 baseEnd_7241354 := by
    simpa [prefixWord, tailWord_7241354, baseEnd_7241354] using wordTrace_append hprefix tailTrace_7241354
  have hstable : (prefixWord ++ tailWord_7241354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7241354).length < 2 ^ (prefixWord ++ tailWord_7241354).sum := by decide
  have hdescent : baseEnd_7241354 < baseStart_7241354 := by decide
  rcases family_descends (prefixWord ++ tailWord_7241354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7241444 : List Nat := [2, 3, 1, 1, 1, 3, 1, 3, 1, 3, 4]
def baseStart_7241444 : Nat := 118140960795 + 7241444 * 2 ^ 59
def prefixEnd_7241444 : Nat := 4983230072969 + 3 ^ 40 * 7241444 * 2
def baseEnd_7241444 : Nat := 3718341404616871050747211

theorem tailTrace_7241444 : CollatzResearch.WordTrace tailWord_7241444 prefixEnd_7241444 3718341404616871050747211 := by
  unfold tailWord_7241444
  simp only [CollatzResearch.WordTrace]
  refine ⟨132058580388746301509197693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176078107184995068678930257 132058580388746301509197693)
  ·
    refine ⟨49521967645779863065949135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132058580388746301509197693 49521967645779863065949135)
    ·
      refine ⟨74282951468669794598923703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49521967645779863065949135 74282951468669794598923703)
      ·
        refine ⟨111424427203004691898385555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74282951468669794598923703 111424427203004691898385555)
        ·
          refine ⟨167136640804507037847578333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111424427203004691898385555 167136640804507037847578333)
          ·
            refine ⟨62676240301690139192841875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 167136640804507037847578333 62676240301690139192841875)
            ·
              refine ⟨94014360452535208789262813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62676240301690139192841875 94014360452535208789262813)
              ·
                refine ⟨35255385169700703295973555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 94014360452535208789262813 35255385169700703295973555)
                ·
                  refine ⟨52883077754551054943960333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35255385169700703295973555 52883077754551054943960333)
                  ·
                    refine ⟨19831154157956645603985125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 52883077754551054943960333 19831154157956645603985125)
                    ·
                      refine ⟨3718341404616871050747211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19831154157956645603985125 3718341404616871050747211)
                      ·
                        rfl

theorem cell23_7241444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 3, 1, 3, 4].length) (baseStart_7241444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7241444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7241444 prefixEnd_7241444 := by exact prefixLift 7241444
  have htrace : WordTrace (prefixWord ++ tailWord_7241444) baseStart_7241444 baseEnd_7241444 := by
    simpa [prefixWord, tailWord_7241444, baseEnd_7241444] using wordTrace_append hprefix tailTrace_7241444
  have hstable : (prefixWord ++ tailWord_7241444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7241444).length < 2 ^ (prefixWord ++ tailWord_7241444).sum := by decide
  have hdescent : baseEnd_7241444 < baseStart_7241444 := by decide
  rcases family_descends (prefixWord ++ tailWord_7241444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7241464 : List Nat := [2, 1, 2, 1, 1, 2, 2, 2, 3, 4, 3]
def baseStart_7241464 : Nat := 118140960795 + 7241464 * 2 ^ 59
def prefixEnd_7241464 : Nat := 4983230072969 + 3 ^ 40 * 7241464 * 2
def baseEnd_7241464 : Nat := 3718351674229960972497119

theorem tailTrace_7241464 : CollatzResearch.WordTrace tailWord_7241464 prefixEnd_7241464 3718351674229960972497119 := by
  unfold tailWord_7241464
  simp only [CollatzResearch.WordTrace]
  refine ⟨132058945118710073217061723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176078593491613430956082297 132058945118710073217061723)
  ·
    refine ⟨198088417678065109825592585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132058945118710073217061723 198088417678065109825592585)
    ·
      refine ⟨148566313258548832369194439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 198088417678065109825592585 148566313258548832369194439)
      ·
        refine ⟨222849469887823248553791659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148566313258548832369194439 222849469887823248553791659)
        ·
          refine ⟨334274204831734872830687489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 222849469887823248553791659 334274204831734872830687489)
          ·
            refine ⟨250705653623801154623015617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 334274204831734872830687489 250705653623801154623015617)
            ·
              refine ⟨188029240217850865967261713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 250705653623801154623015617 188029240217850865967261713)
              ·
                refine ⟨141021930163388149475446285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 188029240217850865967261713 141021930163388149475446285)
                ·
                  refine ⟨52883223811270556053292357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 141021930163388149475446285 52883223811270556053292357)
                  ·
                    refine ⟨9915604464613229259992317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 52883223811270556053292357 9915604464613229259992317)
                    ·
                      refine ⟨3718351674229960972497119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9915604464613229259992317 3718351674229960972497119)
                      ·
                        rfl

theorem cell23_7241464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 2, 3, 4, 3].length) (baseStart_7241464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7241464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7241464 prefixEnd_7241464 := by exact prefixLift 7241464
  have htrace : WordTrace (prefixWord ++ tailWord_7241464) baseStart_7241464 baseEnd_7241464 := by
    simpa [prefixWord, tailWord_7241464, baseEnd_7241464] using wordTrace_append hprefix tailTrace_7241464
  have hstable : (prefixWord ++ tailWord_7241464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7241464).length < 2 ^ (prefixWord ++ tailWord_7241464).sum := by decide
  have hdescent : baseEnd_7241464 < baseStart_7241464 := by decide
  rcases family_descends (prefixWord ++ tailWord_7241464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7241471 : List Nat := [1, 1, 2, 2, 1, 3, 5, 1, 3, 4]
def baseStart_7241471 : Nat := 118140960795 + 7241471 * 2 ^ 59
def prefixEnd_7241471 : Nat := 4983230072969 + 3 ^ 40 * 7241471 * 2
def baseEnd_7241471 : Nat := 1239451756198180815036529

theorem tailTrace_7241471 : CollatzResearch.WordTrace tailWord_7241471 prefixEnd_7241471 1239451756198180815036529 := by
  unfold tailWord_7241471
  simp only [CollatzResearch.WordTrace]
  refine ⟨264118145548394786629628267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176078763698929857753085511 264118145548394786629628267)
  ·
    refine ⟨396177218322592179944442401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264118145548394786629628267 396177218322592179944442401)
    ·
      refine ⟨297132913741944134958331801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 396177218322592179944442401 297132913741944134958331801)
      ·
        refine ⟨222849685306458101218748851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 297132913741944134958331801 222849685306458101218748851)
        ·
          refine ⟨334274527959687151828123277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 222849685306458101218748851 334274527959687151828123277)
          ·
            refine ⟨125352947984882681935546229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 334274527959687151828123277 125352947984882681935546229)
            ·
              refine ⟨11751838873582751431457459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 125352947984882681935546229 11751838873582751431457459)
              ·
                refine ⟨17627758310374127147186189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11751838873582751431457459 17627758310374127147186189)
                ·
                  refine ⟨6610409366390297680194821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17627758310374127147186189 6610409366390297680194821)
                  ·
                    refine ⟨1239451756198180815036529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6610409366390297680194821 1239451756198180815036529)
                    ·
                      rfl

theorem cell23_7241471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 5, 1, 3, 4].length) (baseStart_7241471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7241471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7241471 prefixEnd_7241471 := by exact prefixLift 7241471
  have htrace : WordTrace (prefixWord ++ tailWord_7241471) baseStart_7241471 baseEnd_7241471 := by
    simpa [prefixWord, tailWord_7241471, baseEnd_7241471] using wordTrace_append hprefix tailTrace_7241471
  have hstable : (prefixWord ++ tailWord_7241471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7241471).length < 2 ^ (prefixWord ++ tailWord_7241471).sum := by decide
  have hdescent : baseEnd_7241471 < baseStart_7241471 := by decide
  rcases family_descends (prefixWord ++ tailWord_7241471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7241492 : List Nat := [2, 4, 4, 1, 1, 1, 2, 1, 2, 5]
def baseStart_7241492 : Nat := 118140960795 + 7241492 * 2 ^ 59
def prefixEnd_7241492 : Nat := 4983230072969 + 3 ^ 40 * 7241492 * 2
def baseEnd_7241492 : Nat := 1239455350562762287648997

theorem tailTrace_7241492 : CollatzResearch.WordTrace tailWord_7241492 prefixEnd_7241492 1239455350562762287648997 := by
  unfold tailWord_7241492
  simp only [CollatzResearch.WordTrace]
  refine ⟨132059455740659353608071365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176079274320879138144095153 132059455740659353608071365)
  ·
    refine ⟨24761147951373628801513381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 132059455740659353608071365 24761147951373628801513381)
    ·
      refine ⟨4642715240882555400283759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24761147951373628801513381 4642715240882555400283759)
      ·
        refine ⟨6964072861323833100425639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4642715240882555400283759 6964072861323833100425639)
        ·
          refine ⟨10446109291985749650638459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6964072861323833100425639 10446109291985749650638459)
          ·
            refine ⟨15669163937978624475957689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10446109291985749650638459 15669163937978624475957689)
            ·
              refine ⟨11751872953483968356968267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15669163937978624475957689 11751872953483968356968267)
              ·
                refine ⟨17627809430225952535452401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11751872953483968356968267 17627809430225952535452401)
                ·
                  refine ⟨13220857072669464401589301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17627809430225952535452401 13220857072669464401589301)
                  ·
                    refine ⟨1239455350562762287648997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13220857072669464401589301 1239455350562762287648997)
                    ·
                      rfl

theorem cell23_7241492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 2, 1, 2, 5].length) (baseStart_7241492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7241492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7241492 prefixEnd_7241492 := by exact prefixLift 7241492
  have htrace : WordTrace (prefixWord ++ tailWord_7241492) baseStart_7241492 baseEnd_7241492 := by
    simpa [prefixWord, tailWord_7241492, baseEnd_7241492] using wordTrace_append hprefix tailTrace_7241492
  have hstable : (prefixWord ++ tailWord_7241492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7241492).length < 2 ^ (prefixWord ++ tailWord_7241492).sum := by decide
  have hdescent : baseEnd_7241492 < baseStart_7241492 := by decide
  rcases family_descends (prefixWord ++ tailWord_7241492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7241498 : List Nat := [3, 1, 1, 3, 2, 3, 2, 1, 2, 2, 3]
def baseStart_7241498 : Nat := 118140960795 + 7241498 * 2 ^ 59
def prefixEnd_7241498 : Nat := 4983230072969 + 3 ^ 40 * 7241498 * 2
def baseEnd_7241498 : Nat := 3718369132572213839471963

theorem tailTrace_7241498 : CollatzResearch.WordTrace tailWord_7241498 prefixEnd_7241498 3718369132572213839471963 := by
  unfold tailWord_7241498
  simp only [CollatzResearch.WordTrace]
  refine ⟨66029782579824242560215287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176079420212864646827240765 66029782579824242560215287)
  ·
    refine ⟨99044673869736363840322931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66029782579824242560215287 99044673869736363840322931)
    ·
      refine ⟨148567010804604545760484397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99044673869736363840322931 148567010804604545760484397)
      ·
        refine ⟨55712629051726704660181649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 148567010804604545760484397 55712629051726704660181649)
        ·
          refine ⟨41784471788795028495136237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55712629051726704660181649 41784471788795028495136237)
          ·
            refine ⟨15669176920798135685676089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41784471788795028495136237 15669176920798135685676089)
            ·
              refine ⟨11751882690598601764257067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15669176920798135685676089 11751882690598601764257067)
              ·
                refine ⟨17627824035897902646385601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11751882690598601764257067 17627824035897902646385601)
                ·
                  refine ⟨13220868026923426984789201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17627824035897902646385601 13220868026923426984789201)
                  ·
                    refine ⟨9915651020192570238591901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13220868026923426984789201 9915651020192570238591901)
                    ·
                      refine ⟨3718369132572213839471963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9915651020192570238591901 3718369132572213839471963)
                      ·
                        rfl

theorem cell23_7241498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 2, 1, 2, 2, 3].length) (baseStart_7241498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7241498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7241498 prefixEnd_7241498 := by exact prefixLift 7241498
  have htrace : WordTrace (prefixWord ++ tailWord_7241498) baseStart_7241498 baseEnd_7241498 := by
    simpa [prefixWord, tailWord_7241498, baseEnd_7241498] using wordTrace_append hprefix tailTrace_7241498
  have hstable : (prefixWord ++ tailWord_7241498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7241498).length < 2 ^ (prefixWord ++ tailWord_7241498).sum := by decide
  have hdescent : baseEnd_7241498 < baseStart_7241498 := by decide
  rcases family_descends (prefixWord ++ tailWord_7241498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7241522 : List Nat := [3, 2, 1, 1, 3, 4, 2, 2, 1, 4]
def baseStart_7241522 : Nat := 118140960795 + 7241522 * 2 ^ 59
def prefixEnd_7241522 : Nat := 4983230072969 + 3 ^ 40 * 7241522 * 2
def baseEnd_7241522 : Nat := 1239460485369307248523951

theorem tailTrace_7241522 : CollatzResearch.WordTrace tailWord_7241522 prefixEnd_7241522 1239460485369307248523951 := by
  unfold tailWord_7241522
  simp only [CollatzResearch.WordTrace]
  refine ⟨66030001417802505584933705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176080003780806681559823213 66030001417802505584933705)
  ·
    refine ⟨49522501063351879188700279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66030001417802505584933705 49522501063351879188700279)
    ·
      refine ⟨74283751595027818783050419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49522501063351879188700279 74283751595027818783050419)
      ·
        refine ⟨111425627392541728174575629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74283751595027818783050419 111425627392541728174575629)
        ·
          refine ⟨41784610272203148065465861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 111425627392541728174575629 41784610272203148065465861)
          ·
            refine ⟨7834614426038090262274849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41784610272203148065465861 7834614426038090262274849)
            ·
              refine ⟨5875960819528567696706137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7834614426038090262274849 5875960819528567696706137)
              ·
                refine ⟨4406970614646425772529603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5875960819528567696706137 4406970614646425772529603)
                ·
                  refine ⟨6610455921969638658794405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4406970614646425772529603 6610455921969638658794405)
                  ·
                    refine ⟨1239460485369307248523951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6610455921969638658794405 1239460485369307248523951)
                    ·
                      rfl

theorem cell23_7241522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 4, 2, 2, 1, 4].length) (baseStart_7241522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7241522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7241522 prefixEnd_7241522 := by exact prefixLift 7241522
  have htrace : WordTrace (prefixWord ++ tailWord_7241522) baseStart_7241522 baseEnd_7241522 := by
    simpa [prefixWord, tailWord_7241522, baseEnd_7241522] using wordTrace_append hprefix tailTrace_7241522
  have hstable : (prefixWord ++ tailWord_7241522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7241522).length < 2 ^ (prefixWord ++ tailWord_7241522).sum := by decide
  have hdescent : baseEnd_7241522 < baseStart_7241522 := by decide
  rcases family_descends (prefixWord ++ tailWord_7241522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7241561 : List Nat := [1, 2, 1, 2, 2, 3, 2, 2, 4, 4]
def baseStart_7241561 : Nat := 118140960795 + 7241561 * 2 ^ 59
def prefixEnd_7241561 : Nat := 4983230072969 + 3 ^ 40 * 7241561 * 2
def baseEnd_7241561 : Nat := 1239467160617815697661391

theorem tailTrace_7241561 : CollatzResearch.WordTrace tailWord_7241561 prefixEnd_7241561 1239467160617815697661391 := by
  unfold tailWord_7241561
  simp only [CollatzResearch.WordTrace]
  refine ⟨264121428118068732000404537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176080952078712488000269691 264121428118068732000404537)
  ·
    refine ⟨198091071088551549000303403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 264121428118068732000404537 198091071088551549000303403)
    ·
      refine ⟨297136606632827323500455105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198091071088551549000303403 297136606632827323500455105)
      ·
        refine ⟨222852454974620492625341329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 297136606632827323500455105 222852454974620492625341329)
        ·
          refine ⟨167139341230965369469005997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 222852454974620492625341329 167139341230965369469005997)
          ·
            refine ⟨62677252961612013550877249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 167139341230965369469005997 62677252961612013550877249)
            ·
              refine ⟨47007939721209010163157937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62677252961612013550877249 47007939721209010163157937)
              ·
                refine ⟨35255954790906757622368453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47007939721209010163157937 35255954790906757622368453)
                ·
                  refine ⟨6610491523295017054194085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35255954790906757622368453 6610491523295017054194085)
                  ·
                    refine ⟨1239467160617815697661391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6610491523295017054194085 1239467160617815697661391)
                    ·
                      rfl

theorem cell23_7241561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 2, 2, 4, 4].length) (baseStart_7241561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7241561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7241561 prefixEnd_7241561 := by exact prefixLift 7241561
  have htrace : WordTrace (prefixWord ++ tailWord_7241561) baseStart_7241561 baseEnd_7241561 := by
    simpa [prefixWord, tailWord_7241561, baseEnd_7241561] using wordTrace_append hprefix tailTrace_7241561
  have hstable : (prefixWord ++ tailWord_7241561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7241561).length < 2 ^ (prefixWord ++ tailWord_7241561).sum := by decide
  have hdescent : baseEnd_7241561 < baseStart_7241561 := by decide
  rcases family_descends (prefixWord ++ tailWord_7241561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7241568 : List Nat := [2, 1, 1, 3, 3, 3, 1, 3, 1, 1, 4]
def baseStart_7241568 : Nat := 118140960795 + 7241568 * 2 ^ 59
def prefixEnd_7241568 : Nat := 4983230072969 + 3 ^ 40 * 7241568 * 2
def baseEnd_7241568 : Nat := 3718405076218028565596641

theorem tailTrace_7241568 : CollatzResearch.WordTrace tailWord_7241568 prefixEnd_7241568 3718405076218028565596641 := by
  unfold tailWord_7241568
  simp only [CollatzResearch.WordTrace]
  refine ⟨132060841714521686097954679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176081122286028914797272905 132060841714521686097954679)
  ·
    refine ⟨198091262571782529146932019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132060841714521686097954679 198091262571782529146932019)
    ·
      refine ⟨297136893857673793720398029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198091262571782529146932019 297136893857673793720398029)
      ·
        refine ⟨111426335196627672645149261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 297136893857673793720398029 111426335196627672645149261)
        ·
          refine ⟨41784875698735377241930973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 111426335196627672645149261 41784875698735377241930973)
          ·
            refine ⟨15669328387025766465724115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41784875698735377241930973 15669328387025766465724115)
            ·
              refine ⟨23503992580538649698586173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15669328387025766465724115 23503992580538649698586173)
              ·
                refine ⟨8813997217701993636969815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23503992580538649698586173 8813997217701993636969815)
                ·
                  refine ⟨13220995826552990455454723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8813997217701993636969815 13220995826552990455454723)
                  ·
                    refine ⟨19831493739829485683182085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13220995826552990455454723 19831493739829485683182085)
                    ·
                      refine ⟨3718405076218028565596641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19831493739829485683182085 3718405076218028565596641)
                      ·
                        rfl

theorem cell23_7241568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 1, 3, 1, 1, 4].length) (baseStart_7241568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7241568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7241568 prefixEnd_7241568 := by exact prefixLift 7241568
  have htrace : WordTrace (prefixWord ++ tailWord_7241568) baseStart_7241568 baseEnd_7241568 := by
    simpa [prefixWord, tailWord_7241568, baseEnd_7241568] using wordTrace_append hprefix tailTrace_7241568
  have hstable : (prefixWord ++ tailWord_7241568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7241568).length < 2 ^ (prefixWord ++ tailWord_7241568).sum := by decide
  have hdescent : baseEnd_7241568 < baseStart_7241568 := by decide
  rcases family_descends (prefixWord ++ tailWord_7241568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7241581 : List Nat := [1, 5, 1, 1, 1, 1, 2, 2, 3, 2, 4]
def baseStart_7241581 : Nat := 118140960795 + 7241581 * 2 ^ 59
def prefixEnd_7241581 : Nat := 4983230072969 + 3 ^ 40 * 7241581 * 2
def baseEnd_7241581 : Nat := 3718411751466537014734081

theorem tailTrace_7241581 : CollatzResearch.WordTrace tailWord_7241581 prefixEnd_7241581 3718411751466537014734081 := by
  unfold tailWord_7241581
  simp only [CollatzResearch.WordTrace]
  refine ⟨264122157577996275416132597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176081438385330850277421731 264122157577996275416132597)
  ·
    refine ⟨24761452272937150820262431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 264122157577996275416132597 24761452272937150820262431)
    ·
      refine ⟨37142178409405726230393647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24761452272937150820262431 37142178409405726230393647)
      ·
        refine ⟨55713267614108589345590471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37142178409405726230393647 55713267614108589345590471)
        ·
          refine ⟨83569901421162884018385707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55713267614108589345590471 83569901421162884018385707)
          ·
            refine ⟨125354852131744326027578561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83569901421162884018385707 125354852131744326027578561)
            ·
              refine ⟨94016139098808244520683921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 125354852131744326027578561 94016139098808244520683921)
              ·
                refine ⟨70512104324106183390512941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 94016139098808244520683921 70512104324106183390512941)
                ·
                  refine ⟨26442039121539818771442353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 70512104324106183390512941 26442039121539818771442353)
                  ·
                    refine ⟨19831529341154864078581765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26442039121539818771442353 19831529341154864078581765)
                    ·
                      refine ⟨3718411751466537014734081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19831529341154864078581765 3718411751466537014734081)
                      ·
                        rfl

theorem cell23_7241581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 2, 3, 2, 4].length) (baseStart_7241581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7241581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7241581 prefixEnd_7241581 := by exact prefixLift 7241581
  have htrace : WordTrace (prefixWord ++ tailWord_7241581) baseStart_7241581 baseEnd_7241581 := by
    simpa [prefixWord, tailWord_7241581, baseEnd_7241581] using wordTrace_append hprefix tailTrace_7241581
  have hstable : (prefixWord ++ tailWord_7241581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7241581).length < 2 ^ (prefixWord ++ tailWord_7241581).sum := by decide
  have hdescent : baseEnd_7241581 < baseStart_7241581 := by decide
  rcases family_descends (prefixWord ++ tailWord_7241581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7241584 : List Nat := [2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 7]
def baseStart_7241584 : Nat := 118140960795 + 7241584 * 2 ^ 59
def prefixEnd_7241584 : Nat := 4983230072969 + 3 ^ 40 * 7241584 * 2
def baseEnd_7241584 : Nat := 3718413291908500502996567

theorem tailTrace_7241584 : CollatzResearch.WordTrace tailWord_7241584 prefixEnd_7241584 3718413291908500502996567 := by
  unfold tailWord_7241584
  simp only [CollatzResearch.WordTrace]
  refine ⟨132061133498492703464245903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176081511331323604618994537 132061133498492703464245903)
  ·
    refine ⟨198091700247739055196368855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132061133498492703464245903 198091700247739055196368855)
    ·
      refine ⟨297137550371608582794553283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198091700247739055196368855 297137550371608582794553283)
      ·
        refine ⟨445706325557412874191829925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 297137550371608582794553283 445706325557412874191829925)
        ·
          refine ⟨83569936042014913910968111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 445706325557412874191829925 83569936042014913910968111)
          ·
            refine ⟨125354904063022370866452167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83569936042014913910968111 125354904063022370866452167)
            ·
              refine ⟨188032356094533556299678251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125354904063022370866452167 188032356094533556299678251)
              ·
                refine ⟨282048534141800334449517377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 188032356094533556299678251 282048534141800334449517377)
                ·
                  refine ⟨211536400606350250837138033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 282048534141800334449517377 211536400606350250837138033)
                  ·
                    refine ⟨158652300454762688127853525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 211536400606350250837138033 158652300454762688127853525)
                    ·
                      refine ⟨3718413291908500502996567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 158652300454762688127853525 3718413291908500502996567)
                      ·
                        rfl

theorem cell23_7241584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 7].length) (baseStart_7241584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7241584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7241584 prefixEnd_7241584 := by exact prefixLift 7241584
  have htrace : WordTrace (prefixWord ++ tailWord_7241584) baseStart_7241584 baseEnd_7241584 := by
    simpa [prefixWord, tailWord_7241584, baseEnd_7241584] using wordTrace_append hprefix tailTrace_7241584
  have hstable : (prefixWord ++ tailWord_7241584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7241584).length < 2 ^ (prefixWord ++ tailWord_7241584).sum := by decide
  have hdescent : baseEnd_7241584 < baseStart_7241584 := by decide
  rcases family_descends (prefixWord ++ tailWord_7241584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7241585 : List Nat := [1, 2, 2, 2, 1, 3, 4, 1, 3, 2, 2]
def baseStart_7241585 : Nat := 118140960795 + 7241585 * 2 ^ 59
def prefixEnd_7241585 : Nat := 4983230072969 + 3 ^ 40 * 7241585 * 2
def baseEnd_7241585 : Nat := 3718413805389154999084063

theorem tailTrace_7241585 : CollatzResearch.WordTrace tailWord_7241585 prefixEnd_7241585 3718413805389154999084063 := by
  unfold tailWord_7241585
  simp only [CollatzResearch.WordTrace]
  refine ⟨264122303469981784099278209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176081535646654522732852139 264122303469981784099278209)
  ·
    refine ⟨198091727602486338074458657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 264122303469981784099278209 198091727602486338074458657)
    ·
      refine ⟨148568795701864753555843993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 198091727602486338074458657 148568795701864753555843993)
      ·
        refine ⟨111426596776398565166882995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148568795701864753555843993 111426596776398565166882995)
        ·
          refine ⟨167139895164597847750324493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111426596776398565166882995 167139895164597847750324493)
          ·
            refine ⟨62677460686724192906371685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 167139895164597847750324493 62677460686724192906371685)
            ·
              refine ⟨11752023878760786169944691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 62677460686724192906371685 11752023878760786169944691)
              ·
                refine ⟨17628035818141179254917037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11752023878760786169944691 17628035818141179254917037)
                ·
                  refine ⟨6610513431802942220593889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17628035818141179254917037 6610513431802942220593889)
                  ·
                    refine ⟨4957885073852206665445417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6610513431802942220593889 4957885073852206665445417)
                    ·
                      refine ⟨3718413805389154999084063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4957885073852206665445417 3718413805389154999084063)
                      ·
                        rfl

theorem cell23_7241585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 4, 1, 3, 2, 2].length) (baseStart_7241585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7241585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7241585 prefixEnd_7241585 := by exact prefixLift 7241585
  have htrace : WordTrace (prefixWord ++ tailWord_7241585) baseStart_7241585 baseEnd_7241585 := by
    simpa [prefixWord, tailWord_7241585, baseEnd_7241585] using wordTrace_append hprefix tailTrace_7241585
  have hstable : (prefixWord ++ tailWord_7241585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7241585).length < 2 ^ (prefixWord ++ tailWord_7241585).sum := by decide
  have hdescent : baseEnd_7241585 < baseStart_7241585 := by decide
  rcases family_descends (prefixWord ++ tailWord_7241585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7241662 : List Nat := [4, 2, 1, 1, 1, 3, 3, 2, 1, 3, 2]
def baseStart_7241662 : Nat := 118140960795 + 7241662 * 2 ^ 59
def prefixEnd_7241662 : Nat := 4983230072969 + 3 ^ 40 * 7241662 * 2
def baseEnd_7241662 : Nat := 3718453343399551197821209

theorem tailTrace_7241662 : CollatzResearch.WordTrace tailWord_7241662 prefixEnd_7241662 3718453343399551197821209 := by
  unfold tailWord_7241662
  simp only [CollatzResearch.WordTrace]
  refine ⟨33015638986337853281228905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 176083407927135217499887493 33015638986337853281228905)
  ·
    refine ⟨24761729239753389960921679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33015638986337853281228905 24761729239753389960921679)
    ·
      refine ⟨37142593859630084941382519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24761729239753389960921679 37142593859630084941382519)
      ·
        refine ⟨55713890789445127412073779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37142593859630084941382519 55713890789445127412073779)
        ·
          refine ⟨83570836184167691118110669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55713890789445127412073779 83570836184167691118110669)
          ·
            refine ⟨31339063569062884169291501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 83570836184167691118110669 31339063569062884169291501)
            ·
              refine ⟨11752148838398581563484313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31339063569062884169291501 11752148838398581563484313)
              ·
                refine ⟨8814111628798936172613235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11752148838398581563484313 8814111628798936172613235)
                ·
                  refine ⟨13221167443198404258919853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8814111628798936172613235 13221167443198404258919853)
                  ·
                    refine ⟨4957937791199401597094945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13221167443198404258919853 4957937791199401597094945)
                    ·
                      refine ⟨3718453343399551197821209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4957937791199401597094945 3718453343399551197821209)
                      ·
                        rfl

theorem cell23_7241662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 3, 2, 1, 3, 2].length) (baseStart_7241662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7241662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7241662 prefixEnd_7241662 := by exact prefixLift 7241662
  have htrace : WordTrace (prefixWord ++ tailWord_7241662) baseStart_7241662 baseEnd_7241662 := by
    simpa [prefixWord, tailWord_7241662, baseEnd_7241662] using wordTrace_append hprefix tailTrace_7241662
  have hstable : (prefixWord ++ tailWord_7241662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7241662).length < 2 ^ (prefixWord ++ tailWord_7241662).sum := by decide
  have hdescent : baseEnd_7241662 < baseStart_7241662 := by decide
  rcases family_descends (prefixWord ++ tailWord_7241662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7241671 : List Nat := [1, 1, 4, 1, 1, 2, 1, 2, 4, 2, 4]
def baseStart_7241671 : Nat := 118140960795 + 7241671 * 2 ^ 59
def prefixEnd_7241671 : Nat := 4983230072969 + 3 ^ 40 * 7241671 * 2
def baseEnd_7241671 : Nat := 3718457964725441662608667

theorem tailTrace_7241671 : CollatzResearch.WordTrace tailWord_7241671 prefixEnd_7241671 3718457964725441662608667 := by
  unfold tailWord_7241671
  simp only [CollatzResearch.WordTrace]
  refine ⟨264125440147670220786908867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176083626765113480524605911 264125440147670220786908867)
  ·
    refine ⟨396188160221505331180363301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264125440147670220786908867 396188160221505331180363301)
    ·
      refine ⟨74285280041532249596318119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 396188160221505331180363301 74285280041532249596318119)
      ·
        refine ⟨111427920062298374394477179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74285280041532249596318119 111427920062298374394477179)
        ·
          refine ⟨167141880093447561591715769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111427920062298374394477179 167141880093447561591715769)
          ·
            refine ⟨125356410070085671193786827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 167141880093447561591715769 125356410070085671193786827)
            ·
              refine ⟨188034615105128506790680241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125356410070085671193786827 188034615105128506790680241)
              ·
                refine ⟨141025961328846380093010181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 188034615105128506790680241 141025961328846380093010181)
                ·
                  refine ⟨26442367749158696267439409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 141025961328846380093010181 26442367749158696267439409)
                  ·
                    refine ⟨19831775811869022200579557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26442367749158696267439409 19831775811869022200579557)
                    ·
                      refine ⟨3718457964725441662608667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19831775811869022200579557 3718457964725441662608667)
                      ·
                        rfl

theorem cell23_7241671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 2, 4, 2, 4].length) (baseStart_7241671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7241671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7241671 prefixEnd_7241671 := by exact prefixLift 7241671
  have htrace : WordTrace (prefixWord ++ tailWord_7241671) baseStart_7241671 baseEnd_7241671 := by
    simpa [prefixWord, tailWord_7241671, baseEnd_7241671] using wordTrace_append hprefix tailTrace_7241671
  have hstable : (prefixWord ++ tailWord_7241671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7241671).length < 2 ^ (prefixWord ++ tailWord_7241671).sum := by decide
  have hdescent : baseEnd_7241671 < baseStart_7241671 := by decide
  rcases family_descends (prefixWord ++ tailWord_7241671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7241709 : List Nat := [1, 5, 1, 4, 1, 1, 2, 1, 1, 4, 2]
def baseStart_7241709 : Nat := 118140960795 + 7241709 * 2 ^ 59
def prefixEnd_7241709 : Nat := 4983230072969 + 3 ^ 40 * 7241709 * 2
def baseEnd_7241709 : Nat := 3718477476990312513933493

theorem tailTrace_7241709 : CollatzResearch.WordTrace tailWord_7241709 prefixEnd_7241709 3718477476990312513933493 := by
  unfold tailWord_7241709
  simp only [CollatzResearch.WordTrace]
  refine ⟨264126826121532553276792181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176084550747688368851194787 264126826121532553276792181)
  ·
    refine ⟨24761889948893676869699267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 264126826121532553276792181 24761889948893676869699267)
    ·
      refine ⟨37142834923340515304548901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24761889948893676869699267 37142834923340515304548901)
      ·
        refine ⟨6964281548126346619602919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37142834923340515304548901 6964281548126346619602919)
        ·
          refine ⟨10446422322189519929404379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6964281548126346619602919 10446422322189519929404379)
          ·
            refine ⟨15669633483284279894106569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10446422322189519929404379 15669633483284279894106569)
            ·
              refine ⟨11752225112463209920579927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15669633483284279894106569 11752225112463209920579927)
              ·
                refine ⟨17628337668694814880869891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11752225112463209920579927 17628337668694814880869891)
                ·
                  refine ⟨26442506503042222321304837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17628337668694814880869891 26442506503042222321304837)
                  ·
                    refine ⟨4957969969320416685244657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26442506503042222321304837 4957969969320416685244657)
                    ·
                      refine ⟨3718477476990312513933493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4957969969320416685244657 3718477476990312513933493)
                      ·
                        rfl

theorem cell23_7241709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 2, 1, 1, 4, 2].length) (baseStart_7241709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7241709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7241709 prefixEnd_7241709 := by exact prefixLift 7241709
  have htrace : WordTrace (prefixWord ++ tailWord_7241709) baseStart_7241709 baseEnd_7241709 := by
    simpa [prefixWord, tailWord_7241709, baseEnd_7241709] using wordTrace_append hprefix tailTrace_7241709
  have hstable : (prefixWord ++ tailWord_7241709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7241709).length < 2 ^ (prefixWord ++ tailWord_7241709).sum := by decide
  have hdescent : baseEnd_7241709 < baseStart_7241709 := by decide
  rcases family_descends (prefixWord ++ tailWord_7241709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7241711 : List Nat := [1, 1, 2, 1, 4, 2, 2, 2, 1, 7]
def baseStart_7241711 : Nat := 118140960795 + 7241711 * 2 ^ 59
def prefixEnd_7241711 : Nat := 4983230072969 + 3 ^ 40 * 7241711 * 2
def baseEnd_7241711 : Nat := 1239492834650540502036161

theorem tailTrace_7241711 : CollatzResearch.WordTrace tailWord_7241711 prefixEnd_7241711 1239492834650540502036161 := by
  unfold tailWord_7241711
  simp only [CollatzResearch.WordTrace]
  refine ⟨264126899067525307618364987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176084599378350205078909991 264126899067525307618364987)
  ·
    refine ⟨396190348601287961427547481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264126899067525307618364987 396190348601287961427547481)
    ·
      refine ⟨297142761450965971070660611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 396190348601287961427547481 297142761450965971070660611)
      ·
        refine ⟨445714142176448956605990917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 297142761450965971070660611 445714142176448956605990917)
        ·
          refine ⟨83571401658084179363623297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 445714142176448956605990917 83571401658084179363623297)
          ·
            refine ⟨62678551243563134522717473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83571401658084179363623297 62678551243563134522717473)
            ·
              refine ⟨47008913432672350892038105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62678551243563134522717473 47008913432672350892038105)
              ·
                refine ⟨35256685074504263169028579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47008913432672350892038105 35256685074504263169028579)
                ·
                  refine ⟨52885027611756394753542869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35256685074504263169028579 52885027611756394753542869)
                  ·
                    refine ⟨1239492834650540502036161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 52885027611756394753542869 1239492834650540502036161)
                    ·
                      rfl

theorem cell23_7241711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 2, 2, 1, 7].length) (baseStart_7241711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7241711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7241711 prefixEnd_7241711 := by exact prefixLift 7241711
  have htrace : WordTrace (prefixWord ++ tailWord_7241711) baseStart_7241711 baseEnd_7241711 := by
    simpa [prefixWord, tailWord_7241711, baseEnd_7241711] using wordTrace_append hprefix tailTrace_7241711
  have hstable : (prefixWord ++ tailWord_7241711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7241711).length < 2 ^ (prefixWord ++ tailWord_7241711).sum := by decide
  have hdescent : baseEnd_7241711 < baseStart_7241711 := by decide
  rcases family_descends (prefixWord ++ tailWord_7241711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7241765 : List Nat := [1, 3, 1, 2, 2, 3, 2, 1, 2, 4, 2]
def baseStart_7241765 : Nat := 118140960795 + 7241765 * 2 ^ 59
def prefixEnd_7241765 : Nat := 4983230072969 + 3 ^ 40 * 7241765 * 2
def baseEnd_7241765 : Nat := 3718506231906964294833235

theorem tailTrace_7241765 : CollatzResearch.WordTrace tailWord_7241765 prefixEnd_7241765 3718506231906964294833235 := by
  unfold tailWord_7241765
  simp only [CollatzResearch.WordTrace]
  refine ⟨264128868609329674840830749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176085912406219783227220499 264128868609329674840830749)
  ·
    refine ⟨99048325728498628065311531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 264128868609329674840830749 99048325728498628065311531)
    ·
      refine ⟨148572488592747942097967297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99048325728498628065311531 148572488592747942097967297)
      ·
        refine ⟨111429366444560956573475473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148572488592747942097967297 111429366444560956573475473)
        ·
          refine ⟨83572024833420717430106605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111429366444560956573475473 83572024833420717430106605)
          ·
            refine ⟨31339509312532769036289977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 83572024833420717430106605 31339509312532769036289977)
            ·
              refine ⟨23504631984399576777217483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31339509312532769036289977 23504631984399576777217483)
              ·
                refine ⟨35256947976599365165826225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23504631984399576777217483 35256947976599365165826225)
                ·
                  refine ⟨26442710982449523874369669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35256947976599365165826225 26442710982449523874369669)
                  ·
                    refine ⟨4958008309209285726444313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26442710982449523874369669 4958008309209285726444313)
                    ·
                      refine ⟨3718506231906964294833235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4958008309209285726444313 3718506231906964294833235)
                      ·
                        rfl

theorem cell23_7241765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 2, 1, 2, 4, 2].length) (baseStart_7241765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7241765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7241765 prefixEnd_7241765 := by exact prefixLift 7241765
  have htrace : WordTrace (prefixWord ++ tailWord_7241765) baseStart_7241765 baseEnd_7241765 := by
    simpa [prefixWord, tailWord_7241765, baseEnd_7241765] using wordTrace_append hprefix tailTrace_7241765
  have hstable : (prefixWord ++ tailWord_7241765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7241765).length < 2 ^ (prefixWord ++ tailWord_7241765).sum := by decide
  have hdescent : baseEnd_7241765 < baseStart_7241765 := by decide
  rcases family_descends (prefixWord ++ tailWord_7241765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7241792 : List Nat := [2, 1, 1, 2, 2, 4, 3, 3, 1, 4]
def baseStart_7241792 : Nat := 118140960795 + 7241792 * 2 ^ 59
def prefixEnd_7241792 : Nat := 4983230072969 + 3 ^ 40 * 7241792 * 2
def baseEnd_7241792 : Nat := 1239506698628211896398537

theorem tailTrace_7241792 : CollatzResearch.WordTrace tailWord_7241792 prefixEnd_7241792 1239506698628211896398537 := by
  unfold tailWord_7241792
  simp only [CollatzResearch.WordTrace]
  refine ⟨132064926690115929226031815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176086568920154572301375753 132064926690115929226031815)
  ·
    refine ⟨198097390035173893839047723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132064926690115929226031815 198097390035173893839047723)
    ·
      refine ⟨297146085052760840758571585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198097390035173893839047723 297146085052760840758571585)
      ·
        refine ⟨222859563789570630568928689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 297146085052760840758571585 222859563789570630568928689)
        ·
          refine ⟨167144672842177972926696517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 222859563789570630568928689 167144672842177972926696517)
          ·
            refine ⟨31339626157908369923755597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 167144672842177972926696517 31339626157908369923755597)
            ·
              refine ⟨11752359809215638721408349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31339626157908369923755597 11752359809215638721408349)
              ·
                refine ⟨4407134928455864520528131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11752359809215638721408349 4407134928455864520528131)
                ·
                  refine ⟨6610702392683796780792197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4407134928455864520528131 6610702392683796780792197)
                  ·
                    refine ⟨1239506698628211896398537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6610702392683796780792197 1239506698628211896398537)
                    ·
                      rfl

theorem cell23_7241792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 3, 3, 1, 4].length) (baseStart_7241792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7241792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7241792 prefixEnd_7241792 := by exact prefixLift 7241792
  have htrace : WordTrace (prefixWord ++ tailWord_7241792) baseStart_7241792 baseEnd_7241792 := by
    simpa [prefixWord, tailWord_7241792, baseEnd_7241792] using wordTrace_append hprefix tailTrace_7241792
  have hstable : (prefixWord ++ tailWord_7241792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7241792).length < 2 ^ (prefixWord ++ tailWord_7241792).sum := by decide
  have hdescent : baseEnd_7241792 < baseStart_7241792 := by decide
  rcases family_descends (prefixWord ++ tailWord_7241792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7241805 : List Nat := [1, 6, 1, 1, 1, 1, 2, 4, 6]
def baseStart_7241805 : Nat := 118140960795 + 7241805 * 2 ^ 59
def prefixEnd_7241805 : Nat := 4983230072969 + 3 ^ 40 * 7241805 * 2
def baseEnd_7241805 : Nat := 413169641237016015370339

theorem tailTrace_7241805 : CollatzResearch.WordTrace tailWord_7241805 prefixEnd_7241805 413169641237016015370339 := by
  unfold tailWord_7241805
  simp only [CollatzResearch.WordTrace]
  refine ⟨264130327529184761672286869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176086885019456507781524579 264130327529184761672286869)
  ·
    refine ⟨12381109102930535703388447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 264130327529184761672286869 12381109102930535703388447)
    ·
      refine ⟨18571663654395803555082671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12381109102930535703388447 18571663654395803555082671)
      ·
        refine ⟨27857495481593705332624007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18571663654395803555082671 27857495481593705332624007)
        ·
          refine ⟨41786243222390557998936011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27857495481593705332624007 41786243222390557998936011)
          ·
            refine ⟨62679364833585836998404017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41786243222390557998936011 62679364833585836998404017)
            ·
              refine ⟨47009523625189377748803013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62679364833585836998404017 47009523625189377748803013)
              ·
                refine ⟨8814285679723008327900565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47009523625189377748803013 8814285679723008327900565)
                ·
                  refine ⟨413169641237016015370339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8814285679723008327900565 413169641237016015370339)
                  ·
                    rfl

theorem cell23_7241805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 2, 4, 6].length) (baseStart_7241805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7241805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7241805 prefixEnd_7241805 := by exact prefixLift 7241805
  have htrace : WordTrace (prefixWord ++ tailWord_7241805) baseStart_7241805 baseEnd_7241805 := by
    simpa [prefixWord, tailWord_7241805, baseEnd_7241805] using wordTrace_append hprefix tailTrace_7241805
  have hstable : (prefixWord ++ tailWord_7241805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7241805).length < 2 ^ (prefixWord ++ tailWord_7241805).sum := by decide
  have hdescent : baseEnd_7241805 < baseStart_7241805 := by decide
  rcases family_descends (prefixWord ++ tailWord_7241805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7241818 : List Nat := [3, 1, 1, 2, 1, 1, 4, 2, 3, 5]
def baseStart_7241818 : Nat := 118140960795 + 7241818 * 2 ^ 59
def prefixEnd_7241818 : Nat := 4983230072969 + 3 ^ 40 * 7241818 * 2
def baseEnd_7241818 : Nat := 1239511148793884195823497

theorem tailTrace_7241818 : CollatzResearch.WordTrace tailWord_7241818 prefixEnd_7241818 1239511148793884195823497 := by
  unfold tailWord_7241818
  simp only [CollatzResearch.WordTrace]
  refine ⟨66032700419534416223127527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176087201118758443261673405 66032700419534416223127527)
  ·
    refine ⟨99049050629301624334691291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66032700419534416223127527 99049050629301624334691291)
    ·
      refine ⟨148573575943952436502036937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99049050629301624334691291 148573575943952436502036937)
      ·
        refine ⟨111430181957964327376527703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148573575943952436502036937 111430181957964327376527703)
        ·
          refine ⟨167145272936946491064791555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111430181957964327376527703 167145272936946491064791555)
          ·
            refine ⟨250717909405419736597187333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 167145272936946491064791555 250717909405419736597187333)
            ·
              refine ⟨47009608013516200611972625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 250717909405419736597187333 47009608013516200611972625)
              ·
                refine ⟨35257206010137150458979469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47009608013516200611972625 35257206010137150458979469)
                ·
                  refine ⟨13221452253801431422117301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35257206010137150458979469 13221452253801431422117301)
                  ·
                    refine ⟨1239511148793884195823497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13221452253801431422117301 1239511148793884195823497)
                    ·
                      rfl

theorem cell23_7241818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 4, 2, 3, 5].length) (baseStart_7241818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7241818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7241818 prefixEnd_7241818 := by exact prefixLift 7241818
  have htrace : WordTrace (prefixWord ++ tailWord_7241818) baseStart_7241818 baseEnd_7241818 := by
    simpa [prefixWord, tailWord_7241818, baseEnd_7241818] using wordTrace_append hprefix tailTrace_7241818
  have hstable : (prefixWord ++ tailWord_7241818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7241818).length < 2 ^ (prefixWord ++ tailWord_7241818).sum := by decide
  have hdescent : baseEnd_7241818 < baseStart_7241818 := by decide
  rcases family_descends (prefixWord ++ tailWord_7241818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7241825 : List Nat := [1, 2, 3, 1, 1, 2, 1, 1, 6, 3, 2]
def baseStart_7241825 : Nat := 118140960795 + 7241825 * 2 ^ 59
def prefixEnd_7241825 : Nat := 4983230072969 + 3 ^ 40 * 7241825 * 2
def baseEnd_7241825 : Nat := 3718537040746234060082959

theorem tailTrace_7241825 : CollatzResearch.WordTrace tailWord_7241825 prefixEnd_7241825 3718537040746234060082959 := by
  unfold tailWord_7241825
  simp only [CollatzResearch.WordTrace]
  refine ⟨264131056989112305088014929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176087371326074870058676619 264131056989112305088014929)
  ·
    refine ⟨198098292741834228816011197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 264131056989112305088014929 198098292741834228816011197)
    ·
      refine ⟨74286859778187835806004199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 198098292741834228816011197 74286859778187835806004199)
      ·
        refine ⟨111430289667281753709006299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74286859778187835806004199 111430289667281753709006299)
        ·
          refine ⟨167145434500922630563509449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111430289667281753709006299 167145434500922630563509449)
          ·
            refine ⟨125359075875691972922632087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 167145434500922630563509449 125359075875691972922632087)
            ·
              refine ⟨188038613813537959383948131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125359075875691972922632087 188038613813537959383948131)
              ·
                refine ⟨282057920720306939075922197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 188038613813537959383948131 282057920720306939075922197)
                ·
                  refine ⟨13221465033764387769183853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 282057920720306939075922197 13221465033764387769183853)
                  ·
                    refine ⟨4958049387661645413443945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13221465033764387769183853 4958049387661645413443945)
                    ·
                      refine ⟨3718537040746234060082959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4958049387661645413443945 3718537040746234060082959)
                      ·
                        rfl

theorem cell23_7241825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 1, 6, 3, 2].length) (baseStart_7241825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7241825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7241825 prefixEnd_7241825 := by exact prefixLift 7241825
  have htrace : WordTrace (prefixWord ++ tailWord_7241825) baseStart_7241825 baseEnd_7241825 := by
    simpa [prefixWord, tailWord_7241825, baseEnd_7241825] using wordTrace_append hprefix tailTrace_7241825
  have hstable : (prefixWord ++ tailWord_7241825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7241825).length < 2 ^ (prefixWord ++ tailWord_7241825).sum := by decide
  have hdescent : baseEnd_7241825 < baseStart_7241825 := by decide
  rcases family_descends (prefixWord ++ tailWord_7241825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7241842 : List Nat := [3, 2, 1, 2, 2, 2, 1, 3, 2, 3, 2]
def baseStart_7241842 : Nat := 118140960795 + 7241842 * 2 ^ 59
def prefixEnd_7241842 : Nat := 4983230072969 + 3 ^ 40 * 7241842 * 2
def baseEnd_7241842 : Nat := 3718545769917360493570381

theorem tailTrace_7241842 : CollatzResearch.WordTrace tailWord_7241842 prefixEnd_7241842 3718545769917360493570381 := by
  unfold tailWord_7241842
  simp only [CollatzResearch.WordTrace]
  refine ⟨66032919257512679247845945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176087784686700477994255853 66032919257512679247845945)
  ·
    refine ⟨49524689443134509435884459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66032919257512679247845945 49524689443134509435884459)
    ·
      refine ⟨74287034164701764153826689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49524689443134509435884459 74287034164701764153826689)
      ·
        refine ⟨55715275623526323115370017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74287034164701764153826689 55715275623526323115370017)
        ·
          refine ⟨41786456717644742336527513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55715275623526323115370017 41786456717644742336527513)
          ·
            refine ⟨31339842538233556752395635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41786456717644742336527513 31339842538233556752395635)
            ·
              refine ⟨47009763807350335128593453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31339842538233556752395635 47009763807350335128593453)
              ·
                refine ⟨17628661427756375673222545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47009763807350335128593453 17628661427756375673222545)
                ·
                  refine ⟨13221496070817281754916909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17628661427756375673222545 13221496070817281754916909)
                  ·
                    refine ⟨4958061026556480658093841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13221496070817281754916909 4958061026556480658093841)
                    ·
                      refine ⟨3718545769917360493570381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4958061026556480658093841 3718545769917360493570381)
                      ·
                        rfl

theorem cell23_7241842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 1, 3, 2, 3, 2].length) (baseStart_7241842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7241842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7241842 prefixEnd_7241842 := by exact prefixLift 7241842
  have htrace : WordTrace (prefixWord ++ tailWord_7241842) baseStart_7241842 baseEnd_7241842 := by
    simpa [prefixWord, tailWord_7241842, baseEnd_7241842] using wordTrace_append hprefix tailTrace_7241842
  have hstable : (prefixWord ++ tailWord_7241842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7241842).length < 2 ^ (prefixWord ++ tailWord_7241842).sum := by decide
  have hdescent : baseEnd_7241842 < baseStart_7241842 := by decide
  rcases family_descends (prefixWord ++ tailWord_7241842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7241852 : List Nat := [2, 2, 2, 1, 1, 5, 3, 1, 1, 5]
def baseStart_7241852 : Nat := 118140960795 + 7241852 * 2 ^ 59
def prefixEnd_7241852 : Nat := 4983230072969 + 3 ^ 40 * 7241852 * 2
def baseEnd_7241852 : Nat := 1239516968241301818148445

theorem tailTrace_7241852 : CollatzResearch.WordTrace tailWord_7241852 prefixEnd_7241852 1239516968241301818148445 := by
  unfold tailWord_7241852
  simp only [CollatzResearch.WordTrace]
  refine ⟨132066020880007244349623905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176088027840009659132831873 132066020880007244349623905)
  ·
    refine ⟨99049515660005433262217929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132066020880007244349623905 99049515660005433262217929)
    ·
      refine ⟨74287136745004074946663447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99049515660005433262217929 74287136745004074946663447)
      ·
        refine ⟨111430705117506112419995171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74287136745004074946663447 111430705117506112419995171)
        ·
          refine ⟨167146057676259168629992757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111430705117506112419995171 167146057676259168629992757)
          ·
            refine ⟨15669942907149297059061821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 167146057676259168629992757 15669942907149297059061821)
            ·
              refine ⟨5876228590180986397148183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15669942907149297059061821 5876228590180986397148183)
              ·
                refine ⟨8814342885271479595722275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5876228590180986397148183 8814342885271479595722275)
                ·
                  refine ⟨13221514327907219393583413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8814342885271479595722275 13221514327907219393583413)
                  ·
                    refine ⟨1239516968241301818148445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13221514327907219393583413 1239516968241301818148445)
                    ·
                      rfl

theorem cell23_7241852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 3, 1, 1, 5].length) (baseStart_7241852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7241852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7241852 prefixEnd_7241852 := by exact prefixLift 7241852
  have htrace : WordTrace (prefixWord ++ tailWord_7241852) baseStart_7241852 baseEnd_7241852 := by
    simpa [prefixWord, tailWord_7241852, baseEnd_7241852] using wordTrace_append hprefix tailTrace_7241852
  have hstable : (prefixWord ++ tailWord_7241852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7241852).length < 2 ^ (prefixWord ++ tailWord_7241852).sum := by decide
  have hdescent : baseEnd_7241852 < baseStart_7241852 := by decide
  rcases family_descends (prefixWord ++ tailWord_7241852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7241866 : List Nat := [3, 1, 2, 3, 1, 2, 4, 2, 1, 1, 3]
def baseStart_7241866 : Nat := 118140960795 + 7241866 * 2 ^ 59
def prefixEnd_7241866 : Nat := 4983230072969 + 3 ^ 40 * 7241866 * 2
def baseEnd_7241866 : Nat := 3718558093453068399670271

theorem tailTrace_7241866 : CollatzResearch.WordTrace tailWord_7241866 prefixEnd_7241866 3718558093453068399670271 := by
  unfold tailWord_7241866
  simp only [CollatzResearch.WordTrace]
  refine ⟨66033138095490942272564363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176088368254642512726838301 66033138095490942272564363)
  ·
    refine ⟨99049707143236413408846545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66033138095490942272564363 99049707143236413408846545)
    ·
      refine ⟨74287280357427310056634909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99049707143236413408846545 74287280357427310056634909)
      ·
        refine ⟨27857730134035241271238091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74287280357427310056634909 27857730134035241271238091)
        ·
          refine ⟨41786595201052861906857137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27857730134035241271238091 41786595201052861906857137)
          ·
            refine ⟨31339946400789646430142853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41786595201052861906857137 31339946400789646430142853)
            ·
              refine ⟨5876239950148058705651785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31339946400789646430142853 5876239950148058705651785)
              ·
                refine ⟨4407179962611044029238839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5876239950148058705651785 4407179962611044029238839)
                ·
                  refine ⟨6610769943916566043858259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4407179962611044029238839 6610769943916566043858259)
                  ·
                    refine ⟨9916154915874849065787389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6610769943916566043858259 9916154915874849065787389)
                    ·
                      refine ⟨3718558093453068399670271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9916154915874849065787389 3718558093453068399670271)
                      ·
                        rfl

theorem cell23_7241866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 4, 2, 1, 1, 3].length) (baseStart_7241866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7241866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7241866 prefixEnd_7241866 := by exact prefixLift 7241866
  have htrace : WordTrace (prefixWord ++ tailWord_7241866) baseStart_7241866 baseEnd_7241866 := by
    simpa [prefixWord, tailWord_7241866, baseEnd_7241866] using wordTrace_append hprefix tailTrace_7241866
  have hstable : (prefixWord ++ tailWord_7241866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7241866).length < 2 ^ (prefixWord ++ tailWord_7241866).sum := by decide
  have hdescent : baseEnd_7241866 < baseStart_7241866 := by decide
  rcases family_descends (prefixWord ++ tailWord_7241866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7241872 : List Nat := [2, 1, 1, 1, 1, 1, 6, 3, 3, 2, 2]
def baseStart_7241872 : Nat := 118140960795 + 7241872 * 2 ^ 59
def prefixEnd_7241872 : Nat := 4983230072969 + 3 ^ 40 * 7241872 * 2
def baseEnd_7241872 : Nat := 3718561174336995376195243

theorem tailTrace_7241872 : CollatzResearch.WordTrace tailWord_7241872 prefixEnd_7241872 3718561174336995376195243 := by
  unfold tailWord_7241872
  simp only [CollatzResearch.WordTrace]
  refine ⟨132066385609971016057487935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176088514146628021409983913 132066385609971016057487935)
  ·
    refine ⟨198099578414956524086231903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132066385609971016057487935 198099578414956524086231903)
    ·
      refine ⟨297149367622434786129347855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198099578414956524086231903 297149367622434786129347855)
      ·
        refine ⟨445724051433652179194021783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 297149367622434786129347855 445724051433652179194021783)
        ·
          refine ⟨668586077150478268791032675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 445724051433652179194021783 668586077150478268791032675)
          ·
            refine ⟨1002879115725717403186549013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 668586077150478268791032675 1002879115725717403186549013)
            ·
              refine ⟨47009958549643003274369485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1002879115725717403186549013 47009958549643003274369485)
              ·
                refine ⟨17628734456116126227888557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47009958549643003274369485 17628734456116126227888557)
                ·
                  refine ⟨6610775421043547335458209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17628734456116126227888557 6610775421043547335458209)
                  ·
                    refine ⟨4958081565782660501593657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6610775421043547335458209 4958081565782660501593657)
                    ·
                      refine ⟨3718561174336995376195243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4958081565782660501593657 3718561174336995376195243)
                      ·
                        rfl

theorem cell23_7241872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 6, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 6, 3, 3, 2, 2].length) (baseStart_7241872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7241872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7241872 prefixEnd_7241872 := by exact prefixLift 7241872
  have htrace : WordTrace (prefixWord ++ tailWord_7241872) baseStart_7241872 baseEnd_7241872 := by
    simpa [prefixWord, tailWord_7241872, baseEnd_7241872] using wordTrace_append hprefix tailTrace_7241872
  have hstable : (prefixWord ++ tailWord_7241872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7241872).length < 2 ^ (prefixWord ++ tailWord_7241872).sum := by decide
  have hdescent : baseEnd_7241872 < baseStart_7241872 := by decide
  rcases family_descends (prefixWord ++ tailWord_7241872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7241882 : List Nat := [3, 1, 1, 5, 2, 1, 2, 1, 1, 6]
def baseStart_7241882 : Nat := 118140960795 + 7241882 * 2 ^ 59
def prefixEnd_7241882 : Nat := 4983230072969 + 3 ^ 40 * 7241882 * 2
def baseEnd_7241882 : Nat := 1239522103047846779023399

theorem tailTrace_7241882 : CollatzResearch.WordTrace tailWord_7241882 prefixEnd_7241882 1239522103047846779023399 := by
  unfold tailWord_7241882
  simp only [CollatzResearch.WordTrace]
  refine ⟨66033283987476450955709975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176088757299937202548559933 66033283987476450955709975)
  ·
    refine ⟨99049925981214676433564963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66033283987476450955709975 99049925981214676433564963)
    ·
      refine ⟨148574888971822014650347445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99049925981214676433564963 148574888971822014650347445)
      ·
        refine ⟨13928895841108313873470073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 148574888971822014650347445 13928895841108313873470073)
        ·
          refine ⟨10446671880831235405102555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13928895841108313873470073 10446671880831235405102555)
          ·
            refine ⟨15670007821246853107653833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10446671880831235405102555 15670007821246853107653833)
            ·
              refine ⟨11752505865935139830740375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15670007821246853107653833 11752505865935139830740375)
              ·
                refine ⟨17628758798902709746110563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11752505865935139830740375 17628758798902709746110563)
                ·
                  refine ⟨26443138198354064619165845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17628758798902709746110563 26443138198354064619165845)
                  ·
                    refine ⟨1239522103047846779023399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26443138198354064619165845 1239522103047846779023399)
                    ·
                      rfl

theorem cell23_7241882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 2, 1, 1, 6].length) (baseStart_7241882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7241882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7241882 prefixEnd_7241882 := by exact prefixLift 7241882
  have htrace : WordTrace (prefixWord ++ tailWord_7241882) baseStart_7241882 baseEnd_7241882 := by
    simpa [prefixWord, tailWord_7241882, baseEnd_7241882] using wordTrace_append hprefix tailTrace_7241882
  have hstable : (prefixWord ++ tailWord_7241882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7241882).length < 2 ^ (prefixWord ++ tailWord_7241882).sum := by decide
  have hdescent : baseEnd_7241882 < baseStart_7241882 := by decide
  rcases family_descends (prefixWord ++ tailWord_7241882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7241885 : List Nat := [1, 4, 2, 1, 1, 3, 1, 3, 1, 2, 4]
def baseStart_7241885 : Nat := 118140960795 + 7241885 * 2 ^ 59
def prefixEnd_7241885 : Nat := 4983230072969 + 3 ^ 40 * 7241885 * 2
def baseEnd_7241885 : Nat := 3718567849585503825332683

theorem tailTrace_7241885 : CollatzResearch.WordTrace tailWord_7241885 prefixEnd_7241885 3718567849585503825332683 := by
  unfold tailWord_7241885
  simp only [CollatzResearch.WordTrace]
  refine ⟨264133245368894935335199109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176088830245929956890132739 264133245368894935335199109)
  ·
    refine ⟨49524983506667800375349833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 264133245368894935335199109 49524983506667800375349833)
    ·
      refine ⟨37143737630000850281512375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49524983506667800375349833 37143737630000850281512375)
      ·
        refine ⟨55715606445001275422268563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37143737630000850281512375 55715606445001275422268563)
        ·
          refine ⟨83573409667501913133402845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55715606445001275422268563 83573409667501913133402845)
          ·
            refine ⟨31340028625313217425026067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 83573409667501913133402845 31340028625313217425026067)
            ·
              refine ⟨47010042937969826137539101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31340028625313217425026067 47010042937969826137539101)
              ·
                refine ⟨17628766101738684801577163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47010042937969826137539101 17628766101738684801577163)
                ·
                  refine ⟨26443149152608027202365745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17628766101738684801577163 26443149152608027202365745)
                  ·
                    refine ⟨19832361864456020401774309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26443149152608027202365745 19832361864456020401774309)
                    ·
                      refine ⟨3718567849585503825332683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19832361864456020401774309 3718567849585503825332683)
                      ·
                        rfl

theorem cell23_7241885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 1, 3, 1, 2, 4].length) (baseStart_7241885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7241885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7241885 prefixEnd_7241885 := by exact prefixLift 7241885
  have htrace : WordTrace (prefixWord ++ tailWord_7241885) baseStart_7241885 baseEnd_7241885 := by
    simpa [prefixWord, tailWord_7241885, baseEnd_7241885] using wordTrace_append hprefix tailTrace_7241885
  have hstable : (prefixWord ++ tailWord_7241885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7241885).length < 2 ^ (prefixWord ++ tailWord_7241885).sum := by decide
  have hdescent : baseEnd_7241885 < baseStart_7241885 := by decide
  rcases family_descends (prefixWord ++ tailWord_7241885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7241889 : List Nat := [1, 2, 3, 3, 1, 3, 1, 2, 3, 2, 2]
def baseStart_7241889 : Nat := 118140960795 + 7241889 * 2 ^ 59
def prefixEnd_7241889 : Nat := 4983230072969 + 3 ^ 40 * 7241889 * 2
def baseEnd_7241889 : Nat := 3718569903508121809682665

theorem tailTrace_7241889 : CollatzResearch.WordTrace tailWord_7241889 prefixEnd_7241889 3718569903508121809682665 := by
  unfold tailWord_7241889
  simp only [CollatzResearch.WordTrace]
  refine ⟨264133391260880444018344721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176088927507253629345563147 264133391260880444018344721)
  ·
    refine ⟨198100043445660333013758541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 264133391260880444018344721 198100043445660333013758541)
    ·
      refine ⟨74287516292122624880159453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 198100043445660333013758541 74287516292122624880159453)
      ·
        refine ⟨27857818609545984330059795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74287516292122624880159453 27857818609545984330059795)
        ·
          refine ⟨41786727914318976495089693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27857818609545984330059795 41786727914318976495089693)
          ·
            refine ⟨15670022967869616185658635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41786727914318976495089693 15670022967869616185658635)
            ·
              refine ⟨23505034451804424278487953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15670022967869616185658635 23505034451804424278487953)
              ·
                refine ⟨17628775838853318208865965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23505034451804424278487953 17628775838853318208865965)
                ·
                  refine ⟨6610790939569994328324737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17628775838853318208865965 6610790939569994328324737)
                  ·
                    refine ⟨4958093204677495746243553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6610790939569994328324737 4958093204677495746243553)
                    ·
                      refine ⟨3718569903508121809682665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4958093204677495746243553 3718569903508121809682665)
                      ·
                        rfl

theorem cell23_7241889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 1, 2, 3, 2, 2].length) (baseStart_7241889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7241889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7241889 prefixEnd_7241889 := by exact prefixLift 7241889
  have htrace : WordTrace (prefixWord ++ tailWord_7241889) baseStart_7241889 baseEnd_7241889 := by
    simpa [prefixWord, tailWord_7241889, baseEnd_7241889] using wordTrace_append hprefix tailTrace_7241889
  have hstable : (prefixWord ++ tailWord_7241889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7241889).length < 2 ^ (prefixWord ++ tailWord_7241889).sum := by decide
  have hdescent : baseEnd_7241889 < baseStart_7241889 := by decide
  rcases family_descends (prefixWord ++ tailWord_7241889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7241906 : List Nat := [3, 2, 1, 1, 1, 3, 4, 3, 1, 2, 2]
def baseStart_7241906 : Nat := 118140960795 + 7241906 * 2 ^ 59
def prefixEnd_7241906 : Nat := 4983230072969 + 3 ^ 40 * 7241906 * 2
def baseEnd_7241906 : Nat := 3718578632679248243170087

theorem tailTrace_7241906 : CollatzResearch.WordTrace tailWord_7241906 prefixEnd_7241906 3718578632679248243170087 := by
  unfold tailWord_7241906
  simp only [CollatzResearch.WordTrace]
  refine ⟨66033502825454713980428393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176089340867879237281142381 66033502825454713980428393)
  ·
    refine ⟨49525127119091035485321295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66033502825454713980428393 49525127119091035485321295)
    ·
      refine ⟨74287690678636553227981943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49525127119091035485321295 74287690678636553227981943)
      ·
        refine ⟨111431536017954829841972915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74287690678636553227981943 111431536017954829841972915)
        ·
          refine ⟨167147304026932244762959373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111431536017954829841972915 167147304026932244762959373)
          ·
            refine ⟨62680239010099591786109765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 167147304026932244762959373 62680239010099591786109765)
            ·
              refine ⟨11752544814393673459895581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 62680239010099591786109765 11752544814393673459895581)
              ·
                refine ⟨4407204305397627547460843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11752544814393673459895581 4407204305397627547460843)
                ·
                  refine ⟨6610806458096441321191265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4407204305397627547460843 6610806458096441321191265)
                  ·
                    refine ⟨4958104843572330990893449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6610806458096441321191265 4958104843572330990893449)
                    ·
                      refine ⟨3718578632679248243170087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4958104843572330990893449 3718578632679248243170087)
                      ·
                        rfl

theorem cell23_7241906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 4, 3, 1, 2, 2].length) (baseStart_7241906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7241906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7241906 prefixEnd_7241906 := by exact prefixLift 7241906
  have htrace : WordTrace (prefixWord ++ tailWord_7241906) baseStart_7241906 baseEnd_7241906 := by
    simpa [prefixWord, tailWord_7241906, baseEnd_7241906] using wordTrace_append hprefix tailTrace_7241906
  have hstable : (prefixWord ++ tailWord_7241906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7241906).length < 2 ^ (prefixWord ++ tailWord_7241906).sum := by decide
  have hdescent : baseEnd_7241906 < baseStart_7241906 := by decide
  rcases family_descends (prefixWord ++ tailWord_7241906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7241916 : List Nat := [2, 2, 2, 3, 4, 1, 1, 2, 2, 4]
def baseStart_7241916 : Nat := 118140960795 + 7241916 * 2 ^ 59
def prefixEnd_7241916 : Nat := 4983230072969 + 3 ^ 40 * 7241916 * 2
def baseEnd_7241916 : Nat := 1239527922495264401348347

theorem tailTrace_7241916 : CollatzResearch.WordTrace tailWord_7241916 prefixEnd_7241916 1239527922495264401348347 := by
  unfold tailWord_7241916
  simp only [CollatzResearch.WordTrace]
  refine ⟨132067188015891313814788801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176089584021188418419718401 132067188015891313814788801)
  ·
    refine ⟨99050391011918485361091601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132067188015891313814788801 99050391011918485361091601)
    ·
      refine ⟨74287793258938864020818701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99050391011918485361091601 74287793258938864020818701)
      ·
        refine ⟨27857922472102074007807013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74287793258938864020818701 27857922472102074007807013)
        ·
          refine ⟨5223360463519138876463815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27857922472102074007807013 5223360463519138876463815)
          ·
            refine ⟨7835040695278708314695723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5223360463519138876463815 7835040695278708314695723)
            ·
              refine ⟨11752561042918062472043585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7835040695278708314695723 11752561042918062472043585)
              ·
                refine ⟨8814420782188546854032689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11752561042918062472043585 8814420782188546854032689)
                ·
                  refine ⟨6610815586641410140524517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8814420782188546854032689 6610815586641410140524517)
                  ·
                    refine ⟨1239527922495264401348347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6610815586641410140524517 1239527922495264401348347)
                    ·
                      rfl

theorem cell23_7241916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 4, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 4, 1, 1, 2, 2, 4].length) (baseStart_7241916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7241916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7241916 prefixEnd_7241916 := by exact prefixLift 7241916
  have htrace : WordTrace (prefixWord ++ tailWord_7241916) baseStart_7241916 baseEnd_7241916 := by
    simpa [prefixWord, tailWord_7241916, baseEnd_7241916] using wordTrace_append hprefix tailTrace_7241916
  have hstable : (prefixWord ++ tailWord_7241916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7241916).length < 2 ^ (prefixWord ++ tailWord_7241916).sum := by decide
  have hdescent : baseEnd_7241916 < baseStart_7241916 := by decide
  rcases family_descends (prefixWord ++ tailWord_7241916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7241962 : List Nat := [3, 1, 3, 1, 1, 2, 2, 1, 3, 4, 2]
def baseStart_7241962 : Nat := 118140960795 + 7241962 * 2 ^ 59
def prefixEnd_7241962 : Nat := 4983230072969 + 3 ^ 40 * 7241962 * 2
def baseEnd_7241962 : Nat := 3718607387595900024069829

theorem tailTrace_7241962 : CollatzResearch.WordTrace tailWord_7241962 prefixEnd_7241962 3718607387595900024069829 := by
  unfold tailWord_7241962
  simp only [CollatzResearch.WordTrace]
  refine ⟨66034013447403994371438035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176090702526410651657168093 66034013447403994371438035)
  ·
    refine ⟨99051020171105991557157053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66034013447403994371438035 99051020171105991557157053)
    ·
      refine ⟨37144132564164746833933895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99051020171105991557157053 37144132564164746833933895)
      ·
        refine ⟨55716198846247120250900843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37144132564164746833933895 55716198846247120250900843)
        ·
          refine ⟨83574298269370680376351265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55716198846247120250900843 83574298269370680376351265)
          ·
            refine ⟨62680723702028010282263449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83574298269370680376351265 62680723702028010282263449)
            ·
              refine ⟨47010542776521007711697587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62680723702028010282263449 47010542776521007711697587)
              ·
                refine ⟨70515814164781511567546381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47010542776521007711697587 70515814164781511567546381)
                ·
                  refine ⟨26443430311793066837829893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 70515814164781511567546381 26443430311793066837829893)
                  ·
                    refine ⟨4958143183461200032093105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26443430311793066837829893 4958143183461200032093105)
                    ·
                      refine ⟨3718607387595900024069829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4958143183461200032093105 3718607387595900024069829)
                      ·
                        rfl

theorem cell23_7241962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 2, 1, 3, 4, 2].length) (baseStart_7241962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7241962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7241962 prefixEnd_7241962 := by exact prefixLift 7241962
  have htrace : WordTrace (prefixWord ++ tailWord_7241962) baseStart_7241962 baseEnd_7241962 := by
    simpa [prefixWord, tailWord_7241962, baseEnd_7241962] using wordTrace_append hprefix tailTrace_7241962
  have hstable : (prefixWord ++ tailWord_7241962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7241962).length < 2 ^ (prefixWord ++ tailWord_7241962).sum := by decide
  have hdescent : baseEnd_7241962 < baseStart_7241962 := by decide
  rcases family_descends (prefixWord ++ tailWord_7241962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7241968 : List Nat := [2, 1, 1, 1, 3, 1, 1, 4, 9]
def baseStart_7241968 : Nat := 118140960795 + 7241968 * 2 ^ 59
def prefixEnd_7241968 : Nat := 4983230072969 + 3 ^ 40 * 7241968 * 2
def baseEnd_7241968 : Nat := 413178940942203000066089

theorem tailTrace_7241968 : CollatzResearch.WordTrace tailWord_7241968 prefixEnd_7241968 413178940942203000066089 := by
  unfold tailWord_7241968
  simp only [CollatzResearch.WordTrace]
  refine ⟨132068136313797120255235279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176090848418396160340313705 132068136313797120255235279)
  ·
    refine ⟨198102204470695680382852919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132068136313797120255235279 198102204470695680382852919)
    ·
      refine ⟨297153306706043520574279379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198102204470695680382852919 297153306706043520574279379)
      ·
        refine ⟨445729960059065280861419069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 297153306706043520574279379 445729960059065280861419069)
        ·
          refine ⟨167148735022149480323032151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 445729960059065280861419069 167148735022149480323032151)
          ·
            refine ⟨250723102533224220484548227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 167148735022149480323032151 250723102533224220484548227)
            ·
              refine ⟨376084653799836330726822341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 250723102533224220484548227 376084653799836330726822341)
              ·
                refine ⟨70515872587469312011279189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 376084653799836330726822341 70515872587469312011279189)
                ·
                  refine ⟨413178940942203000066089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 70515872587469312011279189 413178940942203000066089)
                  ·
                    rfl

theorem cell23_7241968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 4, 9].length) (baseStart_7241968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7241968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7241968 prefixEnd_7241968 := by exact prefixLift 7241968
  have htrace : WordTrace (prefixWord ++ tailWord_7241968) baseStart_7241968 baseEnd_7241968 := by
    simpa [prefixWord, tailWord_7241968, baseEnd_7241968] using wordTrace_append hprefix tailTrace_7241968
  have hstable : (prefixWord ++ tailWord_7241968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7241968).length < 2 ^ (prefixWord ++ tailWord_7241968).sum := by decide
  have hdescent : baseEnd_7241968 < baseStart_7241968 := by decide
  rcases family_descends (prefixWord ++ tailWord_7241968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7241982 : List Nat := [4, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3]
def baseStart_7241982 : Nat := 118140960795 + 7241982 * 2 ^ 59
def prefixEnd_7241982 : Nat := 4983230072969 + 3 ^ 40 * 7241982 * 2
def baseEnd_7241982 : Nat := 3718617657208989945819737

theorem tailTrace_7241982 : CollatzResearch.WordTrace tailWord_7241982 prefixEnd_7241982 3718617657208989945819737 := by
  unfold tailWord_7241982
  simp only [CollatzResearch.WordTrace]
  refine ⟨33017097906192940112685025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 176091188833029013934320133 33017097906192940112685025)
  ·
    refine ⟨24762823429644705084513769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33017097906192940112685025 24762823429644705084513769)
    ·
      refine ⟨18572117572233528813385327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24762823429644705084513769 18572117572233528813385327)
      ·
        refine ⟨27858176358350293220077991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18572117572233528813385327 27858176358350293220077991)
        ·
          refine ⟨41787264537525439830116987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27858176358350293220077991 41787264537525439830116987)
          ·
            refine ⟨62680896806288159745175481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41787264537525439830116987 62680896806288159745175481)
            ·
              refine ⟨47010672604716119808881611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62680896806288159745175481 47010672604716119808881611)
              ·
                refine ⟨70516008907074179713322417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47010672604716119808881611 70516008907074179713322417)
                ·
                  refine ⟨52887006680305634784991813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 70516008907074179713322417 52887006680305634784991813)
                  ·
                    refine ⟨9916313752557306522185965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 52887006680305634784991813 9916313752557306522185965)
                    ·
                      refine ⟨3718617657208989945819737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9916313752557306522185965 3718617657208989945819737)
                      ·
                        rfl

theorem cell23_7241982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3].length) (baseStart_7241982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7241982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7241982 prefixEnd_7241982 := by exact prefixLift 7241982
  have htrace : WordTrace (prefixWord ++ tailWord_7241982) baseStart_7241982 baseEnd_7241982 := by
    simpa [prefixWord, tailWord_7241982, baseEnd_7241982] using wordTrace_append hprefix tailTrace_7241982
  have hstable : (prefixWord ++ tailWord_7241982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7241982).length < 2 ^ (prefixWord ++ tailWord_7241982).sum := by decide
  have hdescent : baseEnd_7241982 < baseStart_7241982 := by decide
  rcases family_descends (prefixWord ++ tailWord_7241982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7241995 : List Nat := [1, 1, 1, 1, 5, 2, 2, 1, 1, 5, 3]
def baseStart_7241995 : Nat := 118140960795 + 7241995 * 2 ^ 59
def prefixEnd_7241995 : Nat := 4983230072969 + 3 ^ 40 * 7241995 * 2
def baseEnd_7241995 : Nat := 3718624332457498394957177

theorem tailTrace_7241995 : CollatzResearch.WordTrace tailWord_7241995 prefixEnd_7241995 3718624332457498394957177 := by
  unfold tailWord_7241995
  simp only [CollatzResearch.WordTrace]
  refine ⟨264137257398496424121703439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176091504932330949414468959 264137257398496424121703439)
  ·
    refine ⟨396205886097744636182555159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264137257398496424121703439 396205886097744636182555159)
    ·
      refine ⟨594308829146616954273832739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 396205886097744636182555159 594308829146616954273832739)
      ·
        refine ⟨891463243719925431410749109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 594308829146616954273832739 891463243719925431410749109)
        ·
          refine ⟨83574679098743009194757729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 891463243719925431410749109 83574679098743009194757729)
          ·
            refine ⟨62681009324057256896068297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83574679098743009194757729 62681009324057256896068297)
            ·
              refine ⟨47010756993042942672051223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62681009324057256896068297 47010756993042942672051223)
              ·
                refine ⟨70516135489564414008076835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47010756993042942672051223 70516135489564414008076835)
                ·
                  refine ⟨105774203234346621012115253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70516135489564414008076835 105774203234346621012115253)
                  ·
                    refine ⟨9916331553219995719885805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 105774203234346621012115253 9916331553219995719885805)
                    ·
                      refine ⟨3718624332457498394957177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9916331553219995719885805 3718624332457498394957177)
                      ·
                        rfl

theorem cell23_7241995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 2, 1, 1, 5, 3].length) (baseStart_7241995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7241995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7241995 prefixEnd_7241995 := by exact prefixLift 7241995
  have htrace : WordTrace (prefixWord ++ tailWord_7241995) baseStart_7241995 baseEnd_7241995 := by
    simpa [prefixWord, tailWord_7241995, baseEnd_7241995] using wordTrace_append hprefix tailTrace_7241995
  have hstable : (prefixWord ++ tailWord_7241995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7241995).length < 2 ^ (prefixWord ++ tailWord_7241995).sum := by decide
  have hdescent : baseEnd_7241995 < baseStart_7241995 := by decide
  rcases family_descends (prefixWord ++ tailWord_7241995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7242030 : List Nat := [4, 1, 3, 3, 1, 1, 2, 2, 2, 2, 2]
def baseStart_7242030 : Nat := 118140960795 + 7242030 * 2 ^ 59
def prefixEnd_7242030 : Nat := 4983230072969 + 3 ^ 40 * 7242030 * 2
def baseEnd_7242030 : Nat := 3718642304280405758019517

theorem tailTrace_7242030 : CollatzResearch.WordTrace tailWord_7242030 prefixEnd_7242030 3718642304280405758019517 := by
  unfold tailWord_7242030
  simp only [CollatzResearch.WordTrace]
  refine ⟨33017316744171203137403443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 176092355968913083399485029 33017316744171203137403443)
  ·
    refine ⟨49525975116256804706105165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33017316744171203137403443 49525975116256804706105165)
    ·
      refine ⟨18572240668596301764789437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49525975116256804706105165 18572240668596301764789437)
      ·
        refine ⟨6964590250723613161796039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18572240668596301764789437 6964590250723613161796039)
        ·
          refine ⟨10446885376085419742694059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6964590250723613161796039 10446885376085419742694059)
          ·
            refine ⟨15670328064128129614041089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10446885376085419742694059 15670328064128129614041089)
            ·
              refine ⟨11752746048096097210530817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15670328064128129614041089 11752746048096097210530817)
              ·
                refine ⟨8814559536072072907898113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11752746048096097210530817 8814559536072072907898113)
                ·
                  refine ⟨6610919652054054680923585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8814559536072072907898113 6610919652054054680923585)
                  ·
                    refine ⟨4958189739040541010692689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6610919652054054680923585 4958189739040541010692689)
                    ·
                      refine ⟨3718642304280405758019517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4958189739040541010692689 3718642304280405758019517)
                      ·
                        rfl

theorem cell23_7242030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 2, 2, 2, 2, 2].length) (baseStart_7242030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7242030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7242030 prefixEnd_7242030 := by exact prefixLift 7242030
  have htrace : WordTrace (prefixWord ++ tailWord_7242030) baseStart_7242030 baseEnd_7242030 := by
    simpa [prefixWord, tailWord_7242030, baseEnd_7242030] using wordTrace_append hprefix tailTrace_7242030
  have hstable : (prefixWord ++ tailWord_7242030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7242030).length < 2 ^ (prefixWord ++ tailWord_7242030).sum := by decide
  have hdescent : baseEnd_7242030 < baseStart_7242030 := by decide
  rcases family_descends (prefixWord ++ tailWord_7242030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7242036 : List Nat := [2, 5, 1, 1, 1, 2, 4, 2, 5]
def baseStart_7242036 : Nat := 118140960795 + 7242036 * 2 ^ 59
def prefixEnd_7242036 : Nat := 4983230072969 + 3 ^ 40 * 7242036 * 2
def baseEnd_7242036 : Nat := 413182820573814748282721

theorem tailTrace_7242036 : CollatzResearch.WordTrace tailWord_7242036 prefixEnd_7242036 413182820573814748282721 := by
  unfold tailWord_7242036
  simp only [CollatzResearch.WordTrace]
  refine ⟨132069376395673944061972981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176092501860898592082630641 132069376395673944061972981)
  ·
    refine ⟨12381504037094432255809967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 132069376395673944061972981 12381504037094432255809967)
    ·
      refine ⟨18572256055641648383714951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12381504037094432255809967 18572256055641648383714951)
      ·
        refine ⟨27858384083462472575572427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18572256055641648383714951 27858384083462472575572427)
        ·
          refine ⟨41787576125193708863358641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27858384083462472575572427 41787576125193708863358641)
          ·
            refine ⟨31340682093895281647518981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41787576125193708863358641 31340682093895281647518981)
            ·
              refine ⟨5876377892605365308909809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31340682093895281647518981 5876377892605365308909809)
              ·
                refine ⟨4407283419454023981682357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5876377892605365308909809 4407283419454023981682357)
                ·
                  refine ⟨413182820573814748282721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4407283419454023981682357 413182820573814748282721)
                  ·
                    rfl

theorem cell23_7242036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 4, 2, 5].length) (baseStart_7242036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7242036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7242036 prefixEnd_7242036 := by exact prefixLift 7242036
  have htrace : WordTrace (prefixWord ++ tailWord_7242036) baseStart_7242036 baseEnd_7242036 := by
    simpa [prefixWord, tailWord_7242036, baseEnd_7242036] using wordTrace_append hprefix tailTrace_7242036
  have hstable : (prefixWord ++ tailWord_7242036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7242036).length < 2 ^ (prefixWord ++ tailWord_7242036).sum := by decide
  have hdescent : baseEnd_7242036 < baseStart_7242036 := by decide
  rcases family_descends (prefixWord ++ tailWord_7242036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7242072 : List Nat := [2, 1, 2, 2, 1, 1, 2, 5, 2, 2, 3]
def baseStart_7242072 : Nat := 118140960795 + 7242072 * 2 ^ 59
def prefixEnd_7242072 : Nat := 4983230072969 + 3 ^ 40 * 7242072 * 2
def baseEnd_7242072 : Nat := 3718663870467894593694323

theorem tailTrace_7242072 : CollatzResearch.WordTrace tailWord_7242072 prefixEnd_7242072 3718663870467894593694323 := by
  unfold tailWord_7242072
  simp only [CollatzResearch.WordTrace]
  refine ⟨132070032909608733136128235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176093377212811644181504313 132070032909608733136128235)
  ·
    refine ⟨198105049364413099704192353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132070032909608733136128235 198105049364413099704192353)
    ·
      refine ⟨148578787023309824778144265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 198105049364413099704192353 148578787023309824778144265)
      ·
        refine ⟨111434090267482368583608199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148578787023309824778144265 111434090267482368583608199)
        ·
          refine ⟨167151135401223552875412299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111434090267482368583608199 167151135401223552875412299)
          ·
            refine ⟨250726703101835329313118449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 167151135401223552875412299 250726703101835329313118449)
            ·
              refine ⟨188045027326376496984838837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 250726703101835329313118449 188045027326376496984838837)
              ·
                refine ⟨17629221311847796592328641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 188045027326376496984838837 17629221311847796592328641)
                ·
                  refine ⟨13221915983885847444246481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17629221311847796592328641 13221915983885847444246481)
                  ·
                    refine ⟨9916436987914385583184861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13221915983885847444246481 9916436987914385583184861)
                    ·
                      refine ⟨3718663870467894593694323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9916436987914385583184861 3718663870467894593694323)
                      ·
                        rfl

theorem cell23_7242072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 5, 2, 2, 3].length) (baseStart_7242072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7242072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7242072 prefixEnd_7242072 := by exact prefixLift 7242072
  have htrace : WordTrace (prefixWord ++ tailWord_7242072) baseStart_7242072 baseEnd_7242072 := by
    simpa [prefixWord, tailWord_7242072, baseEnd_7242072] using wordTrace_append hprefix tailTrace_7242072
  have hstable : (prefixWord ++ tailWord_7242072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7242072).length < 2 ^ (prefixWord ++ tailWord_7242072).sum := by decide
  have hdescent : baseEnd_7242072 < baseStart_7242072 := by decide
  rcases family_descends (prefixWord ++ tailWord_7242072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7242079 : List Nat := [1, 1, 2, 3, 1, 2, 3, 5, 1, 4]
def baseStart_7242079 : Nat := 118140960795 + 7242079 * 2 ^ 59
def prefixEnd_7242079 : Nat := 4983230072969 + 3 ^ 40 * 7242079 * 2
def baseEnd_7242079 : Nat := 1239555821610825355435597

theorem tailTrace_7242079 : CollatzResearch.WordTrace tailWord_7242079 prefixEnd_7242079 1239555821610825355435597 := by
  unfold tailWord_7242079
  simp only [CollatzResearch.WordTrace]
  refine ⟨264140321130192106467761291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176093547420128070978507527 264140321130192106467761291)
  ·
    refine ⟨396210481695288159701641937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264140321130192106467761291 396210481695288159701641937)
    ·
      refine ⟨297157861271466119776231453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 396210481695288159701641937 297157861271466119776231453)
      ·
        refine ⟨111434197976799794916086795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 297157861271466119776231453 111434197976799794916086795)
        ·
          refine ⟨167151296965199692374130193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111434197976799794916086795 167151296965199692374130193)
          ·
            refine ⟨125363472723899769280597645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 167151296965199692374130193 125363472723899769280597645)
            ·
              refine ⟨47011302271462413480224117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 125363472723899769280597645 47011302271462413480224117)
              ·
                refine ⟨4407309587949601263771011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 47011302271462413480224117 4407309587949601263771011)
                ·
                  refine ⟨6610964381924401895656517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4407309587949601263771011 6610964381924401895656517)
                  ·
                    refine ⟨1239555821610825355435597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6610964381924401895656517 1239555821610825355435597)
                    ·
                      rfl

theorem cell23_7242079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 3, 5, 1, 4].length) (baseStart_7242079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7242079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7242079 prefixEnd_7242079 := by exact prefixLift 7242079
  have htrace : WordTrace (prefixWord ++ tailWord_7242079) baseStart_7242079 baseEnd_7242079 := by
    simpa [prefixWord, tailWord_7242079, baseEnd_7242079] using wordTrace_append hprefix tailTrace_7242079
  have hstable : (prefixWord ++ tailWord_7242079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7242079).length < 2 ^ (prefixWord ++ tailWord_7242079).sum := by decide
  have hdescent : baseEnd_7242079 < baseStart_7242079 := by decide
  rcases family_descends (prefixWord ++ tailWord_7242079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7242082 : List Nat := [3, 3, 2, 1, 1, 2, 1, 1, 2, 1, 6]
def baseStart_7242082 : Nat := 118140960795 + 7242082 * 2 ^ 59
def prefixEnd_7242082 : Nat := 4983230072969 + 3 ^ 40 * 7242082 * 2
def baseEnd_7242082 : Nat := 3718669005274439554569277

theorem tailTrace_7242082 : CollatzResearch.WordTrace tailWord_7242082 prefixEnd_7242082 3718669005274439554569277 := by
  unfold tailWord_7242082
  simp only [CollatzResearch.WordTrace]
  refine ⟨66035107637295309495030125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176093620366120825320080333 66035107637295309495030125)
  ·
    refine ⟨24763165363985741060636297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66035107637295309495030125 24763165363985741060636297)
    ·
      refine ⟨18572374022989305795477223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24763165363985741060636297 18572374022989305795477223)
      ·
        refine ⟨27858561034483958693215835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18572374022989305795477223 27858561034483958693215835)
        ·
          refine ⟨41787841551725938039823753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27858561034483958693215835 41787841551725938039823753)
          ·
            refine ⟨31340881163794453529867815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41787841551725938039823753 31340881163794453529867815)
            ·
              refine ⟨47011321745691680294801723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31340881163794453529867815 47011321745691680294801723)
              ·
                refine ⟨70516982618537520442202585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47011321745691680294801723 70516982618537520442202585)
                ·
                  refine ⟨52887736963903140331651939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 70516982618537520442202585 52887736963903140331651939)
                  ·
                    refine ⟨79331605445854710497477909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 52887736963903140331651939 79331605445854710497477909)
                    ·
                      refine ⟨3718669005274439554569277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 79331605445854710497477909 3718669005274439554569277)
                      ·
                        rfl

theorem cell23_7242082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 1, 1, 2, 1, 6].length) (baseStart_7242082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7242082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7242082 prefixEnd_7242082 := by exact prefixLift 7242082
  have htrace : WordTrace (prefixWord ++ tailWord_7242082) baseStart_7242082 baseEnd_7242082 := by
    simpa [prefixWord, tailWord_7242082, baseEnd_7242082] using wordTrace_append hprefix tailTrace_7242082
  have hstable : (prefixWord ++ tailWord_7242082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7242082).length < 2 ^ (prefixWord ++ tailWord_7242082).sum := by decide
  have hdescent : baseEnd_7242082 < baseStart_7242082 := by decide
  rcases family_descends (prefixWord ++ tailWord_7242082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7242092 : List Nat := [2, 2, 1, 1, 6, 1, 1, 1, 8]
def baseStart_7242092 : Nat := 118140960795 + 7242092 * 2 ^ 59
def prefixEnd_7242092 : Nat := 4983230072969 + 3 ^ 40 * 7242092 * 2
def baseEnd_7242092 : Nat := 413186015564553835049359

theorem tailTrace_7242092 : CollatzResearch.WordTrace tailWord_7242092 prefixEnd_7242092 413186015564553835049359 := by
  unfold tailWord_7242092
  simp only [CollatzResearch.WordTrace]
  refine ⟨132070397639572504843992265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176093863519430006458656353 132070397639572504843992265)
  ·
    refine ⟨99052798229679378632994199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132070397639572504843992265 99052798229679378632994199)
    ·
      refine ⟨148579197344519067949491299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99052798229679378632994199 148579197344519067949491299)
      ·
        refine ⟨222868796016778601924236949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148579197344519067949491299 222868796016778601924236949)
        ·
          refine ⟨10446974813286496965198607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 222868796016778601924236949 10446974813286496965198607)
          ·
            refine ⟨15670462219929745447797911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10446974813286496965198607 15670462219929745447797911)
            ·
              refine ⟨23505693329894618171696867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15670462219929745447797911 23505693329894618171696867)
              ·
                refine ⟨35258539994841927257545301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23505693329894618171696867 35258539994841927257545301)
                ·
                  refine ⟨413186015564553835049359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 35258539994841927257545301 413186015564553835049359)
                  ·
                    rfl

theorem cell23_7242092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 8].length) (baseStart_7242092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7242092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7242092 prefixEnd_7242092 := by exact prefixLift 7242092
  have htrace : WordTrace (prefixWord ++ tailWord_7242092) baseStart_7242092 baseEnd_7242092 := by
    simpa [prefixWord, tailWord_7242092, baseEnd_7242092] using wordTrace_append hprefix tailTrace_7242092
  have hstable : (prefixWord ++ tailWord_7242092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7242092).length < 2 ^ (prefixWord ++ tailWord_7242092).sum := by decide
  have hdescent : baseEnd_7242092 < baseStart_7242092 := by decide
  rcases family_descends (prefixWord ++ tailWord_7242092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7242109 : List Nat := [1, 4, 1, 1, 2, 4, 3, 1, 6]
def baseStart_7242109 : Nat := 118140960795 + 7242109 * 2 ^ 59
def prefixEnd_7242109 : Nat := 4983230072969 + 3 ^ 40 * 7242109 * 2
def baseEnd_7242109 : Nat := 413186985472456772103517

theorem tailTrace_7242109 : CollatzResearch.WordTrace tailWord_7242109 prefixEnd_7242109 413186985472456772103517 := by
  unfold tailWord_7242109
  simp only [CollatzResearch.WordTrace]
  refine ⟨264141415320083421591353381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176094276880055614394235587 264141415320083421591353381)
  ·
    refine ⟨49526515372515641548378759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 264141415320083421591353381 49526515372515641548378759)
    ·
      refine ⟨74289773058773462322568139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49526515372515641548378759 74289773058773462322568139)
      ·
        refine ⟨111434659588160193483852209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74289773058773462322568139 111434659588160193483852209)
        ·
          refine ⟨83575994691120145112889157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111434659588160193483852209 83575994691120145112889157)
          ·
            refine ⟨15670499004585027208666717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 83575994691120145112889157 15670499004585027208666717)
            ·
              refine ⟨5876437126719385203250019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15670499004585027208666717 5876437126719385203250019)
              ·
                refine ⟨8814655690079077804875029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5876437126719385203250019 8814655690079077804875029)
                ·
                  refine ⟨413186985472456772103517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8814655690079077804875029 413186985472456772103517)
                  ·
                    rfl

theorem cell23_7242109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 3, 1, 6].length) (baseStart_7242109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7242109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7242109 prefixEnd_7242109 := by exact prefixLift 7242109
  have htrace : WordTrace (prefixWord ++ tailWord_7242109) baseStart_7242109 baseEnd_7242109 := by
    simpa [prefixWord, tailWord_7242109, baseEnd_7242109] using wordTrace_append hprefix tailTrace_7242109
  have hstable : (prefixWord ++ tailWord_7242109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7242109).length < 2 ^ (prefixWord ++ tailWord_7242109).sum := by decide
  have hdescent : baseEnd_7242109 < baseStart_7242109 := by decide
  rcases family_descends (prefixWord ++ tailWord_7242109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7242119 : List Nat := [1, 1, 4, 2, 2, 1, 1, 4, 3, 1, 3]
def baseStart_7242119 : Nat := 118140960795 + 7242119 * 2 ^ 59
def prefixEnd_7242119 : Nat := 4983230072969 + 3 ^ 40 * 7242119 * 2
def baseEnd_7242119 : Nat := 3718688004058655909806607

theorem tailTrace_7242119 : CollatzResearch.WordTrace tailWord_7242119 prefixEnd_7242119 3718688004058655909806607 := by
  unfold tailWord_7242119
  simp only [CollatzResearch.WordTrace]
  refine ⟨264141780050047193299217411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176094520033364795532811607 264141780050047193299217411)
  ·
    refine ⟨396212670075070789948826117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264141780050047193299217411 396212670075070789948826117)
    ·
      refine ⟨74289875639075773115404897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 396212670075070789948826117 74289875639075773115404897)
      ·
        refine ⟨55717406729306829836553673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74289875639075773115404897 55717406729306829836553673)
        ·
          refine ⟨41788055046980122377415255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55717406729306829836553673 41788055046980122377415255)
          ·
            refine ⟨62682082570470183566122883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41788055046980122377415255 62682082570470183566122883)
            ·
              refine ⟨94023123855705275349184325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62682082570470183566122883 94023123855705275349184325)
              ·
                refine ⟨17629335722944739127972061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 94023123855705275349184325 17629335722944739127972061)
                ·
                  refine ⟨6611000896104277172989523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17629335722944739127972061 6611000896104277172989523)
                  ·
                    refine ⟨9916501344156415759484285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6611000896104277172989523 9916501344156415759484285)
                    ·
                      refine ⟨3718688004058655909806607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9916501344156415759484285 3718688004058655909806607)
                      ·
                        rfl

theorem cell23_7242119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 4, 3, 1, 3].length) (baseStart_7242119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7242119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7242119 prefixEnd_7242119 := by exact prefixLift 7242119
  have htrace : WordTrace (prefixWord ++ tailWord_7242119) baseStart_7242119 baseEnd_7242119 := by
    simpa [prefixWord, tailWord_7242119, baseEnd_7242119] using wordTrace_append hprefix tailTrace_7242119
  have hstable : (prefixWord ++ tailWord_7242119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7242119).length < 2 ^ (prefixWord ++ tailWord_7242119).sum := by decide
  have hdescent : baseEnd_7242119 < baseStart_7242119 := by decide
  rcases family_descends (prefixWord ++ tailWord_7242119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7242146 : List Nat := [3, 3, 1, 2, 1, 1, 3, 2, 2, 3, 2]
def baseStart_7242146 : Nat := 118140960795 + 7242146 * 2 ^ 59
def prefixEnd_7242146 : Nat := 4983230072969 + 3 ^ 40 * 7242146 * 2
def baseEnd_7242146 : Nat := 3718701868036327304168983

theorem tailTrace_7242146 : CollatzResearch.WordTrace tailWord_7242146 prefixEnd_7242146 3718701868036327304168983 := by
  unfold tailWord_7242146
  simp only [CollatzResearch.WordTrace]
  refine ⟨66035691205237344227612573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176095176547299584606966861 66035691205237344227612573)
  ·
    refine ⟨24763384201964004085354715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66035691205237344227612573 24763384201964004085354715)
    ·
      refine ⟨37145076302946006128032073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24763384201964004085354715 37145076302946006128032073)
      ·
        refine ⟨27858807227209504596024055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37145076302946006128032073 27858807227209504596024055)
        ·
          refine ⟨41788210840814256894036083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27858807227209504596024055 41788210840814256894036083)
          ·
            refine ⟨62682316261221385341054125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41788210840814256894036083 62682316261221385341054125)
            ·
              refine ⟨23505868597958019502895297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62682316261221385341054125 23505868597958019502895297)
              ·
                refine ⟨17629401448468514627171473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23505868597958019502895297 17629401448468514627171473)
                ·
                  refine ⟨13222051086351385970378605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17629401448468514627171473 13222051086351385970378605)
                  ·
                    refine ⟨4958269157381769738891977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13222051086351385970378605 4958269157381769738891977)
                    ·
                      refine ⟨3718701868036327304168983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4958269157381769738891977 3718701868036327304168983)
                      ·
                        rfl

theorem cell23_7242146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 3, 2, 2, 3, 2].length) (baseStart_7242146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7242146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7242146 prefixEnd_7242146 := by exact prefixLift 7242146
  have htrace : WordTrace (prefixWord ++ tailWord_7242146) baseStart_7242146 baseEnd_7242146 := by
    simpa [prefixWord, tailWord_7242146, baseEnd_7242146] using wordTrace_append hprefix tailTrace_7242146
  have hstable : (prefixWord ++ tailWord_7242146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7242146).length < 2 ^ (prefixWord ++ tailWord_7242146).sum := by decide
  have hdescent : baseEnd_7242146 < baseStart_7242146 := by decide
  rcases family_descends (prefixWord ++ tailWord_7242146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7242162 : List Nat := [3, 2, 1, 1, 1, 1, 3, 4, 1, 1, 5]
def baseStart_7242162 : Nat := 118140960795 + 7242162 * 2 ^ 59
def prefixEnd_7242162 : Nat := 4983230072969 + 3 ^ 40 * 7242162 * 2
def baseEnd_7242162 : Nat := 3718710083726799241568909

theorem tailTrace_7242162 : CollatzResearch.WordTrace tailWord_7242162 prefixEnd_7242162 3718710083726799241568909 := by
  unfold tailWord_7242162
  simp only [CollatzResearch.WordTrace]
  refine ⟨66035837097222852910758185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176095565592594274428688493 66035837097222852910758185)
  ·
    refine ⟨49526877822917139683068639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66035837097222852910758185 49526877822917139683068639)
    ·
      refine ⟨74290316734375709524602959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49526877822917139683068639 74290316734375709524602959)
      ·
        refine ⟨111435475101563564286904439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74290316734375709524602959 111435475101563564286904439)
        ·
          refine ⟨167153212652345346430356659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111435475101563564286904439 167153212652345346430356659)
          ·
            refine ⟨250729818978518019645534989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 167153212652345346430356659 250729818978518019645534989)
            ·
              refine ⟨94023682116944257367075621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 250729818978518019645534989 94023682116944257367075621)
              ·
                refine ⟨17629440396927048256326679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 94023682116944257367075621 17629440396927048256326679)
                ·
                  refine ⟨26444160595390572384490019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17629440396927048256326679 26444160595390572384490019)
                  ·
                    refine ⟨39666240893085858576735029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26444160595390572384490019 39666240893085858576735029)
                    ·
                      refine ⟨3718710083726799241568909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39666240893085858576735029 3718710083726799241568909)
                      ·
                        rfl

theorem cell23_7242162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 4, 1, 1, 5].length) (baseStart_7242162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7242162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7242162 prefixEnd_7242162 := by exact prefixLift 7242162
  have htrace : WordTrace (prefixWord ++ tailWord_7242162) baseStart_7242162 baseEnd_7242162 := by
    simpa [prefixWord, tailWord_7242162, baseEnd_7242162] using wordTrace_append hprefix tailTrace_7242162
  have hstable : (prefixWord ++ tailWord_7242162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7242162).length < 2 ^ (prefixWord ++ tailWord_7242162).sum := by decide
  have hdescent : baseEnd_7242162 < baseStart_7242162 := by decide
  rcases family_descends (prefixWord ++ tailWord_7242162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7242196 : List Nat := [2, 4, 1, 2, 2, 3, 1, 1, 1, 1, 5]
def baseStart_7242196 : Nat := 118140960795 + 7242196 * 2 ^ 59
def prefixEnd_7242196 : Nat := 4983230072969 + 3 ^ 40 * 7242196 * 2
def baseEnd_7242196 : Nat := 3718727542069052108543753

theorem tailTrace_7242196 : CollatzResearch.WordTrace tailWord_7242196 prefixEnd_7242196 3718727542069052108543753 := by
  unfold tailWord_7242196
  simp only [CollatzResearch.WordTrace]
  refine ⟨132072294235384117724885221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176096392313845490299846961 132072294235384117724885221)
  ·
    refine ⟨24763555169134522073415979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 132072294235384117724885221 24763555169134522073415979)
    ·
      refine ⟨37145332753701783110123969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24763555169134522073415979 37145332753701783110123969)
      ·
        refine ⟨27858999565276337332592977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37145332753701783110123969 27858999565276337332592977)
        ·
          refine ⟨20894249673957252999444733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27858999565276337332592977 20894249673957252999444733)
          ·
            refine ⟨7835343627733969874791775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20894249673957252999444733 7835343627733969874791775)
            ·
              refine ⟨11753015441600954812187663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7835343627733969874791775 11753015441600954812187663)
              ·
                refine ⟨17629523162401432218281495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11753015441600954812187663 17629523162401432218281495)
                ·
                  refine ⟨26444284743602148327422243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17629523162401432218281495 26444284743602148327422243)
                  ·
                    refine ⟨39666427115403222491133365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26444284743602148327422243 39666427115403222491133365)
                    ·
                      refine ⟨3718727542069052108543753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39666427115403222491133365 3718727542069052108543753)
                      ·
                        rfl

theorem cell23_7242196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 3, 1, 1, 1, 1, 5].length) (baseStart_7242196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7242196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7242196 prefixEnd_7242196 := by exact prefixLift 7242196
  have htrace : WordTrace (prefixWord ++ tailWord_7242196) baseStart_7242196 baseEnd_7242196 := by
    simpa [prefixWord, tailWord_7242196, baseEnd_7242196] using wordTrace_append hprefix tailTrace_7242196
  have hstable : (prefixWord ++ tailWord_7242196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7242196).length < 2 ^ (prefixWord ++ tailWord_7242196).sum := by decide
  have hdescent : baseEnd_7242196 < baseStart_7242196 := by decide
  rcases family_descends (prefixWord ++ tailWord_7242196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7242219 : List Nat := [1, 1, 1, 1, 2, 3, 3, 1, 5, 3, 2]
def baseStart_7242219 : Nat := 118140960795 + 7242219 * 2 ^ 59
def prefixEnd_7242219 : Nat := 4983230072969 + 3 ^ 40 * 7242219 * 2
def baseEnd_7242219 : Nat := 3718739352124105518556147

theorem tailTrace_7242219 : CollatzResearch.WordTrace tailWord_7242219 prefixEnd_7242219 3718739352124105518556147 := by
  unfold tailWord_7242219
  simp only [CollatzResearch.WordTrace]
  refine ⟨264145427349684910377857711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176096951566456606918571807 264145427349684910377857711)
  ·
    refine ⟨396218141024527365566786567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264145427349684910377857711 396218141024527365566786567)
    ·
      refine ⟨594327211536791048350179851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 396218141024527365566786567 594327211536791048350179851)
      ·
        refine ⟨891490817305186572525269777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 594327211536791048350179851 891490817305186572525269777)
        ·
          refine ⟨668618112978889929393952333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 891490817305186572525269777 668618112978889929393952333)
          ·
            refine ⟨250731792367083723522732125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 668618112978889929393952333 250731792367083723522732125)
            ·
              refine ⟨94024422137656396321024547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 250731792367083723522732125 94024422137656396321024547)
              ·
                refine ⟨141036633206484594481536821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94024422137656396321024547 141036633206484594481536821)
                ·
                  refine ⟨13222184363107930732644077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 141036633206484594481536821 13222184363107930732644077)
                  ·
                    refine ⟨4958319136165474024741529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13222184363107930732644077 4958319136165474024741529)
                    ·
                      refine ⟨3718739352124105518556147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4958319136165474024741529 3718739352124105518556147)
                      ·
                        rfl

theorem cell23_7242219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 1, 5, 3, 2].length) (baseStart_7242219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7242219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7242219 prefixEnd_7242219 := by exact prefixLift 7242219
  have htrace : WordTrace (prefixWord ++ tailWord_7242219) baseStart_7242219 baseEnd_7242219 := by
    simpa [prefixWord, tailWord_7242219, baseEnd_7242219] using wordTrace_append hprefix tailTrace_7242219
  have hstable : (prefixWord ++ tailWord_7242219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7242219).length < 2 ^ (prefixWord ++ tailWord_7242219).sum := by decide
  have hdescent : baseEnd_7242219 < baseStart_7242219 := by decide
  rcases family_descends (prefixWord ++ tailWord_7242219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7242232 : List Nat := [2, 1, 2, 1, 1, 4, 1, 2, 2, 3, 4]
def baseStart_7242232 : Nat := 118140960795 + 7242232 * 2 ^ 59
def prefixEnd_7242232 : Nat := 4983230072969 + 3 ^ 40 * 7242232 * 2
def baseEnd_7242232 : Nat := 3718746027372613967693587

theorem tailTrace_7242232 : CollatzResearch.WordTrace tailWord_7242232 prefixEnd_7242232 3718746027372613967693587 := by
  unfold tailWord_7242232
  simp only [CollatzResearch.WordTrace]
  refine ⟨132072950749318906799040475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176097267665758542398720633 132072950749318906799040475)
  ·
    refine ⟨198109426123978360198560713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132072950749318906799040475 198109426123978360198560713)
    ·
      refine ⟨148582069592983770148920535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 198109426123978360198560713 148582069592983770148920535)
      ·
        refine ⟨222873104389475655223380803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148582069592983770148920535 222873104389475655223380803)
        ·
          refine ⟨334309656584213482835071205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 222873104389475655223380803 334309656584213482835071205)
          ·
            refine ⟨62683060609540028031575851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 334309656584213482835071205 62683060609540028031575851)
            ·
              refine ⟨94024590914310042047363777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62683060609540028031575851 94024590914310042047363777)
              ·
                refine ⟨70518443185732531535522833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 94024590914310042047363777 70518443185732531535522833)
                ·
                  refine ⟨52888832389299398651642125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 70518443185732531535522833 52888832389299398651642125)
                  ·
                    refine ⟨19833312145987274494365797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 52888832389299398651642125 19833312145987274494365797)
                    ·
                      refine ⟨3718746027372613967693587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19833312145987274494365797 3718746027372613967693587)
                      ·
                        rfl

theorem cell23_7242232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 2, 2, 3, 4].length) (baseStart_7242232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7242232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7242232 prefixEnd_7242232 := by exact prefixLift 7242232
  have htrace : WordTrace (prefixWord ++ tailWord_7242232) baseStart_7242232 baseEnd_7242232 := by
    simpa [prefixWord, tailWord_7242232, baseEnd_7242232] using wordTrace_append hprefix tailTrace_7242232
  have hstable : (prefixWord ++ tailWord_7242232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7242232).length < 2 ^ (prefixWord ++ tailWord_7242232).sum := by decide
  have hdescent : baseEnd_7242232 < baseStart_7242232 := by decide
  rcases family_descends (prefixWord ++ tailWord_7242232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7242236 : List Nat := [2, 2, 2, 1, 2, 1, 1, 6, 1, 3, 2]
def baseStart_7242236 : Nat := 118140960795 + 7242236 * 2 ^ 59
def prefixEnd_7242236 : Nat := 4983230072969 + 3 ^ 40 * 7242236 * 2
def baseEnd_7242236 : Nat := 3718748081295231952043569

theorem tailTrace_7242236 : CollatzResearch.WordTrace tailWord_7242236 prefixEnd_7242236 3718748081295231952043569 := by
  unfold tailWord_7242236
  simp only [CollatzResearch.WordTrace]
  refine ⟨132073023695311661140613281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176097364927082214854151041 132073023695311661140613281)
  ·
    refine ⟨99054767771483745855459961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132073023695311661140613281 99054767771483745855459961)
    ·
      refine ⟨74291075828612809391594971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99054767771483745855459961 74291075828612809391594971)
      ·
        refine ⟨111436613742919214087392457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74291075828612809391594971 111436613742919214087392457)
        ·
          refine ⟨83577460307189410565544343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111436613742919214087392457 83577460307189410565544343)
          ·
            refine ⟨125366190460784115848316515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83577460307189410565544343 125366190460784115848316515)
            ·
              refine ⟨188049285691176173772474773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125366190460784115848316515 188049285691176173772474773)
              ·
                refine ⟨8814810266773883145584755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 188049285691176173772474773 8814810266773883145584755)
                ·
                  refine ⟨13222215400160824718377133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8814810266773883145584755 13222215400160824718377133)
                  ·
                    refine ⟨4958330775060309269391425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13222215400160824718377133 4958330775060309269391425)
                    ·
                      refine ⟨3718748081295231952043569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4958330775060309269391425 3718748081295231952043569)
                      ·
                        rfl

theorem cell23_7242236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 6, 1, 3, 2].length) (baseStart_7242236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7242236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7242236 prefixEnd_7242236 := by exact prefixLift 7242236
  have htrace : WordTrace (prefixWord ++ tailWord_7242236) baseStart_7242236 baseEnd_7242236 := by
    simpa [prefixWord, tailWord_7242236, baseEnd_7242236] using wordTrace_append hprefix tailTrace_7242236
  have hstable : (prefixWord ++ tailWord_7242236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7242236).length < 2 ^ (prefixWord ++ tailWord_7242236).sum := by decide
  have hdescent : baseEnd_7242236 < baseStart_7242236 := by decide
  rcases family_descends (prefixWord ++ tailWord_7242236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7242249 : List Nat := [1, 2, 1, 1, 3, 1, 2, 3, 3, 4, 2]
def baseStart_7242249 : Nat := 118140960795 + 7242249 * 2 ^ 59
def prefixEnd_7242249 : Nat := 4983230072969 + 3 ^ 40 * 7242249 * 2
def baseEnd_7242249 : Nat := 3718754756543740401181009

theorem tailTrace_7242249 : CollatzResearch.WordTrace tailWord_7242249 prefixEnd_7242249 3718754756543740401181009 := by
  unfold tailWord_7242249
  simp only [CollatzResearch.WordTrace]
  refine ⟨264146521539576225501449801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176097681026384150334299867 264146521539576225501449801)
  ·
    refine ⟨198109891154682169126087351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 264146521539576225501449801 198109891154682169126087351)
    ·
      refine ⟨297164836732023253689131027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198109891154682169126087351 297164836732023253689131027)
      ·
        refine ⟨445747255098034880533696541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 297164836732023253689131027 445747255098034880533696541)
        ·
          refine ⟨167155220661763080200136203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 445747255098034880533696541 167155220661763080200136203)
          ·
            refine ⟨250732830992644620300204305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 167155220661763080200136203 250732830992644620300204305)
            ·
              refine ⟨188049623244483465225153229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 250732830992644620300204305 188049623244483465225153229)
              ·
                refine ⟨70518608716681299459432461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 188049623244483465225153229 70518608716681299459432461)
                ·
                  refine ⟨26444478268755487297287173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 70518608716681299459432461 26444478268755487297287173)
                  ·
                    refine ⟨4958339675391653868241345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26444478268755487297287173 4958339675391653868241345)
                    ·
                      refine ⟨3718754756543740401181009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4958339675391653868241345 3718754756543740401181009)
                      ·
                        rfl

theorem cell23_7242249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 3, 3, 4, 2].length) (baseStart_7242249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7242249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7242249 prefixEnd_7242249 := by exact prefixLift 7242249
  have htrace : WordTrace (prefixWord ++ tailWord_7242249) baseStart_7242249 baseEnd_7242249 := by
    simpa [prefixWord, tailWord_7242249, baseEnd_7242249] using wordTrace_append hprefix tailTrace_7242249
  have hstable : (prefixWord ++ tailWord_7242249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7242249).length < 2 ^ (prefixWord ++ tailWord_7242249).sum := by decide
  have hdescent : baseEnd_7242249 < baseStart_7242249 := by decide
  rcases family_descends (prefixWord ++ tailWord_7242249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7242260 : List Nat := [2, 4, 3, 1, 1, 1, 3, 2, 2, 1, 3]
def baseStart_7242260 : Nat := 118140960795 + 7242260 * 2 ^ 59
def prefixEnd_7242260 : Nat := 4983230072969 + 3 ^ 40 * 7242260 * 2
def baseEnd_7242260 : Nat := 3718760404830939858143459

theorem tailTrace_7242260 : CollatzResearch.WordTrace tailWord_7242260 prefixEnd_7242260 3718760404830939858143459 := by
  unfold tailWord_7242260
  simp only [CollatzResearch.WordTrace]
  refine ⟨132073461371268187190050117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176097948495024249586733489 132073461371268187190050117)
  ·
    refine ⟨24763774007112785098134397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 132073461371268187190050117 24763774007112785098134397)
    ·
      refine ⟨9286415252667294411800399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24763774007112785098134397 9286415252667294411800399)
      ·
        refine ⟨13929622879000941617700599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9286415252667294411800399 13929622879000941617700599)
        ·
          refine ⟨20894434318501412426550899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13929622879000941617700599 20894434318501412426550899)
          ·
            refine ⟨31341651477752118639826349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20894434318501412426550899 31341651477752118639826349)
            ·
              refine ⟨11753119304157044489934881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31341651477752118639826349 11753119304157044489934881)
              ·
                refine ⟨8814839478117783367451161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11753119304157044489934881 8814839478117783367451161)
                ·
                  refine ⟨6611129608588337525588371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8814839478117783367451161 6611129608588337525588371)
                  ·
                    refine ⟨9916694412882506288382557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6611129608588337525588371 9916694412882506288382557)
                    ·
                      refine ⟨3718760404830939858143459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9916694412882506288382557 3718760404830939858143459)
                      ·
                        rfl

theorem cell23_7242260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 3, 2, 2, 1, 3].length) (baseStart_7242260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7242260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7242260 prefixEnd_7242260 := by exact prefixLift 7242260
  have htrace : WordTrace (prefixWord ++ tailWord_7242260) baseStart_7242260 baseEnd_7242260 := by
    simpa [prefixWord, tailWord_7242260, baseEnd_7242260] using wordTrace_append hprefix tailTrace_7242260
  have hstable : (prefixWord ++ tailWord_7242260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7242260).length < 2 ^ (prefixWord ++ tailWord_7242260).sum := by decide
  have hdescent : baseEnd_7242260 < baseStart_7242260 := by decide
  rcases family_descends (prefixWord ++ tailWord_7242260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7242312 : List Nat := [2, 1, 3, 1, 1, 1, 1, 2, 3, 1, 7]
def baseStart_7242312 : Nat := 118140960795 + 7242312 * 2 ^ 59
def prefixEnd_7242312 : Nat := 4983230072969 + 3 ^ 40 * 7242312 * 2
def baseEnd_7242312 : Nat := 3718787105824973654693219

theorem tailTrace_7242312 : CollatzResearch.WordTrace tailWord_7242312 prefixEnd_7242312 3718787105824973654693219 := by
  unfold tailWord_7242312
  simp only [CollatzResearch.WordTrace]
  refine ⟨132074409669173993630496595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176099212892231991507328793 132074409669173993630496595)
  ·
    refine ⟨198111614503760990445744893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132074409669173993630496595 198111614503760990445744893)
    ·
      refine ⟨74291855438910371417154335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 198111614503760990445744893 74291855438910371417154335)
      ·
        refine ⟨111437783158365557125731503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74291855438910371417154335 111437783158365557125731503)
        ·
          refine ⟨167156674737548335688597255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111437783158365557125731503 167156674737548335688597255)
          ·
            refine ⟨250735012106322503532895883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 167156674737548335688597255 250735012106322503532895883)
            ·
              refine ⟨376102518159483755299343825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 250735012106322503532895883 376102518159483755299343825)
              ·
                refine ⟨282076888619612816474507869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 376102518159483755299343825 282076888619612816474507869)
                ·
                  refine ⟨105778833232354806177940451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 282076888619612816474507869 105778833232354806177940451)
                  ·
                    refine ⟨158668249848532209266910677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 105778833232354806177940451 158668249848532209266910677)
                    ·
                      refine ⟨3718787105824973654693219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 158668249848532209266910677 3718787105824973654693219)
                      ·
                        rfl

theorem cell23_7242312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 2, 3, 1, 7].length) (baseStart_7242312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7242312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7242312 prefixEnd_7242312 := by exact prefixLift 7242312
  have htrace : WordTrace (prefixWord ++ tailWord_7242312) baseStart_7242312 baseEnd_7242312 := by
    simpa [prefixWord, tailWord_7242312, baseEnd_7242312] using wordTrace_append hprefix tailTrace_7242312
  have hstable : (prefixWord ++ tailWord_7242312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7242312).length < 2 ^ (prefixWord ++ tailWord_7242312).sum := by decide
  have hdescent : baseEnd_7242312 < baseStart_7242312 := by decide
  rcases family_descends (prefixWord ++ tailWord_7242312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7242339 : List Nat := [1, 1, 1, 5, 1, 2, 1, 2, 4, 1, 4]
def baseStart_7242339 : Nat := 118140960795 + 7242339 * 2 ^ 59
def prefixEnd_7242339 : Nat := 4983230072969 + 3 ^ 40 * 7242339 * 2
def baseEnd_7242339 : Nat := 3718800969802645049055595

theorem tailTrace_7242339 : CollatzResearch.WordTrace tailWord_7242339 prefixEnd_7242339 3718800969802645049055595 := by
  unfold tailWord_7242339
  simp only [CollatzResearch.WordTrace]
  refine ⟨264149804109250170872226071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176099869406166780581484047 264149804109250170872226071)
  ·
    refine ⟨396224706163875256308339107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264149804109250170872226071 396224706163875256308339107)
    ·
      refine ⟨594337059245812884462508661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 396224706163875256308339107 594337059245812884462508661)
      ·
        refine ⟨55719099304294957918360187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 594337059245812884462508661 55719099304294957918360187)
        ·
          refine ⟨83578648956442436877540281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55719099304294957918360187 83578648956442436877540281)
          ·
            refine ⟨62683986717331827658155211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83578648956442436877540281 62683986717331827658155211)
            ·
              refine ⟨94025980075997741487232817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62683986717331827658155211 94025980075997741487232817)
              ·
                refine ⟨70519485056998306115424613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 94025980075997741487232817 70519485056998306115424613)
                ·
                  refine ⟨13222403448187182396642115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 70519485056998306115424613 13222403448187182396642115)
                  ·
                    refine ⟨19833605172280773594963173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13222403448187182396642115 19833605172280773594963173)
                    ·
                      refine ⟨3718800969802645049055595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19833605172280773594963173 3718800969802645049055595)
                      ·
                        rfl

theorem cell23_7242339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 2, 4, 1, 4].length) (baseStart_7242339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7242339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7242339 prefixEnd_7242339 := by exact prefixLift 7242339
  have htrace : WordTrace (prefixWord ++ tailWord_7242339) baseStart_7242339 baseEnd_7242339 := by
    simpa [prefixWord, tailWord_7242339, baseEnd_7242339] using wordTrace_append hprefix tailTrace_7242339
  have hstable : (prefixWord ++ tailWord_7242339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7242339).length < 2 ^ (prefixWord ++ tailWord_7242339).sum := by decide
  have hdescent : baseEnd_7242339 < baseStart_7242339 := by decide
  rcases family_descends (prefixWord ++ tailWord_7242339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7242359 : List Nat := [1, 1, 3, 1, 1, 3, 2, 3, 1, 4, 3]
def baseStart_7242359 : Nat := 118140960795 + 7242359 * 2 ^ 59
def prefixEnd_7242359 : Nat := 4983230072969 + 3 ^ 40 * 7242359 * 2
def baseEnd_7242359 : Nat := 3718811239415734970805503

theorem tailTrace_7242359 : CollatzResearch.WordTrace tailWord_7242359 prefixEnd_7242359 3718811239415734970805503 := by
  unfold tailWord_7242359
  simp only [CollatzResearch.WordTrace]
  refine ⟨264150533569177714287954131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176100355712785142858636087 264150533569177714287954131)
  ·
    refine ⟨396225800353766571431931197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264150533569177714287954131 396225800353766571431931197)
    ·
      refine ⟨148584675132662464286974199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 396225800353766571431931197 148584675132662464286974199)
      ·
        refine ⟨222877012698993696430461299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148584675132662464286974199 222877012698993696430461299)
        ·
          refine ⟨334315519048490544645691949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 222877012698993696430461299 334315519048490544645691949)
          ·
            refine ⟨125368319643183954242134481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 334315519048490544645691949 125368319643183954242134481)
            ·
              refine ⟨94026239732387965681600861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 125368319643183954242134481 94026239732387965681600861)
              ·
                refine ⟨35259839899645487130600323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 94026239732387965681600861 35259839899645487130600323)
                ·
                  refine ⟨52889759849468230695900485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35259839899645487130600323 52889759849468230695900485)
                  ·
                    refine ⟨9916829971775293255481341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 52889759849468230695900485 9916829971775293255481341)
                    ·
                      refine ⟨3718811239415734970805503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9916829971775293255481341 3718811239415734970805503)
                      ·
                        rfl

theorem cell23_7242359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 3, 1, 4, 3].length) (baseStart_7242359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7242359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7242359 prefixEnd_7242359 := by exact prefixLift 7242359
  have htrace : WordTrace (prefixWord ++ tailWord_7242359) baseStart_7242359 baseEnd_7242359 := by
    simpa [prefixWord, tailWord_7242359, baseEnd_7242359] using wordTrace_append hprefix tailTrace_7242359
  have hstable : (prefixWord ++ tailWord_7242359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7242359).length < 2 ^ (prefixWord ++ tailWord_7242359).sum := by decide
  have hdescent : baseEnd_7242359 < baseStart_7242359 := by decide
  rcases family_descends (prefixWord ++ tailWord_7242359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7242369 : List Nat := [1, 2, 4, 2, 1, 1, 2, 1, 2, 1, 6]
def baseStart_7242369 : Nat := 118140960795 + 7242369 * 2 ^ 59
def prefixEnd_7242369 : Nat := 4983230072969 + 3 ^ 40 * 7242369 * 2
def baseEnd_7242369 : Nat := 3718816374222279931680457

theorem tailTrace_7242369 : CollatzResearch.WordTrace tailWord_7242369 prefixEnd_7242369 3718816374222279931680457 := by
  unfold tailWord_7242369
  simp only [CollatzResearch.WordTrace]
  refine ⟨264150898299141485995818161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176100598866094323997212107 264150898299141485995818161)
  ·
    refine ⟨198113173724356114496863621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 264150898299141485995818161 198113173724356114496863621)
    ·
      refine ⟨37146220073316771468161929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 198113173724356114496863621 37146220073316771468161929)
      ·
        refine ⟨27859665054987578601121447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37146220073316771468161929 27859665054987578601121447)
        ·
          refine ⟨41789497582481367901682171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27859665054987578601121447 41789497582481367901682171)
          ·
            refine ⟨62684246373722051852523257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41789497582481367901682171 62684246373722051852523257)
            ·
              refine ⟨47013184780291538889392443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62684246373722051852523257 47013184780291538889392443)
              ·
                refine ⟨70519777170437308334088665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47013184780291538889392443 70519777170437308334088665)
                ·
                  refine ⟨52889832877827981250566499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 70519777170437308334088665 52889832877827981250566499)
                  ·
                    refine ⟨79334749316741971875849749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 52889832877827981250566499 79334749316741971875849749)
                    ·
                      refine ⟨3718816374222279931680457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 79334749316741971875849749 3718816374222279931680457)
                      ·
                        rfl

theorem cell23_7242369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 2, 1, 2, 1, 6].length) (baseStart_7242369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7242369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7242369 prefixEnd_7242369 := by exact prefixLift 7242369
  have htrace : WordTrace (prefixWord ++ tailWord_7242369) baseStart_7242369 baseEnd_7242369 := by
    simpa [prefixWord, tailWord_7242369, baseEnd_7242369] using wordTrace_append hprefix tailTrace_7242369
  have hstable : (prefixWord ++ tailWord_7242369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7242369).length < 2 ^ (prefixWord ++ tailWord_7242369).sum := by decide
  have hdescent : baseEnd_7242369 < baseStart_7242369 := by decide
  rcases family_descends (prefixWord ++ tailWord_7242369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7242389 : List Nat := [1, 3, 2, 1, 1, 1, 1, 1, 4, 5, 3]
def baseStart_7242389 : Nat := 118140960795 + 7242389 * 2 ^ 59
def prefixEnd_7242389 : Nat := 4983230072969 + 3 ^ 40 * 7242389 * 2
def baseEnd_7242389 : Nat := 3718826643835369853430365

theorem tailTrace_7242389 : CollatzResearch.WordTrace tailWord_7242389 prefixEnd_7242389 3718826643835369853430365 := by
  unfold tailWord_7242389
  simp only [CollatzResearch.WordTrace]
  refine ⟨264151627759069029411546221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176101085172712686274364147 264151627759069029411546221)
  ·
    refine ⟨99056860409650886029329833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 264151627759069029411546221 99056860409650886029329833)
    ·
      refine ⟨74292645307238164521997375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99056860409650886029329833 74292645307238164521997375)
      ·
        refine ⟨111438967960857246782996063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74292645307238164521997375 111438967960857246782996063)
        ·
          refine ⟨167158451941285870174494095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111438967960857246782996063 167158451941285870174494095)
          ·
            refine ⟨250737677911928805261741143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 167158451941285870174494095 250737677911928805261741143)
            ·
              refine ⟨376106516867893207892611715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 250737677911928805261741143 376106516867893207892611715)
              ·
                refine ⟨564159775301839811838917573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 376106516867893207892611715 564159775301839811838917573)
                ·
                  refine ⟨105779957869094964719797045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 564159775301839811838917573 105779957869094964719797045)
                  ·
                    refine ⟨9916871050227652942480973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 105779957869094964719797045 9916871050227652942480973)
                    ·
                      refine ⟨3718826643835369853430365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9916871050227652942480973 3718826643835369853430365)
                      ·
                        rfl

theorem cell23_7242389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 1, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 1, 4, 5, 3].length) (baseStart_7242389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7242389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7242389 prefixEnd_7242389 := by exact prefixLift 7242389
  have htrace : WordTrace (prefixWord ++ tailWord_7242389) baseStart_7242389 baseEnd_7242389 := by
    simpa [prefixWord, tailWord_7242389, baseEnd_7242389] using wordTrace_append hprefix tailTrace_7242389
  have hstable : (prefixWord ++ tailWord_7242389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7242389).length < 2 ^ (prefixWord ++ tailWord_7242389).sum := by decide
  have hdescent : baseEnd_7242389 < baseStart_7242389 := by decide
  rcases family_descends (prefixWord ++ tailWord_7242389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7242396 : List Nat := [2, 2, 3, 2, 2, 1, 2, 3, 6]
def baseStart_7242396 : Nat := 118140960795 + 7242396 * 2 ^ 59
def prefixEnd_7242396 : Nat := 4983230072969 + 3 ^ 40 * 7242396 * 2
def baseEnd_7242396 : Nat := 413203359799994591782537

theorem tailTrace_7242396 : CollatzResearch.WordTrace tailWord_7242396 prefixEnd_7242396 413203359799994591782537 := by
  unfold tailWord_7242396
  simp only [CollatzResearch.WordTrace]
  refine ⟨132075941535021834803525521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176101255380029113071367361 132075941535021834803525521)
  ·
    refine ⟨99056956151266376102644141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132075941535021834803525521 99056956151266376102644141)
    ·
      refine ⟨37146358556724891038491553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99056956151266376102644141 37146358556724891038491553)
      ·
        refine ⟨27859768917543668278868665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37146358556724891038491553 27859768917543668278868665)
        ·
          refine ⟨20894826688157751209151499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27859768917543668278868665 20894826688157751209151499)
          ·
            refine ⟨31342240032236626813727249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20894826688157751209151499 31342240032236626813727249)
            ·
              refine ⟨23506680024177470110295437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31342240032236626813727249 23506680024177470110295437)
              ·
                refine ⟨8815005009066551291360789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23506680024177470110295437 8815005009066551291360789)
                ·
                  refine ⟨413203359799994591782537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8815005009066551291360789 413203359799994591782537)
                  ·
                    rfl

theorem cell23_7242396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 2, 3, 6].length) (baseStart_7242396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7242396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7242396 prefixEnd_7242396 := by exact prefixLift 7242396
  have htrace : WordTrace (prefixWord ++ tailWord_7242396) baseStart_7242396 baseEnd_7242396 := by
    simpa [prefixWord, tailWord_7242396, baseEnd_7242396] using wordTrace_append hprefix tailTrace_7242396
  have hstable : (prefixWord ++ tailWord_7242396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7242396).length < 2 ^ (prefixWord ++ tailWord_7242396).sum := by decide
  have hdescent : baseEnd_7242396 < baseStart_7242396 := by decide
  rcases family_descends (prefixWord ++ tailWord_7242396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7242407 : List Nat := [1, 1, 6, 3, 2, 1, 1, 1, 2, 1, 4]
def baseStart_7242407 : Nat := 118140960795 + 7242407 * 2 ^ 59
def prefixEnd_7242407 : Nat := 4983230072969 + 3 ^ 40 * 7242407 * 2
def baseEnd_7242407 : Nat := 3718835886487150783005283

theorem tailTrace_7242407 : CollatzResearch.WordTrace tailWord_7242407 prefixEnd_7242407 3718835886487150783005283 := by
  unfold tailWord_7242407
  simp only [CollatzResearch.WordTrace]
  refine ⟨264152284273003818485701475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176101522848669212323800983 264152284273003818485701475)
  ·
    refine ⟨396228426409505727728552213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264152284273003818485701475 396228426409505727728552213)
    ·
      refine ⟨18573207487945580987275885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 396228426409505727728552213 18573207487945580987275885)
      ·
        refine ⟨6964952807979592870228457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18573207487945580987275885 6964952807979592870228457)
        ·
          refine ⟨5223714605984694652671343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6964952807979592870228457 5223714605984694652671343)
          ·
            refine ⟨7835571908977041979007015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5223714605984694652671343 7835571908977041979007015)
            ·
              refine ⟨11753357863465562968510523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7835571908977041979007015 11753357863465562968510523)
              ·
                refine ⟨17630036795198344452765785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11753357863465562968510523 17630036795198344452765785)
                ·
                  refine ⟨13222527596398758339574339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17630036795198344452765785 13222527596398758339574339)
                  ·
                    refine ⟨19833791394598137509361509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13222527596398758339574339 19833791394598137509361509)
                    ·
                      refine ⟨3718835886487150783005283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19833791394598137509361509 3718835886487150783005283)
                      ·
                        rfl

theorem cell23_7242407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 2, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 2, 1, 1, 1, 2, 1, 4].length) (baseStart_7242407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7242407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7242407 prefixEnd_7242407 := by exact prefixLift 7242407
  have htrace : WordTrace (prefixWord ++ tailWord_7242407) baseStart_7242407 baseEnd_7242407 := by
    simpa [prefixWord, tailWord_7242407, baseEnd_7242407] using wordTrace_append hprefix tailTrace_7242407
  have hstable : (prefixWord ++ tailWord_7242407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7242407).length < 2 ^ (prefixWord ++ tailWord_7242407).sum := by decide
  have hdescent : baseEnd_7242407 < baseStart_7242407 := by decide
  rcases family_descends (prefixWord ++ tailWord_7242407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7242410 : List Nat := [3, 1, 5, 2, 1, 1, 1, 1, 1, 4, 3]
def baseStart_7242410 : Nat := 118140960795 + 7242410 * 2 ^ 59
def prefixEnd_7242410 : Nat := 4983230072969 + 3 ^ 40 * 7242410 * 2
def baseEnd_7242410 : Nat := 3718837426929114271267769

theorem tailTrace_7242410 : CollatzResearch.WordTrace tailWord_7242410 prefixEnd_7242410 3718837426929114271267769 := by
  unfold tailWord_7242410
  simp only [CollatzResearch.WordTrace]
  refine ⟨66038098422998237499515171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176101595794661966665373789 66038098422998237499515171)
  ·
    refine ⟨99057147634497356249272757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66038098422998237499515171 99057147634497356249272757)
    ·
      refine ⟨9286607590734127148369321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 99057147634497356249272757 9286607590734127148369321)
      ·
        refine ⟨6964955693050595361276991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9286607590734127148369321 6964955693050595361276991)
        ·
          refine ⟨10447433539575893041915487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6964955693050595361276991 10447433539575893041915487)
          ·
            refine ⟨15671150309363839562873231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10447433539575893041915487 15671150309363839562873231)
            ·
              refine ⟨23506725464045759344309847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15671150309363839562873231 23506725464045759344309847)
              ·
                refine ⟨35260088196068639016464771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23506725464045759344309847 35260088196068639016464771)
                ·
                  refine ⟨52890132294102958524697157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35260088196068639016464771 52890132294102958524697157)
                  ·
                    refine ⟨9916899805144304723380717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 52890132294102958524697157 9916899805144304723380717)
                    ·
                      refine ⟨3718837426929114271267769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9916899805144304723380717 3718837426929114271267769)
                      ·
                        rfl

theorem cell23_7242410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 1, 1, 1, 4, 3].length) (baseStart_7242410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7242410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7242410 prefixEnd_7242410 := by exact prefixLift 7242410
  have htrace : WordTrace (prefixWord ++ tailWord_7242410) baseStart_7242410 baseEnd_7242410 := by
    simpa [prefixWord, tailWord_7242410, baseEnd_7242410] using wordTrace_append hprefix tailTrace_7242410
  have hstable : (prefixWord ++ tailWord_7242410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7242410).length < 2 ^ (prefixWord ++ tailWord_7242410).sum := by decide
  have hdescent : baseEnd_7242410 < baseStart_7242410 := by decide
  rcases family_descends (prefixWord ++ tailWord_7242410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7242417 : List Nat := [1, 2, 2, 6, 1, 1, 2, 3, 1, 4]
def baseStart_7242417 : Nat := 118140960795 + 7242417 * 2 ^ 59
def prefixEnd_7242417 : Nat := 4983230072969 + 3 ^ 40 * 7242417 * 2
def baseEnd_7242417 : Nat := 1239613673764565247960079

theorem tailTrace_7242417 : CollatzResearch.WordTrace tailWord_7242417 prefixEnd_7242417 1239613673764565247960079 := by
  unfold tailWord_7242417
  simp only [CollatzResearch.WordTrace]
  refine ⟨264152649002967590193565505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176101766001978393462377003 264152649002967590193565505)
  ·
    refine ⟨198114486752225692645174129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 264152649002967590193565505 198114486752225692645174129)
    ·
      refine ⟨148585865064169269483880597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 198114486752225692645174129 148585865064169269483880597)
      ·
        refine ⟨6964962424882934507056903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 148585865064169269483880597 6964962424882934507056903)
        ·
          refine ⟨10447443637324401760585355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6964962424882934507056903 10447443637324401760585355)
          ·
            refine ⟨15671165455986602640878033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10447443637324401760585355 15671165455986602640878033)
            ·
              refine ⟨11753374091989951980658525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15671165455986602640878033 11753374091989951980658525)
              ·
                refine ⟨4407515284496231992746947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11753374091989951980658525 4407515284496231992746947)
                ·
                  refine ⟨6611272926744347989120421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4407515284496231992746947 6611272926744347989120421)
                  ·
                    refine ⟨1239613673764565247960079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6611272926744347989120421 1239613673764565247960079)
                    ·
                      rfl

theorem cell23_7242417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 2, 3, 1, 4].length) (baseStart_7242417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7242417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7242417 prefixEnd_7242417 := by exact prefixLift 7242417
  have htrace : WordTrace (prefixWord ++ tailWord_7242417) baseStart_7242417 baseEnd_7242417 := by
    simpa [prefixWord, tailWord_7242417, baseEnd_7242417] using wordTrace_append hprefix tailTrace_7242417
  have hstable : (prefixWord ++ tailWord_7242417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7242417).length < 2 ^ (prefixWord ++ tailWord_7242417).sum := by decide
  have hdescent : baseEnd_7242417 < baseStart_7242417 := by decide
  rcases family_descends (prefixWord ++ tailWord_7242417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7242426 : List Nat := [3, 1, 1, 1, 2, 3, 3, 3, 1, 5]
def baseStart_7242426 : Nat := 118140960795 + 7242426 * 2 ^ 59
def prefixEnd_7242426 : Nat := 4983230072969 + 3 ^ 40 * 7242426 * 2
def baseEnd_7242426 : Nat := 1239615214206528736222565

theorem tailTrace_7242426 : CollatzResearch.WordTrace tailWord_7242426 prefixEnd_7242426 1239615214206528736222565 := by
  unfold tailWord_7242426
  simp only [CollatzResearch.WordTrace]
  refine ⟨66038244314983746182660783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176101984839956656487095421 66038244314983746182660783)
  ·
    refine ⟨99057366472475619273991175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66038244314983746182660783 99057366472475619273991175)
    ·
      refine ⟨148586049708713428910986763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99057366472475619273991175 148586049708713428910986763)
      ·
        refine ⟨222879074563070143366480145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148586049708713428910986763 222879074563070143366480145)
        ·
          refine ⟨167159305922302607524860109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 222879074563070143366480145 167159305922302607524860109)
          ·
            refine ⟨62684739720863477821822541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 167159305922302607524860109 62684739720863477821822541)
            ·
              refine ⟨23506777395323804183183453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62684739720863477821822541 23506777395323804183183453)
              ·
                refine ⟨8815041523246426568693795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23506777395323804183183453 8815041523246426568693795)
                ·
                  refine ⟨13222562284869639853040693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8815041523246426568693795 13222562284869639853040693)
                  ·
                    refine ⟨1239615214206528736222565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13222562284869639853040693 1239615214206528736222565)
                    ·
                      rfl

theorem cell23_7242426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 3, 3, 1, 5].length) (baseStart_7242426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7242426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7242426 prefixEnd_7242426 := by exact prefixLift 7242426
  have htrace : WordTrace (prefixWord ++ tailWord_7242426) baseStart_7242426 baseEnd_7242426 := by
    simpa [prefixWord, tailWord_7242426, baseEnd_7242426] using wordTrace_append hprefix tailTrace_7242426
  have hstable : (prefixWord ++ tailWord_7242426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7242426).length < 2 ^ (prefixWord ++ tailWord_7242426).sum := by decide
  have hdescent : baseEnd_7242426 < baseStart_7242426 := by decide
  rcases family_descends (prefixWord ++ tailWord_7242426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7242440 : List Nat := [2, 1, 3, 1, 2, 3, 2, 4, 1, 1, 3]
def baseStart_7242440 : Nat := 118140960795 + 7242440 * 2 ^ 59
def prefixEnd_7242440 : Nat := 4983230072969 + 3 ^ 40 * 7242440 * 2
def baseEnd_7242440 : Nat := 3718852831348749153892631

theorem tailTrace_7242440 : CollatzResearch.WordTrace tailWord_7242440 prefixEnd_7242440 3718852831348749153892631 := by
  unfold tailWord_7242440
  simp only [CollatzResearch.WordTrace]
  refine ⟨132076743940942132560826387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176102325254589510081101849 132076743940942132560826387)
  ·
    refine ⟨198115115911413198841239581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132076743940942132560826387 198115115911413198841239581)
    ·
      refine ⟨74293168466779949565464843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 198115115911413198841239581 74293168466779949565464843)
      ·
        refine ⟨111439752700169924348197265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74293168466779949565464843 111439752700169924348197265)
        ·
          refine ⟨83579814525127443261147949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111439752700169924348197265 83579814525127443261147949)
          ·
            refine ⟨31342430446922791222930481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 83579814525127443261147949 31342430446922791222930481)
            ·
              refine ⟨23506822835192093417197861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31342430446922791222930481 23506822835192093417197861)
              ·
                refine ⟨4407529281598517515724599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23506822835192093417197861 4407529281598517515724599)
                ·
                  refine ⟨6611293922397776273586899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4407529281598517515724599 6611293922397776273586899)
                  ·
                    refine ⟨9916940883596664410380349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6611293922397776273586899 9916940883596664410380349)
                    ·
                      refine ⟨3718852831348749153892631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9916940883596664410380349 3718852831348749153892631)
                      ·
                        rfl

theorem cell23_7242440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 2, 4, 1, 1, 3].length) (baseStart_7242440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7242440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7242440 prefixEnd_7242440 := by exact prefixLift 7242440
  have htrace : WordTrace (prefixWord ++ tailWord_7242440) baseStart_7242440 baseEnd_7242440 := by
    simpa [prefixWord, tailWord_7242440, baseEnd_7242440] using wordTrace_append hprefix tailTrace_7242440
  have hstable : (prefixWord ++ tailWord_7242440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7242440).length < 2 ^ (prefixWord ++ tailWord_7242440).sum := by decide
  have hdescent : baseEnd_7242440 < baseStart_7242440 := by decide
  rcases family_descends (prefixWord ++ tailWord_7242440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7242456 : List Nat := [2, 1, 2, 2, 3, 2, 3, 1, 1, 6]
def baseStart_7242456 : Nat := 118140960795 + 7242456 * 2 ^ 59
def prefixEnd_7242456 : Nat := 4983230072969 + 3 ^ 40 * 7242456 * 2
def baseEnd_7242456 : Nat := 1239620349013073697097519

theorem tailTrace_7242456 : CollatzResearch.WordTrace tailWord_7242456 prefixEnd_7242456 1239620349013073697097519 := by
  unfold tailWord_7242456
  simp only [CollatzResearch.WordTrace]
  refine ⟨132077035724913149927117611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176102714299884199902823481 132077035724913149927117611)
  ·
    refine ⟨198115553587369724890676417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132077035724913149927117611 198115553587369724890676417)
    ·
      refine ⟨148586665190527293668007313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 198115553587369724890676417 148586665190527293668007313)
      ·
        refine ⟨111439998892895470251005485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148586665190527293668007313 111439998892895470251005485)
        ·
          refine ⟨41789999584835801344127057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 111439998892895470251005485 41789999584835801344127057)
          ·
            refine ⟨31342499688626851008095293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41789999584835801344127057 31342499688626851008095293)
            ·
              refine ⟨11753437383235069128035735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31342499688626851008095293 11753437383235069128035735)
              ·
                refine ⟨17630156074852603692053603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11753437383235069128035735 17630156074852603692053603)
                ·
                  refine ⟨26445234112278905538080405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17630156074852603692053603 26445234112278905538080405)
                  ·
                    refine ⟨1239620349013073697097519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26445234112278905538080405 1239620349013073697097519)
                    ·
                      rfl

theorem cell23_7242456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 3, 1, 1, 6].length) (baseStart_7242456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7242456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7242456 prefixEnd_7242456 := by exact prefixLift 7242456
  have htrace : WordTrace (prefixWord ++ tailWord_7242456) baseStart_7242456 baseEnd_7242456 := by
    simpa [prefixWord, tailWord_7242456, baseEnd_7242456] using wordTrace_append hprefix tailTrace_7242456
  have hstable : (prefixWord ++ tailWord_7242456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7242456).length < 2 ^ (prefixWord ++ tailWord_7242456).sum := by decide
  have hdescent : baseEnd_7242456 < baseStart_7242456 := by decide
  rcases family_descends (prefixWord ++ tailWord_7242456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7242459 : List Nat := [1, 1, 1, 1, 1, 1, 1, 3, 7, 2, 4]
def baseStart_7242459 : Nat := 118140960795 + 7242459 * 2 ^ 59
def prefixEnd_7242459 : Nat := 4983230072969 + 3 ^ 40 * 7242459 * 2
def baseEnd_7242459 : Nat := 3718862587481184579555043

theorem tailTrace_7242459 : CollatzResearch.WordTrace tailWord_7242459 prefixEnd_7242459 3718862587481184579555043 := by
  unfold tailWord_7242459
  simp only [CollatzResearch.WordTrace]
  refine ⟨264154180868815431366594431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176102787245876954244396287 264154180868815431366594431)
  ·
    refine ⟨396231271303223147049891647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264154180868815431366594431 396231271303223147049891647)
    ·
      refine ⟨594346906954834720574837471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 396231271303223147049891647 594346906954834720574837471)
      ·
        refine ⟨891520360432252080862256207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 594346906954834720574837471 891520360432252080862256207)
        ·
          refine ⟨1337280540648378121293384311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 891520360432252080862256207 1337280540648378121293384311)
          ·
            refine ⟨2005920810972567181940076467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1337280540648378121293384311 2005920810972567181940076467)
            ·
              refine ⟨3008881216458850772910114701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2005920810972567181940076467 3008881216458850772910114701)
              ·
                refine ⟨1128330456172069039841293013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3008881216458850772910114701 1128330456172069039841293013)
                ·
                  refine ⟨26445245066532868121280305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1128330456172069039841293013 26445245066532868121280305)
                  ·
                    refine ⟨19833933799899651090960229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26445245066532868121280305 19833933799899651090960229)
                    ·
                      refine ⟨3718862587481184579555043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19833933799899651090960229 3718862587481184579555043)
                      ·
                        rfl

theorem cell23_7242459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 7, 2, 4].length) (baseStart_7242459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7242459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7242459 prefixEnd_7242459 := by exact prefixLift 7242459
  have htrace : WordTrace (prefixWord ++ tailWord_7242459) baseStart_7242459 baseEnd_7242459 := by
    simpa [prefixWord, tailWord_7242459, baseEnd_7242459] using wordTrace_append hprefix tailTrace_7242459
  have hstable : (prefixWord ++ tailWord_7242459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7242459).length < 2 ^ (prefixWord ++ tailWord_7242459).sum := by decide
  have hdescent : baseEnd_7242459 < baseStart_7242459 := by decide
  rcases family_descends (prefixWord ++ tailWord_7242459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7242460 : List Nat := [2, 2, 5, 1, 1, 2, 2, 2, 1, 5]
def baseStart_7242460 : Nat := 118140960795 + 7242460 * 2 ^ 59
def prefixEnd_7242460 : Nat := 4983230072969 + 3 ^ 40 * 7242460 * 2
def baseEnd_7242460 : Nat := 1239621033653946358547513

theorem tailTrace_7242460 : CollatzResearch.WordTrace tailWord_7242460 prefixEnd_7242460 1239621033653946358547513 := by
  unfold tailWord_7242460
  simp only [CollatzResearch.WordTrace]
  refine ⟨132077108670905904268690417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176102811561207872358253889 132077108670905904268690417)
  ·
    refine ⟨99057831503179428201517813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132077108670905904268690417 99057831503179428201517813)
    ·
      refine ⟨9286671703423071393892295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 99057831503179428201517813 9286671703423071393892295)
      ·
        refine ⟨13930007555134607090838443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9286671703423071393892295 13930007555134607090838443)
        ·
          refine ⟨20895011332701910636257665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13930007555134607090838443 20895011332701910636257665)
          ·
            refine ⟨15671258499526432977193249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20895011332701910636257665 15671258499526432977193249)
            ·
              refine ⟨11753443874644824732894937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15671258499526432977193249 11753443874644824732894937)
              ·
                refine ⟨8815082905983618549671203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11753443874644824732894937 8815082905983618549671203)
                ·
                  refine ⟨13222624358975427824506805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8815082905983618549671203 13222624358975427824506805)
                  ·
                    refine ⟨1239621033653946358547513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13222624358975427824506805 1239621033653946358547513)
                    ·
                      rfl

theorem cell23_7242460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 2, 2, 1, 5].length) (baseStart_7242460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7242460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7242460 prefixEnd_7242460 := by exact prefixLift 7242460
  have htrace : WordTrace (prefixWord ++ tailWord_7242460) baseStart_7242460 baseEnd_7242460 := by
    simpa [prefixWord, tailWord_7242460, baseEnd_7242460] using wordTrace_append hprefix tailTrace_7242460
  have hstable : (prefixWord ++ tailWord_7242460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7242460).length < 2 ^ (prefixWord ++ tailWord_7242460).sum := by decide
  have hdescent : baseEnd_7242460 < baseStart_7242460 := by decide
  rcases family_descends (prefixWord ++ tailWord_7242460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7242463 : List Nat := [1, 1, 2, 3, 2, 4, 2, 2, 1, 1, 4]
def baseStart_7242463 : Nat := 118140960795 + 7242463 * 2 ^ 59
def prefixEnd_7242463 : Nat := 4983230072969 + 3 ^ 40 * 7242463 * 2
def baseEnd_7242463 : Nat := 3718864641403802563905025

theorem tailTrace_7242463 : CollatzResearch.WordTrace tailWord_7242463 prefixEnd_7242463 3718864641403802563905025 := by
  unfold tailWord_7242463
  simp only [CollatzResearch.WordTrace]
  refine ⟨264154326760800940049740043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176102884507200626699826695 264154326760800940049740043)
  ·
    refine ⟨396231490141201410074610065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264154326760800940049740043 396231490141201410074610065)
    ·
      refine ⟨297173617605901057555957549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 396231490141201410074610065 297173617605901057555957549)
      ·
        refine ⟨111440106602212896583484081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 297173617605901057555957549 111440106602212896583484081)
        ·
          refine ⟨83580079951659672437613061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111440106602212896583484081 83580079951659672437613061)
          ·
            refine ⟨15671264990936188582052449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 83580079951659672437613061 15671264990936188582052449)
            ·
              refine ⟨11753448743202141436539337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15671264990936188582052449 11753448743202141436539337)
              ·
                refine ⟨8815086557401606077404503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11753448743202141436539337 8815086557401606077404503)
                ·
                  refine ⟨13222629836102409116106755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8815086557401606077404503 13222629836102409116106755)
                  ·
                    refine ⟨19833944754153613674160133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13222629836102409116106755 19833944754153613674160133)
                    ·
                      refine ⟨3718864641403802563905025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19833944754153613674160133 3718864641403802563905025)
                      ·
                        rfl

theorem cell23_7242463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 2, 2, 1, 1, 4].length) (baseStart_7242463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7242463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7242463 prefixEnd_7242463 := by exact prefixLift 7242463
  have htrace : WordTrace (prefixWord ++ tailWord_7242463) baseStart_7242463 baseEnd_7242463 := by
    simpa [prefixWord, tailWord_7242463, baseEnd_7242463] using wordTrace_append hprefix tailTrace_7242463
  have hstable : (prefixWord ++ tailWord_7242463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7242463).length < 2 ^ (prefixWord ++ tailWord_7242463).sum := by decide
  have hdescent : baseEnd_7242463 < baseStart_7242463 := by decide
  rcases family_descends (prefixWord ++ tailWord_7242463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7242484 : List Nat := [2, 6, 1, 1, 2, 1, 1, 2, 2, 3, 2]
def baseStart_7242484 : Nat := 118140960795 + 7242484 * 2 ^ 59
def prefixEnd_7242484 : Nat := 4983230072969 + 3 ^ 40 * 7242484 * 2
def baseEnd_7242484 : Nat := 3718875424497546981742429

theorem tailTrace_7242484 : CollatzResearch.WordTrace tailWord_7242484 prefixEnd_7242484 3718875424497546981742429 := by
  unfold tailWord_7242484
  simp only [CollatzResearch.WordTrace]
  refine ⟨132077546346862430318127253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176103395129149907090836337 132077546346862430318127253)
  ·
    refine ⟨6191134985009176421162215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 132077546346862430318127253 6191134985009176421162215)
    ·
      refine ⟨9286702477513764631743323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6191134985009176421162215 9286702477513764631743323)
      ·
        refine ⟨13930053716270646947614985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9286702477513764631743323 13930053716270646947614985)
        ·
          refine ⟨10447540287202985210711239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13930053716270646947614985 10447540287202985210711239)
          ·
            refine ⟨15671310430804477816066859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10447540287202985210711239 15671310430804477816066859)
            ·
              refine ⟨23506965646206716724100289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15671310430804477816066859 23506965646206716724100289)
              ·
                refine ⟨17630224234655037543075217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23506965646206716724100289 17630224234655037543075217)
                ·
                  refine ⟨13222668175991278157306413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17630224234655037543075217 13222668175991278157306413)
                  ·
                    refine ⟨4958500565996729308989905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13222668175991278157306413 4958500565996729308989905)
                    ·
                      refine ⟨3718875424497546981742429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4958500565996729308989905 3718875424497546981742429)
                      ·
                        rfl

theorem cell23_7242484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 1, 2, 2, 3, 2].length) (baseStart_7242484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7242484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7242484 prefixEnd_7242484 := by exact prefixLift 7242484
  have htrace : WordTrace (prefixWord ++ tailWord_7242484) baseStart_7242484 baseEnd_7242484 := by
    simpa [prefixWord, tailWord_7242484, baseEnd_7242484] using wordTrace_append hprefix tailTrace_7242484
  have hstable : (prefixWord ++ tailWord_7242484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7242484).length < 2 ^ (prefixWord ++ tailWord_7242484).sum := by decide
  have hdescent : baseEnd_7242484 < baseStart_7242484 := by decide
  rcases family_descends (prefixWord ++ tailWord_7242484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7242499 : List Nat := [1, 1, 1, 3, 2, 2, 1, 3, 2, 7]
def baseStart_7242499 : Nat := 118140960795 + 7242499 * 2 ^ 59
def prefixEnd_7242499 : Nat := 4983230072969 + 3 ^ 40 * 7242499 * 2
def baseEnd_7242499 : Nat := 1239627708902454807684953

theorem tailTrace_7242499 : CollatzResearch.WordTrace tailWord_7242499 prefixEnd_7242499 1239627708902454807684953 := by
  unfold tailWord_7242499
  simp only [CollatzResearch.WordTrace]
  refine ⟨264155639788670518198050551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176103759859113678798700367 264155639788670518198050551)
  ·
    refine ⟨396233459683005777297075827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264155639788670518198050551 396233459683005777297075827)
    ·
      refine ⟨594350189524508665945613741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 396233459683005777297075827 594350189524508665945613741)
      ·
        refine ⟨222881321071690749729605153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 594350189524508665945613741 222881321071690749729605153)
        ·
          refine ⟨167160990803768062297203865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 222881321071690749729605153 167160990803768062297203865)
          ·
            refine ⟨125370743102826046722902899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 167160990803768062297203865 125370743102826046722902899)
            ·
              refine ⟨188056114654239070084354349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125370743102826046722902899 188056114654239070084354349)
              ·
                refine ⟨70521042995339651281632881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 188056114654239070084354349 70521042995339651281632881)
                ·
                  refine ⟨52890782246504738461224661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 70521042995339651281632881 52890782246504738461224661)
                  ·
                    refine ⟨1239627708902454807684953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 52890782246504738461224661 1239627708902454807684953)
                    ·
                      rfl

theorem cell23_7242499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 3, 2, 7].length) (baseStart_7242499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7242499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7242499 prefixEnd_7242499 := by exact prefixLift 7242499
  have htrace : WordTrace (prefixWord ++ tailWord_7242499) baseStart_7242499 baseEnd_7242499 := by
    simpa [prefixWord, tailWord_7242499, baseEnd_7242499] using wordTrace_append hprefix tailTrace_7242499
  have hstable : (prefixWord ++ tailWord_7242499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7242499).length < 2 ^ (prefixWord ++ tailWord_7242499).sum := by decide
  have hdescent : baseEnd_7242499 < baseStart_7242499 := by decide
  rcases family_descends (prefixWord ++ tailWord_7242499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7242514 : List Nat := [3, 2, 4, 1, 3, 1, 1, 2, 1, 1, 4]
def baseStart_7242514 : Nat := 118140960795 + 7242514 * 2 ^ 59
def prefixEnd_7242514 : Nat := 4983230072969 + 3 ^ 40 * 7242514 * 2
def baseEnd_7242514 : Nat := 3718890828917181864367291

theorem tailTrace_7242514 : CollatzResearch.WordTrace tailWord_7242514 prefixEnd_7242514 3718890828917181864367291 := by
  unfold tailWord_7242514
  simp only [CollatzResearch.WordTrace]
  refine ⟨66039046720904043939961649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176104124589077450506564397 66039046720904043939961649)
  ·
    refine ⟨49529285040678032954971237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66039046720904043939961649 49529285040678032954971237)
    ·
      refine ⟨9286740945127131179057107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49529285040678032954971237 9286740945127131179057107)
      ·
        refine ⟨13930111417690696768585661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9286740945127131179057107 13930111417690696768585661)
        ·
          refine ⟨5223791781634011288219623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13930111417690696768585661 5223791781634011288219623)
          ·
            refine ⟨7835687672451016932329435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5223791781634011288219623 7835687672451016932329435)
            ·
              refine ⟨11753531508676525398494153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7835687672451016932329435 11753531508676525398494153)
              ·
                refine ⟨8815148631507394048870615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11753531508676525398494153 8815148631507394048870615)
                ·
                  refine ⟨13222722947261091073305923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8815148631507394048870615 13222722947261091073305923)
                  ·
                    refine ⟨19834084420891636609958885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13222722947261091073305923 19834084420891636609958885)
                    ·
                      refine ⟨3718890828917181864367291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19834084420891636609958885 3718890828917181864367291)
                      ·
                        rfl

theorem cell23_7242514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 3, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 3, 1, 1, 2, 1, 1, 4].length) (baseStart_7242514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7242514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7242514 prefixEnd_7242514 := by exact prefixLift 7242514
  have htrace : WordTrace (prefixWord ++ tailWord_7242514) baseStart_7242514 baseEnd_7242514 := by
    simpa [prefixWord, tailWord_7242514, baseEnd_7242514] using wordTrace_append hprefix tailTrace_7242514
  have hstable : (prefixWord ++ tailWord_7242514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7242514).length < 2 ^ (prefixWord ++ tailWord_7242514).sum := by decide
  have hdescent : baseEnd_7242514 < baseStart_7242514 := by decide
  rcases family_descends (prefixWord ++ tailWord_7242514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7242546 : List Nat := [3, 2, 1, 1, 3, 1, 2, 2, 2, 6]
def baseStart_7242546 : Nat := 118140960795 + 7242546 * 2 ^ 59
def prefixEnd_7242546 : Nat := 4983230072969 + 3 ^ 40 * 7242546 * 2
def baseEnd_7242546 : Nat := 1239635753432708579722381

theorem tailTrace_7242546 : CollatzResearch.WordTrace tailWord_7242546 prefixEnd_7242546 1239635753432708579722381 := by
  unfold tailWord_7242546
  simp only [CollatzResearch.WordTrace]
  refine ⟨66039338504875061306252873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176104902679666830150007661 66039338504875061306252873)
  ·
    refine ⟨49529503878656295979689655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66039338504875061306252873 49529503878656295979689655)
    ·
      refine ⟨74294255817984443969534483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49529503878656295979689655 74294255817984443969534483)
      ·
        refine ⟨111441383726976665954301725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74294255817984443969534483 111441383726976665954301725)
        ·
          refine ⟨41790518897616249732863147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 111441383726976665954301725 41790518897616249732863147)
          ·
            refine ⟨62685778346424374599294721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41790518897616249732863147 62685778346424374599294721)
            ·
              refine ⟨47014333759818280949471041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62685778346424374599294721 47014333759818280949471041)
              ·
                refine ⟨35260750319863710712103281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47014333759818280949471041 35260750319863710712103281)
                ·
                  refine ⟨26445562739897783034077461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35260750319863710712103281 26445562739897783034077461)
                  ·
                    refine ⟨1239635753432708579722381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26445562739897783034077461 1239635753432708579722381)
                    ·
                      rfl

theorem cell23_7242546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 2, 2, 2, 6].length) (baseStart_7242546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7242546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7242546 prefixEnd_7242546 := by exact prefixLift 7242546
  have htrace : WordTrace (prefixWord ++ tailWord_7242546) baseStart_7242546 baseEnd_7242546 := by
    simpa [prefixWord, tailWord_7242546, baseEnd_7242546] using wordTrace_append hprefix tailTrace_7242546
  have hstable : (prefixWord ++ tailWord_7242546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7242546).length < 2 ^ (prefixWord ++ tailWord_7242546).sum := by decide
  have hdescent : baseEnd_7242546 < baseStart_7242546 := by decide
  rcases family_descends (prefixWord ++ tailWord_7242546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7242548 : List Nat := [2, 5, 1, 1, 3, 2, 2, 2, 1, 2, 2]
def baseStart_7242548 : Nat := 118140960795 + 7242548 * 2 ^ 59
def prefixEnd_7242548 : Nat := 4983230072969 + 3 ^ 40 * 7242548 * 2
def baseEnd_7242548 : Nat := 3718908287259434731342135

theorem tailTrace_7242548 : CollatzResearch.WordTrace tailWord_7242548 prefixEnd_7242548 3718908287259434731342135 := by
  unfold tailWord_7242548
  simp only [CollatzResearch.WordTrace]
  refine ⟨132078713482746499783292149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176104951310328666377722865 132078713482746499783292149)
  ·
    refine ⟨12382379389007484354683639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 132078713482746499783292149 12382379389007484354683639)
    ·
      refine ⟨18573569083511226532025459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12382379389007484354683639 18573569083511226532025459)
      ·
        refine ⟨27860353625266839798038189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18573569083511226532025459 27860353625266839798038189)
        ·
          refine ⟨10447632609475064924264321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27860353625266839798038189 10447632609475064924264321)
          ·
            refine ⟨7835724457106298693198241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10447632609475064924264321 7835724457106298693198241)
            ·
              refine ⟨5876793342829724019898681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7835724457106298693198241 5876793342829724019898681)
              ·
                refine ⟨4407595007122293014924011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5876793342829724019898681 4407595007122293014924011)
                ·
                  refine ⟨6611392510683439522386017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4407595007122293014924011 6611392510683439522386017)
                  ·
                    refine ⟨4958544383012579641789513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6611392510683439522386017 4958544383012579641789513)
                    ·
                      refine ⟨3718908287259434731342135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4958544383012579641789513 3718908287259434731342135)
                      ·
                        rfl

theorem cell23_7242548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 2, 2, 2, 1, 2, 2].length) (baseStart_7242548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7242548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7242548 prefixEnd_7242548 := by exact prefixLift 7242548
  have htrace : WordTrace (prefixWord ++ tailWord_7242548) baseStart_7242548 baseEnd_7242548 := by
    simpa [prefixWord, tailWord_7242548, baseEnd_7242548] using wordTrace_append hprefix tailTrace_7242548
  have hstable : (prefixWord ++ tailWord_7242548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7242548).length < 2 ^ (prefixWord ++ tailWord_7242548).sum := by decide
  have hdescent : baseEnd_7242548 < baseStart_7242548 := by decide
  rcases family_descends (prefixWord ++ tailWord_7242548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7242643 : List Nat := [1, 1, 1, 2, 1, 2, 1, 4, 4, 4, 2]
def baseStart_7242643 : Nat := 118140960795 + 7242643 * 2 ^ 59
def prefixEnd_7242643 : Nat := 4983230072969 + 3 ^ 40 * 7242643 * 2
def baseEnd_7242643 : Nat := 3718957067921611859654197

theorem tailTrace_7242643 : CollatzResearch.WordTrace tailWord_7242643 prefixEnd_7242643 3718957067921611859654197 := by
  unfold tailWord_7242643
  simp only [CollatzResearch.WordTrace]
  refine ⟨264160891900148830791292583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176107261266765887194195055 264160891900148830791292583)
  ·
    refine ⟨396241337850223246186938875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264160891900148830791292583 396241337850223246186938875)
    ·
      refine ⟨594362006775334869280408313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 396241337850223246186938875 594362006775334869280408313)
      ·
        refine ⟨445771505081501151960306235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 594362006775334869280408313 445771505081501151960306235)
        ·
          refine ⟨668657257622251727940459353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 445771505081501151960306235 668657257622251727940459353)
          ·
            refine ⟨501492943216688795955344515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 668657257622251727940459353 501492943216688795955344515)
            ·
              refine ⟨752239414825033193933016773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 501492943216688795955344515 752239414825033193933016773)
              ·
                refine ⟨141044890279693723862440645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 752239414825033193933016773 141044890279693723862440645)
                ·
                  refine ⟨26445916927442573224207621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 141044890279693723862440645 26445916927442573224207621)
                  ·
                    refine ⟨4958609423895482479538929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26445916927442573224207621 4958609423895482479538929)
                    ·
                      refine ⟨3718957067921611859654197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4958609423895482479538929 3718957067921611859654197)
                      ·
                        rfl

theorem cell23_7242643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 4, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 4, 4, 4, 2].length) (baseStart_7242643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7242643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7242643 prefixEnd_7242643 := by exact prefixLift 7242643
  have htrace : WordTrace (prefixWord ++ tailWord_7242643) baseStart_7242643 baseEnd_7242643 := by
    simpa [prefixWord, tailWord_7242643, baseEnd_7242643] using wordTrace_append hprefix tailTrace_7242643
  have hstable : (prefixWord ++ tailWord_7242643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7242643).length < 2 ^ (prefixWord ++ tailWord_7242643).sum := by decide
  have hdescent : baseEnd_7242643 < baseStart_7242643 := by decide
  rcases family_descends (prefixWord ++ tailWord_7242643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7242656 : List Nat := [2, 1, 1, 4, 1, 1, 2, 1, 1, 3, 6]
def baseStart_7242656 : Nat := 118140960795 + 7242656 * 2 ^ 59
def prefixEnd_7242656 : Nat := 4983230072969 + 3 ^ 40 * 7242656 * 2
def baseEnd_7242656 : Nat := 3718963743170120308791637

theorem tailTrace_7242656 : CollatzResearch.WordTrace tailWord_7242656 prefixEnd_7242656 3718963743170120308791637 := by
  unfold tailWord_7242656
  simp only [CollatzResearch.WordTrace]
  refine ⟨132080683024550867005757911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176107577366067822674343881 132080683024550867005757911)
  ·
    refine ⟨198121024536826300508636867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132080683024550867005757911 198121024536826300508636867)
    ·
      refine ⟨297181536805239450762955301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198121024536826300508636867 297181536805239450762955301)
      ·
        refine ⟨55721538150982397018054119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 297181536805239450762955301 55721538150982397018054119)
        ·
          refine ⟨83582307226473595527081179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55721538150982397018054119 83582307226473595527081179)
          ·
            refine ⟨125373460839710393290621769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83582307226473595527081179 125373460839710393290621769)
            ·
              refine ⟨94030095629782794967966327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 125373460839710393290621769 94030095629782794967966327)
              ·
                refine ⟨141045143444674192451949491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94030095629782794967966327 141045143444674192451949491)
                ·
                  refine ⟨211567715167011288677924237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 141045143444674192451949491 211567715167011288677924237)
                  ·
                    refine ⟨79337893187629233254221589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 211567715167011288677924237 79337893187629233254221589)
                    ·
                      refine ⟨3718963743170120308791637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 79337893187629233254221589 3718963743170120308791637)
                      ·
                        rfl

theorem cell23_7242656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 1, 1, 3, 6].length) (baseStart_7242656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7242656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7242656 prefixEnd_7242656 := by exact prefixLift 7242656
  have htrace : WordTrace (prefixWord ++ tailWord_7242656) baseStart_7242656 baseEnd_7242656 := by
    simpa [prefixWord, tailWord_7242656, baseEnd_7242656] using wordTrace_append hprefix tailTrace_7242656
  have hstable : (prefixWord ++ tailWord_7242656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7242656).length < 2 ^ (prefixWord ++ tailWord_7242656).sum := by decide
  have hdescent : baseEnd_7242656 < baseStart_7242656 := by decide
  rcases family_descends (prefixWord ++ tailWord_7242656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7242773 : List Nat := [1, 3, 2, 1, 4, 2, 10]
def baseStart_7242773 : Nat := 118140960795 + 7242773 * 2 ^ 59
def prefixEnd_7242773 : Nat := 4983230072969 + 3 ^ 40 * 7242773 * 2
def baseEnd_7242773 : Nat := 45913874326008596926279

theorem tailTrace_7242773 : CollatzResearch.WordTrace tailWord_7242773 prefixEnd_7242773 45913874326008596926279 := by
  unfold tailWord_7242773
  simp only [CollatzResearch.WordTrace]
  refine ⟨264165633389677862993524973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176110422259785241995683315 264165633389677862993524973)
  ·
    refine ⟨99062112521129198622571865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 264165633389677862993524973 99062112521129198622571865)
    ·
      refine ⟨74296584390846898966928899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99062112521129198622571865 74296584390846898966928899)
      ·
        refine ⟨111444876586270348450393349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74296584390846898966928899 111444876586270348450393349)
        ·
          refine ⟨20895914359925690334448753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 111444876586270348450393349 20895914359925690334448753)
          ·
            refine ⟨15671935769944267750836565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20895914359925690334448753 15671935769944267750836565)
            ·
              refine ⟨45913874326008596926279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 15671935769944267750836565 45913874326008596926279)
              ·
                rfl

theorem cell23_7242773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 10].length) (baseStart_7242773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7242773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7242773 prefixEnd_7242773 := by exact prefixLift 7242773
  have htrace : WordTrace (prefixWord ++ tailWord_7242773) baseStart_7242773 baseEnd_7242773 := by
    simpa [prefixWord, tailWord_7242773, baseEnd_7242773] using wordTrace_append hprefix tailTrace_7242773
  have hstable : (prefixWord ++ tailWord_7242773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7242773).length < 2 ^ (prefixWord ++ tailWord_7242773).sum := by decide
  have hdescent : baseEnd_7242773 < baseStart_7242773 := by decide
  rcases family_descends (prefixWord ++ tailWord_7242773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7242794 : List Nat := [3, 1, 4, 1, 4, 1, 1, 1, 1, 6]
def baseStart_7242794 : Nat := 118140960795 + 7242794 * 2 ^ 59
def prefixEnd_7242794 : Nat := 4983230072969 + 3 ^ 40 * 7242794 * 2
def baseEnd_7242794 : Nat := 1239678201166813589622001

theorem tailTrace_7242794 : CollatzResearch.WordTrace tailWord_7242794 prefixEnd_7242794 1239678201166813589622001 := by
  unfold tailWord_7242794
  simp only [CollatzResearch.WordTrace]
  refine ⟨66041599830650445895009859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176110932881734522386692957 66041599830650445895009859)
  ·
    refine ⟨99062399745975668842514789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66041599830650445895009859 99062399745975668842514789)
    ·
      refine ⟨18574199952370437907971523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 99062399745975668842514789 18574199952370437907971523)
      ·
        refine ⟨27861299928555656861957285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18574199952370437907971523 27861299928555656861957285)
        ·
          refine ⟨5223993736604185661616991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27861299928555656861957285 5223993736604185661616991)
          ·
            refine ⟨7835990604906278492425487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5223993736604185661616991 7835990604906278492425487)
            ·
              refine ⟨11753985907359417738638231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7835990604906278492425487 11753985907359417738638231)
              ·
                refine ⟨17630978861039126607957347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11753985907359417738638231 17630978861039126607957347)
                ·
                  refine ⟨26446468291558689911936021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17630978861039126607957347 26446468291558689911936021)
                  ·
                    refine ⟨1239678201166813589622001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26446468291558689911936021 1239678201166813589622001)
                    ·
                      rfl

theorem cell23_7242794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 4, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 4, 1, 1, 1, 1, 6].length) (baseStart_7242794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7242794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7242794 prefixEnd_7242794 := by exact prefixLift 7242794
  have htrace : WordTrace (prefixWord ++ tailWord_7242794) baseStart_7242794 baseEnd_7242794 := by
    simpa [prefixWord, tailWord_7242794, baseEnd_7242794] using wordTrace_append hprefix tailTrace_7242794
  have hstable : (prefixWord ++ tailWord_7242794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7242794).length < 2 ^ (prefixWord ++ tailWord_7242794).sum := by decide
  have hdescent : baseEnd_7242794 < baseStart_7242794 := by decide
  rcases family_descends (prefixWord ++ tailWord_7242794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7242804 : List Nat := [2, 5, 1, 2, 1, 1, 1, 4, 1, 2, 3]
def baseStart_7242804 : Nat := 118140960795 + 7242804 * 2 ^ 59
def prefixEnd_7242804 : Nat := 4983230072969 + 3 ^ 40 * 7242804 * 2
def baseEnd_7242804 : Nat := 3719039738306985729740957

theorem tailTrace_7242804 : CollatzResearch.WordTrace tailWord_7242804 prefixEnd_7242804 3719039738306985729740957 := by
  unfold tailWord_7242804
  simp only [CollatzResearch.WordTrace]
  refine ⟨132083382026282777643951733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176111176035043703525268977 132083382026282777643951733)
  ·
    refine ⟨12382817064964010404120475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 132083382026282777643951733 12382817064964010404120475)
    ·
      refine ⟨18574225597446015606180713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12382817064964010404120475 18574225597446015606180713)
      ·
        refine ⟨13930669198084511704635535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18574225597446015606180713 13930669198084511704635535)
        ·
          refine ⟨20896003797126767556953303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13930669198084511704635535 20896003797126767556953303)
          ·
            refine ⟨31344005695690151335429955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20896003797126767556953303 31344005695690151335429955)
            ·
              refine ⟨47016008543535227003144933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31344005695690151335429955 47016008543535227003144933)
              ·
                refine ⟨8815501601912855063089675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47016008543535227003144933 8815501601912855063089675)
                ·
                  refine ⟨13223252402869282594634513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8815501601912855063089675 13223252402869282594634513)
                  ·
                    refine ⟨9917439302151961945975885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13223252402869282594634513 9917439302151961945975885)
                    ·
                      refine ⟨3719039738306985729740957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9917439302151961945975885 3719039738306985729740957)
                      ·
                        rfl

theorem cell23_7242804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 1, 4, 1, 2, 3].length) (baseStart_7242804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7242804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7242804 prefixEnd_7242804 := by exact prefixLift 7242804
  have htrace : WordTrace (prefixWord ++ tailWord_7242804) baseStart_7242804 baseEnd_7242804 := by
    simpa [prefixWord, tailWord_7242804, baseEnd_7242804] using wordTrace_append hprefix tailTrace_7242804
  have hstable : (prefixWord ++ tailWord_7242804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7242804).length < 2 ^ (prefixWord ++ tailWord_7242804).sum := by decide
  have hdescent : baseEnd_7242804 < baseStart_7242804 := by decide
  rcases family_descends (prefixWord ++ tailWord_7242804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7242833 : List Nat := [1, 2, 2, 1, 3, 1, 2, 1, 4, 6]
def baseStart_7242833 : Nat := 118140960795 + 7242833 * 2 ^ 59
def prefixEnd_7242833 : Nat := 4983230072969 + 3 ^ 40 * 7242833 * 2
def baseEnd_7242833 : Nat := 1239684876415322038759441

theorem tailTrace_7242833 : CollatzResearch.WordTrace tailWord_7242833 prefixEnd_7242833 1239684876415322038759441 := by
  unfold tailWord_7242833
  simp only [CollatzResearch.WordTrace]
  refine ⟨264167821769460493240709153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176111881179640328827139435 264167821769460493240709153)
  ·
    refine ⟨198125866327095369930531865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 264167821769460493240709153 198125866327095369930531865)
    ·
      refine ⟨148594399745321527447898899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 198125866327095369930531865 148594399745321527447898899)
      ·
        refine ⟨222891599617982291171848349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148594399745321527447898899 222891599617982291171848349)
        ·
          refine ⟨83584349856743359189443131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 222891599617982291171848349 83584349856743359189443131)
          ·
            refine ⟨125376524785115038784164697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83584349856743359189443131 125376524785115038784164697)
            ·
              refine ⟨94032393588836279088123523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 125376524785115038784164697 94032393588836279088123523)
              ·
                refine ⟨141048590383254418632185285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94032393588836279088123523 141048590383254418632185285)
                ·
                  refine ⟨26446610696860203493534741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 141048590383254418632185285 26446610696860203493534741)
                  ·
                    refine ⟨1239684876415322038759441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26446610696860203493534741 1239684876415322038759441)
                    ·
                      rfl

theorem cell23_7242833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 1, 4, 6].length) (baseStart_7242833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7242833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7242833 prefixEnd_7242833 := by exact prefixLift 7242833
  have htrace : WordTrace (prefixWord ++ tailWord_7242833) baseStart_7242833 baseEnd_7242833 := by
    simpa [prefixWord, tailWord_7242833, baseEnd_7242833] using wordTrace_append hprefix tailTrace_7242833
  have hstable : (prefixWord ++ tailWord_7242833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7242833).length < 2 ^ (prefixWord ++ tailWord_7242833).sum := by decide
  have hdescent : baseEnd_7242833 < baseStart_7242833 := by decide
  rcases family_descends (prefixWord ++ tailWord_7242833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7242861 : List Nat := [1, 5, 1, 1, 2, 4, 1, 2, 1, 3, 2]
def baseStart_7242861 : Nat := 118140960795 + 7242861 * 2 ^ 59
def prefixEnd_7242861 : Nat := 4983230072969 + 3 ^ 40 * 7242861 * 2
def baseEnd_7242861 : Nat := 3719069006704292006728195

theorem tailTrace_7242861 : CollatzResearch.WordTrace tailWord_7242861 prefixEnd_7242861 3719069006704292006728195 := by
  unfold tailWord_7242861
  simp only [CollatzResearch.WordTrace]
  refine ⟨264168843013359054022728437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176112562008906036015152291 264168843013359054022728437)
  ·
    refine ⟨24765829032502411314630791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 264168843013359054022728437 24765829032502411314630791)
    ·
      refine ⟨37148743548753616971946187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24765829032502411314630791 37148743548753616971946187)
      ·
        refine ⟨55723115323130425457919281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37148743548753616971946187 55723115323130425457919281)
        ·
          refine ⟨41792336492347819093439461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55723115323130425457919281 41792336492347819093439461)
          ·
            refine ⟨7836063092315216080019899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41792336492347819093439461 7836063092315216080019899)
            ·
              refine ⟨11754094638472824120029849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7836063092315216080019899 11754094638472824120029849)
              ·
                refine ⟨8815570978854618090022387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11754094638472824120029849 8815570978854618090022387)
                ·
                  refine ⟨13223356468281927135033581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8815570978854618090022387 13223356468281927135033581)
                  ·
                    refine ⟨4958758675605722675637593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13223356468281927135033581 4958758675605722675637593)
                    ·
                      refine ⟨3719069006704292006728195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4958758675605722675637593 3719069006704292006728195)
                      ·
                        rfl

theorem cell23_7242861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 4, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 4, 1, 2, 1, 3, 2].length) (baseStart_7242861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7242861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7242861 prefixEnd_7242861 := by exact prefixLift 7242861
  have htrace : WordTrace (prefixWord ++ tailWord_7242861) baseStart_7242861 baseEnd_7242861 := by
    simpa [prefixWord, tailWord_7242861, baseEnd_7242861] using wordTrace_append hprefix tailTrace_7242861
  have hstable : (prefixWord ++ tailWord_7242861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7242861).length < 2 ^ (prefixWord ++ tailWord_7242861).sum := by decide
  have hdescent : baseEnd_7242861 < baseStart_7242861 := by decide
  rcases family_descends (prefixWord ++ tailWord_7242861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7242863 : List Nat := [1, 1, 2, 1, 3, 3, 2, 1, 9]
def baseStart_7242863 : Nat := 118140960795 + 7242863 * 2 ^ 59
def prefixEnd_7242863 : Nat := 4983230072969 + 3 ^ 40 * 7242863 * 2
def baseEnd_7242863 : Nat := 413230003740622333211465

theorem tailTrace_7242863 : CollatzResearch.WordTrace tailWord_7242863 prefixEnd_7242863 413230003740622333211465 := by
  unfold tailWord_7242863
  simp only [CollatzResearch.WordTrace]
  refine ⟨264168915959351808364301243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176112610639567872242867495 264168915959351808364301243)
  ·
    refine ⟨396253373939027712546451865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264168915959351808364301243 396253373939027712546451865)
    ·
      refine ⟨297190030454270784409838899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 396253373939027712546451865 297190030454270784409838899)
      ·
        refine ⟨445785045681406176614758349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 297190030454270784409838899 445785045681406176614758349)
        ·
          refine ⟨167169392130527316230534381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 445785045681406176614758349 167169392130527316230534381)
          ·
            refine ⟨62688522048947743586450393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 167169392130527316230534381 62688522048947743586450393)
            ·
              refine ⟨47016391536710807689837795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62688522048947743586450393 47016391536710807689837795)
              ·
                refine ⟨70524587305066211534756693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47016391536710807689837795 70524587305066211534756693)
                ·
                  refine ⟨413230003740622333211465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 70524587305066211534756693 413230003740622333211465)
                  ·
                    rfl

theorem cell23_7242863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 2, 1, 9].length) (baseStart_7242863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7242863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7242863 prefixEnd_7242863 := by exact prefixLift 7242863
  have htrace : WordTrace (prefixWord ++ tailWord_7242863) baseStart_7242863 baseEnd_7242863 := by
    simpa [prefixWord, tailWord_7242863, baseEnd_7242863] using wordTrace_append hprefix tailTrace_7242863
  have hstable : (prefixWord ++ tailWord_7242863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7242863).length < 2 ^ (prefixWord ++ tailWord_7242863).sum := by decide
  have hdescent : baseEnd_7242863 < baseStart_7242863 := by decide
  rcases family_descends (prefixWord ++ tailWord_7242863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7243000 : List Nat := [2, 1, 2, 1, 1, 2, 1, 1, 7, 5]
def baseStart_7243000 : Nat := 118140960795 + 7243000 * 2 ^ 59
def prefixEnd_7243000 : Nat := 4983230072969 + 3 ^ 40 * 7243000 * 2
def baseEnd_7243000 : Nat := 1239713460171755654296685

theorem tailTrace_7243000 : CollatzResearch.WordTrace tailWord_7243000 prefixEnd_7243000 1239713460171755654296685 := by
  unfold tailWord_7243000
  simp only [CollatzResearch.WordTrace]
  refine ⟨132086956379927740381019227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176115941839903653841358969 132086956379927740381019227)
  ·
    refine ⟨198130434569891610571528841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132086956379927740381019227 198130434569891610571528841)
    ·
      refine ⟨148597825927418707928646631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 198130434569891610571528841 148597825927418707928646631)
      ·
        refine ⟨222896738891128061892969947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148597825927418707928646631 222896738891128061892969947)
        ·
          refine ⟨334345108336692092839454921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 222896738891128061892969947 334345108336692092839454921)
          ·
            refine ⟨250758831252519069629591191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 334345108336692092839454921 250758831252519069629591191)
            ·
              refine ⟨376138246878778604444386787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 250758831252519069629591191 376138246878778604444386787)
              ·
                refine ⟨564207370318167906666580181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 376138246878778604444386787 564207370318167906666580181)
                ·
                  refine ⟨13223610241832060312497973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 564207370318167906666580181 13223610241832060312497973)
                  ·
                    refine ⟨1239713460171755654296685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13223610241832060312497973 1239713460171755654296685)
                    ·
                      rfl

theorem cell23_7243000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 1, 7, 5].length) (baseStart_7243000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7243000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7243000 prefixEnd_7243000 := by exact prefixLift 7243000
  have htrace : WordTrace (prefixWord ++ tailWord_7243000) baseStart_7243000 baseEnd_7243000 := by
    simpa [prefixWord, tailWord_7243000, baseEnd_7243000] using wordTrace_append hprefix tailTrace_7243000
  have hstable : (prefixWord ++ tailWord_7243000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7243000).length < 2 ^ (prefixWord ++ tailWord_7243000).sum := by decide
  have hdescent : baseEnd_7243000 < baseStart_7243000 := by decide
  rcases family_descends (prefixWord ++ tailWord_7243000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7243034 : List Nat := [3, 1, 1, 3, 3, 1, 3, 2, 1, 5]
def baseStart_7243034 : Nat := 118140960795 + 7243034 * 2 ^ 59
def prefixEnd_7243034 : Nat := 4983230072969 + 3 ^ 40 * 7243034 * 2
def baseEnd_7243034 : Nat := 1239719279619173276621633

theorem tailTrace_7243034 : CollatzResearch.WordTrace tailWord_7243034 prefixEnd_7243034 1239719279619173276621633 := by
  unfold tailWord_7243034
  simp only [CollatzResearch.WordTrace]
  refine ⟨66043788210433076142194039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176116768561154869712517437 66043788210433076142194039)
  ·
    refine ⟨99065682315649614213291059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66043788210433076142194039 99065682315649614213291059)
    ·
      refine ⟨148598523473474421319936589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99065682315649614213291059 148598523473474421319936589)
      ·
        refine ⟨55724446302552907994976221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 148598523473474421319936589 55724446302552907994976221)
        ·
          refine ⟨20896667363457340498116083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55724446302552907994976221 20896667363457340498116083)
          ·
            refine ⟨31345001045186010747174125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20896667363457340498116083 31345001045186010747174125)
            ·
              refine ⟨11754375391944754030190297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31345001045186010747174125 11754375391944754030190297)
              ·
                refine ⟨8815781543958565522642723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11754375391944754030190297 8815781543958565522642723)
                ·
                  refine ⟨13223672315937848283964085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8815781543958565522642723 13223672315937848283964085)
                  ·
                    refine ⟨1239719279619173276621633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13223672315937848283964085 1239719279619173276621633)
                    ·
                      rfl

theorem cell23_7243034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 3, 2, 1, 5].length) (baseStart_7243034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7243034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7243034 prefixEnd_7243034 := by exact prefixLift 7243034
  have htrace : WordTrace (prefixWord ++ tailWord_7243034) baseStart_7243034 baseEnd_7243034 := by
    simpa [prefixWord, tailWord_7243034, baseEnd_7243034] using wordTrace_append hprefix tailTrace_7243034
  have hstable : (prefixWord ++ tailWord_7243034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7243034).length < 2 ^ (prefixWord ++ tailWord_7243034).sum := by decide
  have hdescent : baseEnd_7243034 < baseStart_7243034 := by decide
  rcases family_descends (prefixWord ++ tailWord_7243034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7243084 : List Nat := [2, 2, 1, 3, 2, 3, 2, 1, 1, 2, 4]
def baseStart_7243084 : Nat := 118140960795 + 7243084 * 2 ^ 59
def prefixEnd_7243084 : Nat := 4983230072969 + 3 ^ 40 * 7243084 * 2
def baseEnd_7243084 : Nat := 3719183512890244634239669

theorem tailTrace_7243084 : CollatzResearch.WordTrace tailWord_7243084 prefixEnd_7243084 3719183512890244634239669 := by
  unfold tailWord_7243084
  simp only [CollatzResearch.WordTrace]
  refine ⟨132088488245775581554048153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176117984327700775405397537 132088488245775581554048153)
  ·
    refine ⟨99066366184331686165536115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132088488245775581554048153 99066366184331686165536115)
    ·
      refine ⟨148599549276497529248304173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99066366184331686165536115 148599549276497529248304173)
      ·
        refine ⟨55724830978686573468114065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 148599549276497529248304173 55724830978686573468114065)
        ·
          refine ⟨41793623234014930101085549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55724830978686573468114065 41793623234014930101085549)
          ·
            refine ⟨15672608712755598787907081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41793623234014930101085549 15672608712755598787907081)
            ·
              refine ⟨11754456534566699090930311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15672608712755598787907081 11754456534566699090930311)
              ·
                refine ⟨17631684801850048636395467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11754456534566699090930311 17631684801850048636395467)
                ·
                  refine ⟨26447527202775072954593201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17631684801850048636395467 26447527202775072954593201)
                  ·
                    refine ⟨19835645402081304715944901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26447527202775072954593201 19835645402081304715944901)
                    ·
                      refine ⟨3719183512890244634239669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19835645402081304715944901 3719183512890244634239669)
                      ·
                        rfl

theorem cell23_7243084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 2, 1, 1, 2, 4].length) (baseStart_7243084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7243084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7243084 prefixEnd_7243084 := by exact prefixLift 7243084
  have htrace : WordTrace (prefixWord ++ tailWord_7243084) baseStart_7243084 baseEnd_7243084 := by
    simpa [prefixWord, tailWord_7243084, baseEnd_7243084] using wordTrace_append hprefix tailTrace_7243084
  have hstable : (prefixWord ++ tailWord_7243084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7243084).length < 2 ^ (prefixWord ++ tailWord_7243084).sum := by decide
  have hdescent : baseEnd_7243084 < baseStart_7243084 := by decide
  rcases family_descends (prefixWord ++ tailWord_7243084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7243104 : List Nat := [2, 1, 1, 3, 4, 1, 2, 2, 1, 3, 3]
def baseStart_7243104 : Nat := 118140960795 + 7243104 * 2 ^ 59
def prefixEnd_7243104 : Nat := 4983230072969 + 3 ^ 40 * 7243104 * 2
def baseEnd_7243104 : Nat := 3719193782503334555989577

theorem tailTrace_7243104 : CollatzResearch.WordTrace tailWord_7243104 prefixEnd_7243104 3719193782503334555989577 := by
  unfold tailWord_7243104
  simp only [CollatzResearch.WordTrace]
  refine ⟨132088852975739353261912183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176118470634319137682549577 132088852975739353261912183)
  ·
    refine ⟨198133279463609029892868275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132088852975739353261912183 198133279463609029892868275)
    ·
      refine ⟨297199919195413544839302413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198133279463609029892868275 297199919195413544839302413)
      ·
        refine ⟨111449969698280079314738405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 297199919195413544839302413 111449969698280079314738405)
        ·
          refine ⟨20896869318427514871513451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 111449969698280079314738405 20896869318427514871513451)
          ·
            refine ⟨31345303977641272307270177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20896869318427514871513451 31345303977641272307270177)
            ·
              refine ⟨23508977983230954230452633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31345303977641272307270177 23508977983230954230452633)
              ·
                refine ⟨17631733487423215672839475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23508977983230954230452633 17631733487423215672839475)
                ·
                  refine ⟨26447600231134823509259213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17631733487423215672839475 26447600231134823509259213)
                  ·
                    refine ⟨9917850086675558815972205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26447600231134823509259213 9917850086675558815972205)
                    ·
                      refine ⟨3719193782503334555989577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9917850086675558815972205 3719193782503334555989577)
                      ·
                        rfl

theorem cell23_7243104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 2, 2, 1, 3, 3].length) (baseStart_7243104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7243104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7243104 prefixEnd_7243104 := by exact prefixLift 7243104
  have htrace : WordTrace (prefixWord ++ tailWord_7243104) baseStart_7243104 baseEnd_7243104 := by
    simpa [prefixWord, tailWord_7243104, baseEnd_7243104] using wordTrace_append hprefix tailTrace_7243104
  have hstable : (prefixWord ++ tailWord_7243104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7243104).length < 2 ^ (prefixWord ++ tailWord_7243104).sum := by decide
  have hdescent : baseEnd_7243104 < baseStart_7243104 := by decide
  rcases family_descends (prefixWord ++ tailWord_7243104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7243108 : List Nat := [2, 3, 1, 1, 3, 4, 2, 1, 1, 2, 3]
def baseStart_7243108 : Nat := 118140960795 + 7243108 * 2 ^ 59
def prefixEnd_7243108 : Nat := 4983230072969 + 3 ^ 40 * 7243108 * 2
def baseEnd_7243108 : Nat := 3719195836425952540339559

theorem tailTrace_7243108 : CollatzResearch.WordTrace tailWord_7243108 prefixEnd_7243108 3719195836425952540339559 := by
  unfold tailWord_7243108
  simp only [CollatzResearch.WordTrace]
  refine ⟨132088925921732107603484989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176118567895642810137979985 132088925921732107603484989)
  ·
    refine ⟨49533347220649540351306871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132088925921732107603484989 49533347220649540351306871)
    ·
      refine ⟨74300020830974310526960307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49533347220649540351306871 74300020830974310526960307)
      ·
        refine ⟨111450031246461465790440461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74300020830974310526960307 111450031246461465790440461)
        ·
          refine ⟨41793761717423049671415173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 111450031246461465790440461 41793761717423049671415173)
          ·
            refine ⟨7836330322016821813390345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41793761717423049671415173 7836330322016821813390345)
            ·
              refine ⟨5877247741512616360042759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7836330322016821813390345 5877247741512616360042759)
              ·
                refine ⟨8815871612268924540064139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5877247741512616360042759 8815871612268924540064139)
                ·
                  refine ⟨13223807418403386810096209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8815871612268924540064139 13223807418403386810096209)
                  ·
                    refine ⟨9917855563802540107572157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13223807418403386810096209 9917855563802540107572157)
                    ·
                      refine ⟨3719195836425952540339559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9917855563802540107572157 3719195836425952540339559)
                      ·
                        rfl

theorem cell23_7243108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 4, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 4, 2, 1, 1, 2, 3].length) (baseStart_7243108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7243108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7243108 prefixEnd_7243108 := by exact prefixLift 7243108
  have htrace : WordTrace (prefixWord ++ tailWord_7243108) baseStart_7243108 baseEnd_7243108 := by
    simpa [prefixWord, tailWord_7243108, baseEnd_7243108] using wordTrace_append hprefix tailTrace_7243108
  have hstable : (prefixWord ++ tailWord_7243108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7243108).length < 2 ^ (prefixWord ++ tailWord_7243108).sum := by decide
  have hdescent : baseEnd_7243108 < baseStart_7243108 := by decide
  rcases family_descends (prefixWord ++ tailWord_7243108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7243121 : List Nat := [1, 2, 2, 2, 1, 2, 5, 2, 2, 1, 3]
def baseStart_7243121 : Nat := 118140960795 + 7243121 * 2 ^ 59
def prefixEnd_7243121 : Nat := 4983230072969 + 3 ^ 40 * 7243121 * 2
def baseEnd_7243121 : Nat := 3719202511674460989476999

theorem tailTrace_7243121 : CollatzResearch.WordTrace tailWord_7243121 prefixEnd_7243121 3719202511674460989476999 := by
  unfold tailWord_7243121
  simp only [CollatzResearch.WordTrace]
  refine ⟨264178325992417118427193217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176118883994944745618128811 264178325992417118427193217)
  ·
    refine ⟨198133744494312838820394913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 264178325992417118427193217 198133744494312838820394913)
    ·
      refine ⟨148600308370734629115296185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 198133744494312838820394913 148600308370734629115296185)
      ·
        refine ⟨111450231278050971836472139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148600308370734629115296185 111450231278050971836472139)
        ·
          refine ⟨167175346917076457754708209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111450231278050971836472139 167175346917076457754708209)
          ·
            refine ⟨125381510187807343316031157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 167175346917076457754708209 125381510187807343316031157)
            ·
              refine ⟨11754516580106938435877921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 125381510187807343316031157 11754516580106938435877921)
              ·
                refine ⟨8815887435080203826908441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11754516580106938435877921 8815887435080203826908441)
                ·
                  refine ⟨6611915576310152870181331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8815887435080203826908441 6611915576310152870181331)
                  ·
                    refine ⟨9917873364465229305271997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6611915576310152870181331 9917873364465229305271997)
                    ·
                      refine ⟨3719202511674460989476999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9917873364465229305271997 3719202511674460989476999)
                      ·
                        rfl

theorem cell23_7243121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 5, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 5, 2, 2, 1, 3].length) (baseStart_7243121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7243121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7243121 prefixEnd_7243121 := by exact prefixLift 7243121
  have htrace : WordTrace (prefixWord ++ tailWord_7243121) baseStart_7243121 baseEnd_7243121 := by
    simpa [prefixWord, tailWord_7243121, baseEnd_7243121] using wordTrace_append hprefix tailTrace_7243121
  have hstable : (prefixWord ++ tailWord_7243121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7243121).length < 2 ^ (prefixWord ++ tailWord_7243121).sum := by decide
  have hdescent : baseEnd_7243121 < baseStart_7243121 := by decide
  rcases family_descends (prefixWord ++ tailWord_7243121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7243138 : List Nat := [3, 4, 2, 1, 1, 1, 3, 1, 1, 3, 3]
def baseStart_7243138 : Nat := 118140960795 + 7243138 * 2 ^ 59
def prefixEnd_7243138 : Nat := 4983230072969 + 3 ^ 40 * 7243138 * 2
def baseEnd_7243138 : Nat := 3719211240845587422964421

theorem tailTrace_7243138 : CollatzResearch.WordTrace tailWord_7243138 prefixEnd_7243138 3719211240845587422964421 := by
  unfold tailWord_7243138
  simp only [CollatzResearch.WordTrace]
  refine ⟨66044736508338882582640517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176119297355570353553708045 66044736508338882582640517)
  ·
    refine ⟨12383388095313540484245097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 66044736508338882582640517 12383388095313540484245097)
    ·
      refine ⟨9287541071485155363183823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12383388095313540484245097 9287541071485155363183823)
      ·
        refine ⟨13931311607227733044775735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9287541071485155363183823 13931311607227733044775735)
        ·
          refine ⟨20896967410841599567163603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13931311607227733044775735 20896967410841599567163603)
          ·
            refine ⟨31345451116262399350745405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20896967410841599567163603 31345451116262399350745405)
            ·
              refine ⟨11754544168598399756529527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31345451116262399350745405 11754544168598399756529527)
              ·
                refine ⟨17631816252897599634794291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11754544168598399756529527 17631816252897599634794291)
                ·
                  refine ⟨26447724379346399452191437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17631816252897599634794291 26447724379346399452191437)
                  ·
                    refine ⟨9917896642254899794571789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26447724379346399452191437 9917896642254899794571789)
                    ·
                      refine ⟨3719211240845587422964421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9917896642254899794571789 3719211240845587422964421)
                      ·
                        rfl

theorem cell23_7243138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 3, 1, 1, 3, 3].length) (baseStart_7243138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7243138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7243138 prefixEnd_7243138 := by exact prefixLift 7243138
  have htrace : WordTrace (prefixWord ++ tailWord_7243138) baseStart_7243138 baseEnd_7243138 := by
    simpa [prefixWord, tailWord_7243138, baseEnd_7243138] using wordTrace_append hprefix tailTrace_7243138
  have hstable : (prefixWord ++ tailWord_7243138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7243138).length < 2 ^ (prefixWord ++ tailWord_7243138).sum := by decide
  have hdescent : baseEnd_7243138 < baseStart_7243138 := by decide
  rcases family_descends (prefixWord ++ tailWord_7243138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7243147 : List Nat := [1, 1, 1, 1, 4, 3, 2, 2, 2, 1, 5]
def baseStart_7243147 : Nat := 118140960795 + 7243147 * 2 ^ 59
def prefixEnd_7243147 : Nat := 4983230072969 + 3 ^ 40 * 7243147 * 2
def baseEnd_7243147 : Nat := 3719215862171477887751879

theorem tailTrace_7243147 : CollatzResearch.WordTrace tailWord_7243147 prefixEnd_7243147 3719215862171477887751879 := by
  unfold tailWord_7243147
  simp only [CollatzResearch.WordTrace]
  refine ⟨264179274290322924867639695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176119516193548616578426463 264179274290322924867639695)
  ·
    refine ⟨396268911435484387301459543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264179274290322924867639695 396268911435484387301459543)
    ·
      refine ⟨594403367153226580952189315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 396268911435484387301459543 594403367153226580952189315)
      ·
        refine ⟨891605050729839871428283973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 594403367153226580952189315 891605050729839871428283973)
        ·
          refine ⟨167175947011844975892803245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 891605050729839871428283973 167175947011844975892803245)
          ·
            refine ⟨62690980129441865959801217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 167175947011844975892803245 62690980129441865959801217)
            ·
              refine ⟨47018235097081399469850913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62690980129441865959801217 47018235097081399469850913)
              ·
                refine ⟨35263676322811049602388185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47018235097081399469850913 35263676322811049602388185)
                ·
                  refine ⟨26447757242108287201791139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35263676322811049602388185 26447757242108287201791139)
                  ·
                    refine ⟨39671635863162430802686709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26447757242108287201791139 39671635863162430802686709)
                    ·
                      refine ⟨3719215862171477887751879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39671635863162430802686709 3719215862171477887751879)
                      ·
                        rfl

theorem cell23_7243147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 2, 2, 2, 1, 5].length) (baseStart_7243147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7243147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7243147 prefixEnd_7243147 := by exact prefixLift 7243147
  have htrace : WordTrace (prefixWord ++ tailWord_7243147) baseStart_7243147 baseEnd_7243147 := by
    simpa [prefixWord, tailWord_7243147, baseEnd_7243147] using wordTrace_append hprefix tailTrace_7243147
  have hstable : (prefixWord ++ tailWord_7243147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7243147).length < 2 ^ (prefixWord ++ tailWord_7243147).sum := by decide
  have hdescent : baseEnd_7243147 < baseStart_7243147 := by decide
  rcases family_descends (prefixWord ++ tailWord_7243147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7243157 : List Nat := [1, 3, 2, 1, 1, 2, 2, 2, 1, 4, 4]
def baseStart_7243157 : Nat := 118140960795 + 7243157 * 2 ^ 59
def prefixEnd_7243157 : Nat := 4983230072969 + 3 ^ 40 * 7243157 * 2
def baseEnd_7243157 : Nat := 3719220996978022848626833

theorem tailTrace_7243157 : CollatzResearch.WordTrace tailWord_7243157 prefixEnd_7243157 3719220996978022848626833 := by
  unfold tailWord_7243157
  simp only [CollatzResearch.WordTrace]
  refine ⟨264179639020286696575503725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176119759346857797717002483 264179639020286696575503725)
  ·
    refine ⟨99067364632607511215813897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 264179639020286696575503725 99067364632607511215813897)
    ·
      refine ⟨74300523474455633411860423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99067364632607511215813897 74300523474455633411860423)
      ·
        refine ⟨111450785211683450117790635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74300523474455633411860423 111450785211683450117790635)
        ·
          refine ⟨167176177817525175176685953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111450785211683450117790635 167176177817525175176685953)
          ·
            refine ⟨125382133363143881382514465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 167176177817525175176685953 125382133363143881382514465)
            ·
              refine ⟨94036600022357911036885849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 125382133363143881382514465 94036600022357911036885849)
              ·
                refine ⟨70527450016768433277664387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 94036600022357911036885849 70527450016768433277664387)
                ·
                  refine ⟨105791175025152649916496581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70527450016768433277664387 105791175025152649916496581)
                  ·
                    refine ⟨19835845317216121859343109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 105791175025152649916496581 19835845317216121859343109)
                    ·
                      refine ⟨3719220996978022848626833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19835845317216121859343109 3719220996978022848626833)
                      ·
                        rfl

theorem cell23_7243157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 2, 1, 4, 4].length) (baseStart_7243157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7243157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7243157 prefixEnd_7243157 := by exact prefixLift 7243157
  have htrace : WordTrace (prefixWord ++ tailWord_7243157) baseStart_7243157 baseEnd_7243157 := by
    simpa [prefixWord, tailWord_7243157, baseEnd_7243157] using wordTrace_append hprefix tailTrace_7243157
  have hstable : (prefixWord ++ tailWord_7243157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7243157).length < 2 ^ (prefixWord ++ tailWord_7243157).sum := by decide
  have hdescent : baseEnd_7243157 < baseStart_7243157 := by decide
  rcases family_descends (prefixWord ++ tailWord_7243157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7243161 : List Nat := [1, 2, 1, 2, 1, 5, 1, 2, 4, 2, 2]
def baseStart_7243161 : Nat := 118140960795 + 7243161 * 2 ^ 59
def prefixEnd_7243161 : Nat := 4983230072969 + 3 ^ 40 * 7243161 * 2
def baseEnd_7243161 : Nat := 3719223050900640832976815

theorem tailTrace_7243161 : CollatzResearch.WordTrace tailWord_7243161 prefixEnd_7243161 3719223050900640832976815 := by
  unfold tailWord_7243161
  simp only [CollatzResearch.WordTrace]
  refine ⟨264179784912272205258649337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176119856608181470172432891 264179784912272205258649337)
  ·
    refine ⟨198134838684204153943987003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 264179784912272205258649337 198134838684204153943987003)
    ·
      refine ⟨297202258026306230915980505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198134838684204153943987003 297202258026306230915980505)
      ·
        refine ⟨222901693519729673186985379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 297202258026306230915980505 222901693519729673186985379)
        ·
          refine ⟨334352540279594509780478069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 222901693519729673186985379 334352540279594509780478069)
          ·
            refine ⟨31345550651211985291919819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 334352540279594509780478069 31345550651211985291919819)
            ·
              refine ⟨47018325976817977937879729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31345550651211985291919819 47018325976817977937879729)
              ·
                refine ⟨35263744482613483453409797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47018325976817977937879729 35263744482613483453409797)
                ·
                  refine ⟨6611952090490028147514337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35263744482613483453409797 6611952090490028147514337)
                  ·
                    refine ⟨4958964067867521110635753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6611952090490028147514337 4958964067867521110635753)
                    ·
                      refine ⟨3719223050900640832976815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4958964067867521110635753 3719223050900640832976815)
                      ·
                        rfl

theorem cell23_7243161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 1, 2, 4, 2, 2].length) (baseStart_7243161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7243161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7243161 prefixEnd_7243161 := by exact prefixLift 7243161
  have htrace : WordTrace (prefixWord ++ tailWord_7243161) baseStart_7243161 baseEnd_7243161 := by
    simpa [prefixWord, tailWord_7243161, baseEnd_7243161] using wordTrace_append hprefix tailTrace_7243161
  have hstable : (prefixWord ++ tailWord_7243161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7243161).length < 2 ^ (prefixWord ++ tailWord_7243161).sum := by decide
  have hdescent : baseEnd_7243161 < baseStart_7243161 := by decide
  rcases family_descends (prefixWord ++ tailWord_7243161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7243207 : List Nat := [1, 1, 4, 1, 1, 3, 1, 2, 1, 1, 7]
def baseStart_7243207 : Nat := 118140960795 + 7243207 * 2 ^ 59
def prefixEnd_7243207 : Nat := 4983230072969 + 3 ^ 40 * 7243207 * 2
def baseEnd_7243207 : Nat := 3719246671010747653001603

theorem tailTrace_7243207 : CollatzResearch.WordTrace tailWord_7243207 prefixEnd_7243207 3719246671010747653001603 := by
  unfold tailWord_7243207
  simp only [CollatzResearch.WordTrace]
  refine ⟨264181462670105555114823875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176120975113403703409882583 264181462670105555114823875)
  ·
    refine ⟨396272194005158332672235813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264181462670105555114823875 396272194005158332672235813)
    ·
      refine ⟨74301036375967187376044215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 396272194005158332672235813 74301036375967187376044215)
      ·
        refine ⟨111451554563950781064066323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74301036375967187376044215 111451554563950781064066323)
        ·
          refine ⟨167177331845926171596099485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111451554563950781064066323 167177331845926171596099485)
          ·
            refine ⟨62691499442222314348537307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 167177331845926171596099485 62691499442222314348537307)
            ·
              refine ⟨94037249163333471522805961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62691499442222314348537307 94037249163333471522805961)
              ·
                refine ⟨70527936872500103642104471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 94037249163333471522805961 70527936872500103642104471)
                ·
                  refine ⟨105791905308750155463156707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70527936872500103642104471 105791905308750155463156707)
                  ·
                    refine ⟨158687857963125233194735061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 105791905308750155463156707 158687857963125233194735061)
                    ·
                      refine ⟨3719246671010747653001603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 158687857963125233194735061 3719246671010747653001603)
                      ·
                        rfl

theorem cell23_7243207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 2, 1, 1, 7].length) (baseStart_7243207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7243207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7243207 prefixEnd_7243207 := by exact prefixLift 7243207
  have htrace : WordTrace (prefixWord ++ tailWord_7243207) baseStart_7243207 baseEnd_7243207 := by
    simpa [prefixWord, tailWord_7243207, baseEnd_7243207] using wordTrace_append hprefix tailTrace_7243207
  have hstable : (prefixWord ++ tailWord_7243207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7243207).length < 2 ^ (prefixWord ++ tailWord_7243207).sum := by decide
  have hdescent : baseEnd_7243207 < baseStart_7243207 := by decide
  rcases family_descends (prefixWord ++ tailWord_7243207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7243214 : List Nat := [4, 1, 1, 1, 2, 1, 3, 3, 2, 5]
def baseStart_7243214 : Nat := 118140960795 + 7243214 * 2 ^ 59
def prefixEnd_7243214 : Nat := 4983230072969 + 3 ^ 40 * 7243214 * 2
def baseEnd_7243214 : Nat := 1239750088458443041871357

theorem tailTrace_7243214 : CollatzResearch.WordTrace tailWord_7243214 prefixEnd_7243214 1239750088458443041871357 := by
  unfold tailWord_7243214
  simp only [CollatzResearch.WordTrace]
  refine ⟨33022714747635024413791087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 176121145320720130206885797 33022714747635024413791087)
  ·
    refine ⟨49534072121452536620686631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33022714747635024413791087 49534072121452536620686631)
    ·
      refine ⟨74301108182178804931029947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49534072121452536620686631 74301108182178804931029947)
      ·
        refine ⟨111451662273268207396544921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74301108182178804931029947 111451662273268207396544921)
        ·
          refine ⟨83588746704951155547408691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111451662273268207396544921 83588746704951155547408691)
          ·
            refine ⟨125383120057426733321113037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83588746704951155547408691 125383120057426733321113037)
            ·
              refine ⟨47018670021535024995417389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 125383120057426733321113037 47018670021535024995417389)
              ·
                refine ⟨17632001258075634373281521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47018670021535024995417389 17632001258075634373281521)
                ·
                  refine ⟨13224000943556725779961141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17632001258075634373281521 13224000943556725779961141)
                  ·
                    refine ⟨1239750088458443041871357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13224000943556725779961141 1239750088458443041871357)
                    ·
                      rfl

theorem cell23_7243214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 3, 3, 2, 5].length) (baseStart_7243214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7243214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7243214 prefixEnd_7243214 := by exact prefixLift 7243214
  have htrace : WordTrace (prefixWord ++ tailWord_7243214) baseStart_7243214 baseEnd_7243214 := by
    simpa [prefixWord, tailWord_7243214, baseEnd_7243214] using wordTrace_append hprefix tailTrace_7243214
  have hstable : (prefixWord ++ tailWord_7243214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7243214).length < 2 ^ (prefixWord ++ tailWord_7243214).sum := by decide
  have hdescent : baseEnd_7243214 < baseStart_7243214 := by decide
  rcases family_descends (prefixWord ++ tailWord_7243214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7243257 : List Nat := [1, 2, 1, 3, 1, 2, 1, 2, 10]
def baseStart_7243257 : Nat := 118140960795 + 7243257 * 2 ^ 59
def prefixEnd_7243257 : Nat := 4983230072969 + 3 ^ 40 * 7243257 * 2
def baseEnd_7243257 : Nat := 413252482782608050819597

theorem tailTrace_7243257 : CollatzResearch.WordTrace tailWord_7243257 prefixEnd_7243257 413252482782608050819597 := by
  unfold tailWord_7243257
  simp only [CollatzResearch.WordTrace]
  refine ⟨264183286319924413654144025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176122190879949609102762683 264183286319924413654144025)
  ·
    refine ⟨198137464739943310240608019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 264183286319924413654144025 198137464739943310240608019)
    ·
      refine ⟨297206197109914965360912029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198137464739943310240608019 297206197109914965360912029)
      ·
        refine ⟨111452323916218112010342011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 297206197109914965360912029 111452323916218112010342011)
        ·
          refine ⟨167178485874327168015513017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111452323916218112010342011 167178485874327168015513017)
          ·
            refine ⟨125383864405745376011634763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 167178485874327168015513017 125383864405745376011634763)
            ·
              refine ⟨188075796608618064017452145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125383864405745376011634763 188075796608618064017452145)
              ·
                refine ⟨141056847456463548013089109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 188075796608618064017452145 141056847456463548013089109)
                ·
                  refine ⟨413252482782608050819597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 141056847456463548013089109 413252482782608050819597)
                  ·
                    rfl

theorem cell23_7243257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 2, 10].length) (baseStart_7243257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7243257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7243257 prefixEnd_7243257 := by exact prefixLift 7243257
  have htrace : WordTrace (prefixWord ++ tailWord_7243257) baseStart_7243257 baseEnd_7243257 := by
    simpa [prefixWord, tailWord_7243257, baseEnd_7243257] using wordTrace_append hprefix tailTrace_7243257
  have hstable : (prefixWord ++ tailWord_7243257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7243257).length < 2 ^ (prefixWord ++ tailWord_7243257).sum := by decide
  have hdescent : baseEnd_7243257 < baseStart_7243257 := by decide
  rcases family_descends (prefixWord ++ tailWord_7243257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7243261 : List Nat := [1, 4, 1, 1, 1, 5, 1, 2, 3, 4]
def baseStart_7243261 : Nat := 118140960795 + 7243261 * 2 ^ 59
def prefixEnd_7243261 : Nat := 4983230072969 + 3 ^ 40 * 7243261 * 2
def baseEnd_7243261 : Nat := 1239758132988696813908785

theorem tailTrace_7243261 : CollatzResearch.WordTrace tailWord_7243261 prefixEnd_7243261 1239758132988696813908785 := by
  unfold tailWord_7243261
  simp only [CollatzResearch.WordTrace]
  refine ⟨264183432211909922337289637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176122288141273281558193091 264183432211909922337289637)
  ·
    refine ⟨49534393539733110438241807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 264183432211909922337289637 49534393539733110438241807)
    ·
      refine ⟨74301590309599665657362711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49534393539733110438241807 74301590309599665657362711)
      ·
        refine ⟨111452385464399498486044067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74301590309599665657362711 111452385464399498486044067)
        ·
          refine ⟨167178578196599247729066101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111452385464399498486044067 167178578196599247729066101)
          ·
            refine ⟨15672991705931179474599947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 167178578196599247729066101 15672991705931179474599947)
            ·
              refine ⟨23509487558896769211899921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15672991705931179474599947 23509487558896769211899921)
              ·
                refine ⟨17632115669172576908924941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23509487558896769211899921 17632115669172576908924941)
                ·
                  refine ⟨6612043375939716340846853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17632115669172576908924941 6612043375939716340846853)
                  ·
                    refine ⟨1239758132988696813908785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6612043375939716340846853 1239758132988696813908785)
                    ·
                      rfl

theorem cell23_7243261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 1, 2, 3, 4].length) (baseStart_7243261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7243261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7243261 prefixEnd_7243261 := by exact prefixLift 7243261
  have htrace : WordTrace (prefixWord ++ tailWord_7243261) baseStart_7243261 baseEnd_7243261 := by
    simpa [prefixWord, tailWord_7243261, baseEnd_7243261] using wordTrace_append hprefix tailTrace_7243261
  have hstable : (prefixWord ++ tailWord_7243261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7243261).length < 2 ^ (prefixWord ++ tailWord_7243261).sum := by decide
  have hdescent : baseEnd_7243261 < baseStart_7243261 := by decide
  rcases family_descends (prefixWord ++ tailWord_7243261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7243271 : List Nat := [1, 1, 4, 3, 2, 2, 1, 1, 1, 4, 3]
def baseStart_7243271 : Nat := 118140960795 + 7243271 * 2 ^ 59
def prefixEnd_7243271 : Nat := 4983230072969 + 3 ^ 40 * 7243271 * 2
def baseEnd_7243271 : Nat := 3719279533772635402601309

theorem tailTrace_7243271 : CollatzResearch.WordTrace tailWord_7243271 prefixEnd_7243271 3719279533772635402601309 := by
  unfold tailWord_7243271
  simp only [CollatzResearch.WordTrace]
  refine ⟨264183796941873694045153667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176122531294582462696769111 264183796941873694045153667)
  ·
    refine ⟨396275695412810541067730501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264183796941873694045153667 396275695412810541067730501)
    ·
      refine ⟨74301692889901976450199469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 396275695412810541067730501 74301692889901976450199469)
      ·
        refine ⟨27863134833713241168824801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74301692889901976450199469 27863134833713241168824801)
        ·
          refine ⟨20897351125284930876618601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27863134833713241168824801 20897351125284930876618601)
          ·
            refine ⟨15673013343963698157463951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20897351125284930876618601 15673013343963698157463951)
            ·
              refine ⟨23509520015945547236195927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15673013343963698157463951 23509520015945547236195927)
              ·
                refine ⟨35264280023918320854293891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23509520015945547236195927 35264280023918320854293891)
                ·
                  refine ⟨52896420035877481281440837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35264280023918320854293891 52896420035877481281440837)
                  ·
                    refine ⟨9918078756727027740270157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 52896420035877481281440837 9918078756727027740270157)
                    ·
                      refine ⟨3719279533772635402601309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9918078756727027740270157 3719279533772635402601309)
                      ·
                        rfl

theorem cell23_7243271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 1, 1, 1, 4, 3].length) (baseStart_7243271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7243271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7243271 prefixEnd_7243271 := by exact prefixLift 7243271
  have htrace : WordTrace (prefixWord ++ tailWord_7243271) baseStart_7243271 baseEnd_7243271 := by
    simpa [prefixWord, tailWord_7243271, baseEnd_7243271] using wordTrace_append hprefix tailTrace_7243271
  have hstable : (prefixWord ++ tailWord_7243271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7243271).length < 2 ^ (prefixWord ++ tailWord_7243271).sum := by decide
  have hdescent : baseEnd_7243271 < baseStart_7243271 := by decide
  rcases family_descends (prefixWord ++ tailWord_7243271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7243321 : List Nat := [1, 2, 1, 5, 1, 2, 1, 4, 1, 5]
def baseStart_7243321 : Nat := 118140960795 + 7243321 * 2 ^ 59
def prefixEnd_7243321 : Nat := 4983230072969 + 3 ^ 40 * 7243321 * 2
def baseEnd_7243321 : Nat := 1239768402601786735658693

theorem tailTrace_7243321 : CollatzResearch.WordTrace tailWord_7243321 prefixEnd_7243321 1239768402601786735658693 := by
  unfold tailWord_7243321
  simp only [CollatzResearch.WordTrace]
  refine ⟨264185620591692552584473817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176123747061128368389649211 264185620591692552584473817)
  ·
    refine ⟨198139215443769414438355363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 264185620591692552584473817 198139215443769414438355363)
    ·
      refine ⟨297208823165654121657533045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198139215443769414438355363 297208823165654121657533045)
      ·
        refine ⟨27863327171780073905393723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 297208823165654121657533045 27863327171780073905393723)
        ·
          refine ⟨41794990757670110858090585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27863327171780073905393723 41794990757670110858090585)
          ·
            refine ⟨31346243068252583143567939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41794990757670110858090585 31346243068252583143567939)
            ·
              refine ⟨47019364602378874715351909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31346243068252583143567939 47019364602378874715351909)
              ·
                refine ⟨8816130862946039009128483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47019364602378874715351909 8816130862946039009128483)
                ·
                  refine ⟨13224196294419058513692725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8816130862946039009128483 13224196294419058513692725)
                  ·
                    refine ⟨1239768402601786735658693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13224196294419058513692725 1239768402601786735658693)
                    ·
                      rfl

theorem cell23_7243321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 1, 4, 1, 5].length) (baseStart_7243321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7243321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7243321 prefixEnd_7243321 := by exact prefixLift 7243321
  have htrace : WordTrace (prefixWord ++ tailWord_7243321) baseStart_7243321 baseEnd_7243321 := by
    simpa [prefixWord, tailWord_7243321, baseEnd_7243321] using wordTrace_append hprefix tailTrace_7243321
  have hstable : (prefixWord ++ tailWord_7243321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7243321).length < 2 ^ (prefixWord ++ tailWord_7243321).sum := by decide
  have hdescent : baseEnd_7243321 < baseStart_7243321 := by decide
  rcases family_descends (prefixWord ++ tailWord_7243321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7243351 : List Nat := [1, 1, 3, 2, 2, 3, 2, 1, 4, 4]
def baseStart_7243351 : Nat := 118140960795 + 7243351 * 2 ^ 59
def prefixEnd_7243351 : Nat := 4983230072969 + 3 ^ 40 * 7243351 * 2
def baseEnd_7243351 : Nat := 1239773537408331696533647

theorem tailTrace_7243351 : CollatzResearch.WordTrace tailWord_7243351 prefixEnd_7243351 1239773537408331696533647 := by
  unfold tailWord_7243351
  simp only [CollatzResearch.WordTrace]
  refine ⟨264186714781583867708065907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176124476521055911805377271 264186714781583867708065907)
  ·
    refine ⟨396280072172375801562098861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264186714781583867708065907 396280072172375801562098861)
    ·
      refine ⟨148605027064640925585787073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 396280072172375801562098861 148605027064640925585787073)
      ·
        refine ⟨111453770298480694189340305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148605027064640925585787073 111453770298480694189340305)
        ·
          refine ⟨83590327723860520642005229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111453770298480694189340305 83590327723860520642005229)
          ·
            refine ⟨31346372896447695240751961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 83590327723860520642005229 31346372896447695240751961)
            ·
              refine ⟨23509779672335771430563971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31346372896447695240751961 23509779672335771430563971)
              ·
                refine ⟨35264669508503657145845957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23509779672335771430563971 35264669508503657145845957)
                ·
                  refine ⟨6612125532844435714846117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35264669508503657145845957 6612125532844435714846117)
                  ·
                    refine ⟨1239773537408331696533647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6612125532844435714846117 1239773537408331696533647)
                    ·
                      rfl

theorem cell23_7243351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 2, 1, 4, 4].length) (baseStart_7243351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7243351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7243351 prefixEnd_7243351 := by exact prefixLift 7243351
  have htrace : WordTrace (prefixWord ++ tailWord_7243351) baseStart_7243351 baseEnd_7243351 := by
    simpa [prefixWord, tailWord_7243351, baseEnd_7243351] using wordTrace_append hprefix tailTrace_7243351
  have hstable : (prefixWord ++ tailWord_7243351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7243351).length < 2 ^ (prefixWord ++ tailWord_7243351).sum := by decide
  have hdescent : baseEnd_7243351 < baseStart_7243351 := by decide
  rcases family_descends (prefixWord ++ tailWord_7243351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7243361 : List Nat := [1, 2, 3, 1, 1, 3, 2, 2, 3, 2, 3]
def baseStart_7243361 : Nat := 118140960795 + 7243361 * 2 ^ 59
def prefixEnd_7243361 : Nat := 4983230072969 + 3 ^ 40 * 7243361 * 2
def baseEnd_7243361 : Nat := 3719325747031540050475895

theorem tailTrace_7243361 : CollatzResearch.WordTrace tailWord_7243361 prefixEnd_7243361 3719325747031540050475895 := by
  unfold tailWord_7243361
  simp only [CollatzResearch.WordTrace]
  refine ⟨264187079511547639415929937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176124719674365092943953291 264187079511547639415929937)
  ·
    refine ⟨198140309633660729561947453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 264187079511547639415929937 198140309633660729561947453)
    ·
      refine ⟨74302616112622773585730295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 198140309633660729561947453 74302616112622773585730295)
      ·
        refine ⟨111453924168934160378595443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74302616112622773585730295 111453924168934160378595443)
        ·
          refine ⟨167180886253401240567893165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111453924168934160378595443 167180886253401240567893165)
          ·
            refine ⟨62692832345025465212959937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 167180886253401240567893165 62692832345025465212959937)
            ·
              refine ⟨47019624258769098909719953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62692832345025465212959937 47019624258769098909719953)
              ·
                refine ⟨35264718194076824182289965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47019624258769098909719953 35264718194076824182289965)
                ·
                  refine ⟨13224269322778809068358737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35264718194076824182289965 13224269322778809068358737)
                  ·
                    refine ⟨9918201992084106801269053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13224269322778809068358737 9918201992084106801269053)
                    ·
                      refine ⟨3719325747031540050475895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9918201992084106801269053 3719325747031540050475895)
                      ·
                        rfl

theorem cell23_7243361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 2, 2, 3, 2, 3].length) (baseStart_7243361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7243361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7243361 prefixEnd_7243361 := by exact prefixLift 7243361
  have htrace : WordTrace (prefixWord ++ tailWord_7243361) baseStart_7243361 baseEnd_7243361 := by
    simpa [prefixWord, tailWord_7243361, baseEnd_7243361] using wordTrace_append hprefix tailTrace_7243361
  have hstable : (prefixWord ++ tailWord_7243361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7243361).length < 2 ^ (prefixWord ++ tailWord_7243361).sum := by decide
  have hdescent : baseEnd_7243361 < baseStart_7243361 := by decide
  rcases family_descends (prefixWord ++ tailWord_7243361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7243364 : List Nat := [2, 3, 1, 1, 2, 3, 1, 10]
def baseStart_7243364 : Nat := 118140960795 + 7243364 * 2 ^ 59
def prefixEnd_7243364 : Nat := 4983230072969 + 3 ^ 40 * 7243364 * 2
def baseEnd_7243364 : Nat := 137752862499018649582903

theorem tailTrace_7243364 : CollatzResearch.WordTrace tailWord_7243364 prefixEnd_7243364 137752862499018649582903 := by
  unfold tailWord_7243364
  simp only [CollatzResearch.WordTrace]
  refine ⟨132093594465268385464144573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176124792620357847285526097 132093594465268385464144573)
  ·
    refine ⟨49535097924475644549054215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132093594465268385464144573 49535097924475644549054215)
    ·
      refine ⟨74302646886713466823581323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49535097924475644549054215 74302646886713466823581323)
      ·
        refine ⟨111453970330070200235371985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74302646886713466823581323 111453970330070200235371985)
        ·
          refine ⟨83590477747552650176528989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111453970330070200235371985 83590477747552650176528989)
          ·
            refine ⟨31346429155332243816198371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 83590477747552650176528989 31346429155332243816198371)
            ·
              refine ⟨47019643732998365724297557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31346429155332243816198371 47019643732998365724297557)
              ·
                refine ⟨137752862499018649582903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 47019643732998365724297557 137752862499018649582903)
                ·
                  rfl

theorem cell23_7243364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 1, 10].length) (baseStart_7243364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7243364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7243364 prefixEnd_7243364 := by exact prefixLift 7243364
  have htrace : WordTrace (prefixWord ++ tailWord_7243364) baseStart_7243364 baseEnd_7243364 := by
    simpa [prefixWord, tailWord_7243364, baseEnd_7243364] using wordTrace_append hprefix tailTrace_7243364
  have hstable : (prefixWord ++ tailWord_7243364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7243364).length < 2 ^ (prefixWord ++ tailWord_7243364).sum := by decide
  have hdescent : baseEnd_7243364 < baseStart_7243364 := by decide
  rcases family_descends (prefixWord ++ tailWord_7243364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7243378 : List Nat := [3, 2, 1, 2, 3, 2, 1, 1, 3, 2, 3]
def baseStart_7243378 : Nat := 118140960795 + 7243378 * 2 ^ 59
def prefixEnd_7243378 : Nat := 4983230072969 + 3 ^ 40 * 7243378 * 2
def baseEnd_7243378 : Nat := 3719334476202666483963317

theorem tailTrace_7243378 : CollatzResearch.WordTrace tailWord_7243378 prefixEnd_7243378 3719334476202666483963317 := by
  unfold tailWord_7243378
  simp only [CollatzResearch.WordTrace]
  refine ⟨66046924888121512829824697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176125133034990700879532525 66046924888121512829824697)
  ·
    refine ⟨49535193666091134622368523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66046924888121512829824697 49535193666091134622368523)
    ·
      refine ⟨74302790499136701933552785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49535193666091134622368523 74302790499136701933552785)
      ·
        refine ⟨55727092874352526450164589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74302790499136701933552785 55727092874352526450164589)
        ·
          refine ⟨20897659827882197418811721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55727092874352526450164589 20897659827882197418811721)
          ·
            refine ⟨15673244870911648064108791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20897659827882197418811721 15673244870911648064108791)
            ·
              refine ⟨23509867306367472096163187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15673244870911648064108791 23509867306367472096163187)
              ·
                refine ⟨35264800959551208144244781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23509867306367472096163187 35264800959551208144244781)
                ·
                  refine ⟨13224300359831703054091793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35264800959551208144244781 13224300359831703054091793)
                  ·
                    refine ⟨9918225269873777290568845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13224300359831703054091793 9918225269873777290568845)
                    ·
                      refine ⟨3719334476202666483963317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9918225269873777290568845 3719334476202666483963317)
                      ·
                        rfl

theorem cell23_7243378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 1, 1, 3, 2, 3].length) (baseStart_7243378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7243378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7243378 prefixEnd_7243378 := by exact prefixLift 7243378
  have htrace : WordTrace (prefixWord ++ tailWord_7243378) baseStart_7243378 baseEnd_7243378 := by
    simpa [prefixWord, tailWord_7243378, baseEnd_7243378] using wordTrace_append hprefix tailTrace_7243378
  have hstable : (prefixWord ++ tailWord_7243378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7243378).length < 2 ^ (prefixWord ++ tailWord_7243378).sum := by decide
  have hdescent : baseEnd_7243378 < baseStart_7243378 := by decide
  rcases family_descends (prefixWord ++ tailWord_7243378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7243381 : List Nat := [1, 3, 4, 2, 1, 1, 2, 9]
def baseStart_7243381 : Nat := 118140960795 + 7243381 * 2 ^ 59
def prefixEnd_7243381 : Nat := 4983230072969 + 3 ^ 40 * 7243381 * 2
def baseEnd_7243381 : Nat := 137753185801652961934289

theorem tailTrace_7243381 : CollatzResearch.WordTrace tailWord_7243381 prefixEnd_7243381 137753185801652961934289 := by
  unfold tailWord_7243381
  simp only [CollatzResearch.WordTrace]
  refine ⟨264187808971475182831657997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176125205980983455221105331 264187808971475182831657997)
  ·
    refine ⟨99070428364303193561871749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 264187808971475182831657997 99070428364303193561871749)
    ·
      refine ⟨18575705318306848792850953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 99070428364303193561871749 18575705318306848792850953)
      ·
        refine ⟨13931778988730136594638215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18575705318306848792850953 13931778988730136594638215)
        ·
          refine ⟨20897668483095204891957323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13931778988730136594638215 20897668483095204891957323)
          ·
            refine ⟨31346502724642807337935985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20897668483095204891957323 31346502724642807337935985)
            ·
              refine ⟨23509877043482105503451989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31346502724642807337935985 23509877043482105503451989)
              ·
                refine ⟨137753185801652961934289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 23509877043482105503451989 137753185801652961934289)
                ·
                  rfl

theorem cell23_7243381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 2, 9].length) (baseStart_7243381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7243381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7243381 prefixEnd_7243381 := by exact prefixLift 7243381
  have htrace : WordTrace (prefixWord ++ tailWord_7243381) baseStart_7243381 baseEnd_7243381 := by
    simpa [prefixWord, tailWord_7243381, baseEnd_7243381] using wordTrace_append hprefix tailTrace_7243381
  have hstable : (prefixWord ++ tailWord_7243381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7243381).length < 2 ^ (prefixWord ++ tailWord_7243381).sum := by decide
  have hdescent : baseEnd_7243381 < baseStart_7243381 := by decide
  rcases family_descends (prefixWord ++ tailWord_7243381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7243425 : List Nat := [1, 2, 3, 3, 2, 1, 2, 3, 2, 1, 3]
def baseStart_7243425 : Nat := 118140960795 + 7243425 * 2 ^ 59
def prefixEnd_7243425 : Nat := 4983230072969 + 3 ^ 40 * 7243425 * 2
def baseEnd_7243425 : Nat := 3719358609793427800075601

theorem tailTrace_7243425 : CollatzResearch.WordTrace tailWord_7243425 prefixEnd_7243425 3719358609793427800075601 := by
  unfold tailWord_7243425
  simp only [CollatzResearch.WordTrace]
  refine ⟨264189413783315778346259729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176126275855543852230839819 264189413783315778346259729)
  ·
    refine ⟨198142060337486833759694797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 264189413783315778346259729 198142060337486833759694797)
    ·
      refine ⟨74303272626557562659885549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 198142060337486833759694797 74303272626557562659885549)
      ·
        refine ⟨27863727234959085997457081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74303272626557562659885549 27863727234959085997457081)
        ·
          refine ⟨20897795426219314498092811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27863727234959085997457081 20897795426219314498092811)
          ·
            refine ⟨31346693139328971747139217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20897795426219314498092811 31346693139328971747139217)
            ·
              refine ⟨23510019854496728810354413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31346693139328971747139217 23510019854496728810354413)
              ·
                refine ⟨8816257445436273303882905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23510019854496728810354413 8816257445436273303882905)
                ·
                  refine ⟨6612193084077204977912179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8816257445436273303882905 6612193084077204977912179)
                  ·
                    refine ⟨9918289626115807466868269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6612193084077204977912179 9918289626115807466868269)
                    ·
                      refine ⟨3719358609793427800075601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9918289626115807466868269 3719358609793427800075601)
                      ·
                        rfl

theorem cell23_7243425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 2, 3, 2, 1, 3].length) (baseStart_7243425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7243425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7243425 prefixEnd_7243425 := by exact prefixLift 7243425
  have htrace : WordTrace (prefixWord ++ tailWord_7243425) baseStart_7243425 baseEnd_7243425 := by
    simpa [prefixWord, tailWord_7243425, baseEnd_7243425] using wordTrace_append hprefix tailTrace_7243425
  have hstable : (prefixWord ++ tailWord_7243425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7243425).length < 2 ^ (prefixWord ++ tailWord_7243425).sum := by decide
  have hdescent : baseEnd_7243425 < baseStart_7243425 := by decide
  rcases family_descends (prefixWord ++ tailWord_7243425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7243432 : List Nat := [2, 1, 7, 1, 1, 1, 3, 7]
def baseStart_7243432 : Nat := 118140960795 + 7243432 * 2 ^ 59
def prefixEnd_7243432 : Nat := 4983230072969 + 3 ^ 40 * 7243432 * 2
def baseEnd_7243432 : Nat := 137754155709555898988447

theorem tailTrace_7243432 : CollatzResearch.WordTrace tailWord_7243432 prefixEnd_7243432 137754155709555898988447 := by
  unfold tailWord_7243432
  simp only [CollatzResearch.WordTrace]
  refine ⟨132094834547145209270882275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176126446062860279027843033 132094834547145209270882275)
  ·
    refine ⟨198142251820717813906323413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132094834547145209270882275 198142251820717813906323413)
    ·
      refine ⟨4643959027048073763429455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 198142251820717813906323413 4643959027048073763429455)
      ·
        refine ⟨6965938540572110645144183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4643959027048073763429455 6965938540572110645144183)
        ·
          refine ⟨10448907810858165967716275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6965938540572110645144183 10448907810858165967716275)
          ·
            refine ⟨15673361716287248951574413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10448907810858165967716275 15673361716287248951574413)
            ·
              refine ⟨5877510643607718356840405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15673361716287248951574413 5877510643607718356840405)
              ·
                refine ⟨137754155709555898988447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5877510643607718356840405 137754155709555898988447)
                ·
                  rfl

theorem cell23_7243432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 3, 7].length) (baseStart_7243432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7243432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7243432 prefixEnd_7243432 := by exact prefixLift 7243432
  have htrace : WordTrace (prefixWord ++ tailWord_7243432) baseStart_7243432 baseEnd_7243432 := by
    simpa [prefixWord, tailWord_7243432, baseEnd_7243432] using wordTrace_append hprefix tailTrace_7243432
  have hstable : (prefixWord ++ tailWord_7243432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7243432).length < 2 ^ (prefixWord ++ tailWord_7243432).sum := by decide
  have hdescent : baseEnd_7243432 < baseStart_7243432 := by decide
  rcases family_descends (prefixWord ++ tailWord_7243432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7243452 : List Nat := [2, 2, 2, 3, 1, 2, 4, 1, 1, 3, 2]
def baseStart_7243452 : Nat := 118140960795 + 7243452 * 2 ^ 59
def prefixEnd_7243452 : Nat := 4983230072969 + 3 ^ 40 * 7243452 * 2
def baseEnd_7243452 : Nat := 3719372473771099194437977

theorem tailTrace_7243452 : CollatzResearch.WordTrace tailWord_7243452 prefixEnd_7243452 3719372473771099194437977 := by
  unfold tailWord_7243452
  simp only [CollatzResearch.WordTrace]
  refine ⟨132095199277108980978746305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176126932369478641304995073 132095199277108980978746305)
  ·
    refine ⟨99071399457831735734059729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132095199277108980978746305 99071399457831735734059729)
    ·
      refine ⟨74303549593373801800544797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99071399457831735734059729 74303549593373801800544797)
      ·
        refine ⟨27863831097515175675204299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74303549593373801800544797 27863831097515175675204299)
        ·
          refine ⟨41795746646272763512806449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27863831097515175675204299 41795746646272763512806449)
          ·
            refine ⟨31346809984704572634604837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41795746646272763512806449 31346809984704572634604837)
            ·
              refine ⟨5877526872132107368988407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31346809984704572634604837 5877526872132107368988407)
              ·
                refine ⟨8816290308198161053482611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5877526872132107368988407 8816290308198161053482611)
                ·
                  refine ⟨13224435462297241580223917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8816290308198161053482611 13224435462297241580223917)
                  ·
                    refine ⟨4959163298361465592583969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13224435462297241580223917 4959163298361465592583969)
                    ·
                      refine ⟨3719372473771099194437977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4959163298361465592583969 3719372473771099194437977)
                      ·
                        rfl

theorem cell23_7243452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 4, 1, 1, 3, 2].length) (baseStart_7243452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7243452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7243452 prefixEnd_7243452 := by exact prefixLift 7243452
  have htrace : WordTrace (prefixWord ++ tailWord_7243452) baseStart_7243452 baseEnd_7243452 := by
    simpa [prefixWord, tailWord_7243452, baseEnd_7243452] using wordTrace_append hprefix tailTrace_7243452
  have hstable : (prefixWord ++ tailWord_7243452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7243452).length < 2 ^ (prefixWord ++ tailWord_7243452).sum := by decide
  have hdescent : baseEnd_7243452 < baseStart_7243452 := by decide
  rcases family_descends (prefixWord ++ tailWord_7243452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7243505 : List Nat := [1, 2, 2, 2, 2, 5, 1, 3, 5]
def baseStart_7243505 : Nat := 118140960795 + 7243505 * 2 ^ 59
def prefixEnd_7243505 : Nat := 4983230072969 + 3 ^ 40 * 7243505 * 2
def baseEnd_7243505 : Nat := 413266632027309720786137

theorem tailTrace_7243505 : CollatzResearch.WordTrace tailWord_7243505 prefixEnd_7243505 413266632027309720786137 := by
  unfold tailWord_7243505
  simp only [CollatzResearch.WordTrace]
  refine ⟨264192331623025952009171969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176128221082017301339447979 264192331623025952009171969)
  ·
    refine ⟨198144248717269464006878977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 264192331623025952009171969 198144248717269464006878977)
    ·
      refine ⟨148608186537952098005159233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 198144248717269464006878977 148608186537952098005159233)
      ·
        refine ⟨111456139903464073503869425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148608186537952098005159233 111456139903464073503869425)
        ·
          refine ⟨83592104927598055127902069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111456139903464073503869425 83592104927598055127902069)
          ·
            refine ⟨7836759836962317668240819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 83592104927598055127902069 7836759836962317668240819)
            ·
              refine ⟨11755139755443476502361229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7836759836962317668240819 11755139755443476502361229)
              ·
                refine ⟨4408177408291303688385461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11755139755443476502361229 4408177408291303688385461)
                ·
                  refine ⟨413266632027309720786137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4408177408291303688385461 413266632027309720786137)
                  ·
                    rfl

theorem cell23_7243505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 5, 1, 3, 5].length) (baseStart_7243505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7243505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7243505 prefixEnd_7243505 := by exact prefixLift 7243505
  have htrace : WordTrace (prefixWord ++ tailWord_7243505) baseStart_7243505 baseEnd_7243505 := by
    simpa [prefixWord, tailWord_7243505, baseEnd_7243505] using wordTrace_append hprefix tailTrace_7243505
  have hstable : (prefixWord ++ tailWord_7243505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7243505).length < 2 ^ (prefixWord ++ tailWord_7243505).sum := by decide
  have hdescent : baseEnd_7243505 < baseStart_7243505 := by decide
  rcases family_descends (prefixWord ++ tailWord_7243505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7243522 : List Nat := [3, 4, 1, 1, 1, 1, 5, 2, 5]
def baseStart_7243522 : Nat := 118140960795 + 7243522 * 2 ^ 59
def prefixEnd_7243522 : Nat := 4983230072969 + 3 ^ 40 * 7243522 * 2
def baseEnd_7243522 : Nat := 413267601935212657840295

theorem tailTrace_7243522 : CollatzResearch.WordTrace tailWord_7243522 prefixEnd_7243522 413267601935212657840295 := by
  unfold tailWord_7243522
  simp only [CollatzResearch.WordTrace]
  refine ⟨66048237915991090978135205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176128634442642909275027213 66048237915991090978135205)
  ·
    refine ⟨12384044609248329558400351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 66048237915991090978135205 12384044609248329558400351)
    ·
      refine ⟨18576066913872494337600527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12384044609248329558400351 18576066913872494337600527)
      ·
        refine ⟨27864100370808741506400791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18576066913872494337600527 27864100370808741506400791)
        ·
          refine ⟨41796150556213112259601187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27864100370808741506400791 41796150556213112259601187)
          ·
            refine ⟨62694225834319668389401781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41796150556213112259601187 62694225834319668389401781)
            ·
              refine ⟨5877583671967468911506417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 62694225834319668389401781 5877583671967468911506417)
              ·
                refine ⟨4408187753975601683629813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5877583671967468911506417 4408187753975601683629813)
                ·
                  refine ⟨413267601935212657840295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4408187753975601683629813 413267601935212657840295)
                  ·
                    rfl

theorem cell23_7243522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 5, 2, 5].length) (baseStart_7243522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7243522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7243522 prefixEnd_7243522 := by exact prefixLift 7243522
  have htrace : WordTrace (prefixWord ++ tailWord_7243522) baseStart_7243522 baseEnd_7243522 := by
    simpa [prefixWord, tailWord_7243522, baseEnd_7243522] using wordTrace_append hprefix tailTrace_7243522
  have hstable : (prefixWord ++ tailWord_7243522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7243522).length < 2 ^ (prefixWord ++ tailWord_7243522).sum := by decide
  have hdescent : baseEnd_7243522 < baseStart_7243522 := by decide
  rcases family_descends (prefixWord ++ tailWord_7243522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7243548 : List Nat := [2, 2, 3, 1, 1, 2, 2, 1, 5, 4]
def baseStart_7243548 : Nat := 118140960795 + 7243548 * 2 ^ 59
def prefixEnd_7243548 : Nat := 4983230072969 + 3 ^ 40 * 7243548 * 2
def baseEnd_7243548 : Nat := 1239807255971310272945845

theorem tailTrace_7243548 : CollatzResearch.WordTrace tailWord_7243548 prefixEnd_7243548 1239807255971310272945845 := by
  unfold tailWord_7243548
  simp only [CollatzResearch.WordTrace]
  refine ⟨132096949980935085176493649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176129266641246780235324865 132096949980935085176493649)
  ·
    refine ⟨99072712485701313882370237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132096949980935085176493649 99072712485701313882370237)
    ·
      refine ⟨37152267182137992705888839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99072712485701313882370237 37152267182137992705888839)
      ·
        refine ⟨55728400773206989058833259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37152267182137992705888839 55728400773206989058833259)
        ·
          refine ⟨83592601159810483588249889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55728400773206989058833259 83592601159810483588249889)
          ·
            refine ⟨62694450869857862691187417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83592601159810483588249889 62694450869857862691187417)
            ·
              refine ⟨47020838152393397018390563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62694450869857862691187417 47020838152393397018390563)
              ·
                refine ⟨70531257228590095527585845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47020838152393397018390563 70531257228590095527585845)
                ·
                  refine ⟨6612305365180321455711173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 70531257228590095527585845 6612305365180321455711173)
                  ·
                    refine ⟨1239807255971310272945845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6612305365180321455711173 1239807255971310272945845)
                    ·
                      rfl

theorem cell23_7243548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 2, 1, 5, 4].length) (baseStart_7243548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7243548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7243548 prefixEnd_7243548 := by exact prefixLift 7243548
  have htrace : WordTrace (prefixWord ++ tailWord_7243548) baseStart_7243548 baseEnd_7243548 := by
    simpa [prefixWord, tailWord_7243548, baseEnd_7243548] using wordTrace_append hprefix tailTrace_7243548
  have hstable : (prefixWord ++ tailWord_7243548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7243548).length < 2 ^ (prefixWord ++ tailWord_7243548).sum := by decide
  have hdescent : baseEnd_7243548 < baseStart_7243548 := by decide
  rcases family_descends (prefixWord ++ tailWord_7243548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7243578 : List Nat := [3, 1, 1, 1, 5, 1, 1, 4, 6]
def baseStart_7243578 : Nat := 118140960795 + 7243578 * 2 ^ 59
def prefixEnd_7243578 : Nat := 4983230072969 + 3 ^ 40 * 7243578 * 2
def baseEnd_7243578 : Nat := 413270796925951744606933

theorem tailTrace_7243578 : CollatzResearch.WordTrace tailWord_7243578 prefixEnd_7243578 413270796925951744606933 := by
  unfold tailWord_7243578
  simp only [CollatzResearch.WordTrace]
  refine ⟨66048748537940371369144847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176129996101174323651052925 66048748537940371369144847)
  ·
    refine ⟨99073122806910557053717271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66048748537940371369144847 99073122806910557053717271)
    ·
      refine ⟨148609684210365835580575907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99073122806910557053717271 148609684210365835580575907)
      ·
        refine ⟨222914526315548753370863861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148609684210365835580575907 222914526315548753370863861)
        ·
          refine ⟨20898236842082695628518487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 222914526315548753370863861 20898236842082695628518487)
          ·
            refine ⟨31347355263124043442777731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20898236842082695628518487 31347355263124043442777731)
            ·
              refine ⟨47021032894686065164166597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31347355263124043442777731 47021032894686065164166597)
              ·
                refine ⟨8816443667753637218281237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47021032894686065164166597 8816443667753637218281237)
                ·
                  refine ⟨413270796925951744606933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8816443667753637218281237 413270796925951744606933)
                  ·
                    rfl

theorem cell23_7243578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 1, 4, 6].length) (baseStart_7243578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7243578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7243578 prefixEnd_7243578 := by exact prefixLift 7243578
  have htrace : WordTrace (prefixWord ++ tailWord_7243578) baseStart_7243578 baseEnd_7243578 := by
    simpa [prefixWord, tailWord_7243578, baseEnd_7243578] using wordTrace_append hprefix tailTrace_7243578
  have hstable : (prefixWord ++ tailWord_7243578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7243578).length < 2 ^ (prefixWord ++ tailWord_7243578).sum := by decide
  have hdescent : baseEnd_7243578 < baseStart_7243578 := by decide
  rcases family_descends (prefixWord ++ tailWord_7243578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7243605 : List Nat := [1, 3, 2, 2, 2, 2, 1, 1, 5, 1, 3]
def baseStart_7243605 : Nat := 118140960795 + 7243605 * 2 ^ 59
def prefixEnd_7243605 : Nat := 4983230072969 + 3 ^ 40 * 7243605 * 2
def baseEnd_7243605 : Nat := 3719451036311237095824773

theorem tailTrace_7243605 : CollatzResearch.WordTrace tailWord_7243605 prefixEnd_7243605 3719451036311237095824773 := by
  unfold tailWord_7243605
  simp only [CollatzResearch.WordTrace]
  refine ⟨264195978922663669087812269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176130652615109112725208179 264195978922663669087812269)
  ·
    refine ⟨99073492095998875907929601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 264195978922663669087812269 99073492095998875907929601)
    ·
      refine ⟨74305119071999156930947201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99073492095998875907929601 74305119071999156930947201)
      ·
        refine ⟨55728839303999367698210401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74305119071999156930947201 55728839303999367698210401)
        ·
          refine ⟨41796629477999525773657801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55728839303999367698210401 41796629477999525773657801)
          ·
            refine ⟨31347472108499644330243351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41796629477999525773657801 31347472108499644330243351)
            ·
              refine ⟨47021208162749466495365027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31347472108499644330243351 47021208162749466495365027)
              ·
                refine ⟨70531812244124199743047541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47021208162749466495365027 70531812244124199743047541)
                ·
                  refine ⟨6612357397886643725910707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 70531812244124199743047541 6612357397886643725910707)
                  ·
                    refine ⟨9918536096829965588866061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6612357397886643725910707 9918536096829965588866061)
                    ·
                      refine ⟨3719451036311237095824773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9918536096829965588866061 3719451036311237095824773)
                      ·
                        rfl

theorem cell23_7243605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 1, 1, 5, 1, 3].length) (baseStart_7243605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7243605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7243605 prefixEnd_7243605 := by exact prefixLift 7243605
  have htrace : WordTrace (prefixWord ++ tailWord_7243605) baseStart_7243605 baseEnd_7243605 := by
    simpa [prefixWord, tailWord_7243605, baseEnd_7243605] using wordTrace_append hprefix tailTrace_7243605
  have hstable : (prefixWord ++ tailWord_7243605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7243605).length < 2 ^ (prefixWord ++ tailWord_7243605).sum := by decide
  have hdescent : baseEnd_7243605 < baseStart_7243605 := by decide
  rcases family_descends (prefixWord ++ tailWord_7243605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7243615 : List Nat := [1, 1, 2, 3, 1, 5, 1, 1, 1, 5, 2]
def baseStart_7243615 : Nat := 118140960795 + 7243615 * 2 ^ 59
def prefixEnd_7243615 : Nat := 4983230072969 + 3 ^ 40 * 7243615 * 2
def baseEnd_7243615 : Nat := 3719456171117782056699727

theorem tailTrace_7243615 : CollatzResearch.WordTrace tailWord_7243615 prefixEnd_7243615 3719456171117782056699727 := by
  unfold tailWord_7243615
  simp only [CollatzResearch.WordTrace]
  refine ⟨264196343652627440795676299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176130895768418293863784199 264196343652627440795676299)
  ·
    refine ⟨396294515478941161193514449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264196343652627440795676299 396294515478941161193514449)
    ·
      refine ⟨297220886609205870895135837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 396294515478941161193514449 297220886609205870895135837)
      ·
        refine ⟨111457832478452201585675939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 297220886609205870895135837 111457832478452201585675939)
        ·
          refine ⟨167186748717678302378513909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111457832478452201585675939 167186748717678302378513909)
          ·
            refine ⟨15673757692282340847985679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 167186748717678302378513909 15673757692282340847985679)
            ·
              refine ⟨23510636538423511271978519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15673757692282340847985679 23510636538423511271978519)
              ·
                refine ⟨35265954807635266907967779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23510636538423511271978519 35265954807635266907967779)
                ·
                  refine ⟨52898932211452900361951669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35265954807635266907967779 52898932211452900361951669)
                  ·
                    refine ⟨4959274894823709408932969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 52898932211452900361951669 4959274894823709408932969)
                    ·
                      refine ⟨3719456171117782056699727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4959274894823709408932969 3719456171117782056699727)
                      ·
                        rfl

theorem cell23_7243615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 1, 1, 1, 5, 2].length) (baseStart_7243615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7243615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7243615 prefixEnd_7243615 := by exact prefixLift 7243615
  have htrace : WordTrace (prefixWord ++ tailWord_7243615) baseStart_7243615 baseEnd_7243615 := by
    simpa [prefixWord, tailWord_7243615, baseEnd_7243615] using wordTrace_append hprefix tailTrace_7243615
  have hstable : (prefixWord ++ tailWord_7243615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7243615).length < 2 ^ (prefixWord ++ tailWord_7243615).sum := by decide
  have hdescent : baseEnd_7243615 < baseStart_7243615 := by decide
  rcases family_descends (prefixWord ++ tailWord_7243615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7243648 : List Nat := [2, 1, 1, 2, 1, 2, 5, 2, 1, 1, 5]
def baseStart_7243648 : Nat := 118140960795 + 7243648 * 2 ^ 59
def prefixEnd_7243648 : Nat := 4983230072969 + 3 ^ 40 * 7243648 * 2
def baseEnd_7243648 : Nat := 3719473115979380427587075

theorem tailTrace_7243648 : CollatzResearch.WordTrace tailWord_7243648 prefixEnd_7243648 3719473115979380427587075 := by
  unfold tailWord_7243648
  simp only [CollatzResearch.WordTrace]
  refine ⟨132098773630753943715813799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176131698174338591621085065 132098773630753943715813799)
  ·
    refine ⟨198148160446130915573720699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132098773630753943715813799 198148160446130915573720699)
    ·
      refine ⟨297222240669196373360581049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198148160446130915573720699 297222240669196373360581049)
      ·
        refine ⟨222916680501897280020435787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 297222240669196373360581049 222916680501897280020435787)
        ·
          refine ⟨334375020752845920030653681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 222916680501897280020435787 334375020752845920030653681)
          ·
            refine ⟨250781265564634440022990261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 334375020752845920030653681 250781265564634440022990261)
            ·
              refine ⟨23510743646684478752155337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 250781265564634440022990261 23510743646684478752155337)
              ·
                refine ⟨17633057735013359064116503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23510743646684478752155337 17633057735013359064116503)
                ·
                  refine ⟨26449586602520038596174755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17633057735013359064116503 26449586602520038596174755)
                  ·
                    refine ⟨39674379903780057894262133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26449586602520038596174755 39674379903780057894262133)
                    ·
                      refine ⟨3719473115979380427587075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39674379903780057894262133 3719473115979380427587075)
                      ·
                        rfl

theorem cell23_7243648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 5, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 5, 2, 1, 1, 5].length) (baseStart_7243648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7243648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7243648 prefixEnd_7243648 := by exact prefixLift 7243648
  have htrace : WordTrace (prefixWord ++ tailWord_7243648) baseStart_7243648 baseEnd_7243648 := by
    simpa [prefixWord, tailWord_7243648, baseEnd_7243648] using wordTrace_append hprefix tailTrace_7243648
  have hstable : (prefixWord ++ tailWord_7243648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7243648).length < 2 ^ (prefixWord ++ tailWord_7243648).sum := by decide
  have hdescent : baseEnd_7243648 < baseStart_7243648 := by decide
  rcases family_descends (prefixWord ++ tailWord_7243648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7243665 : List Nat := [1, 2, 2, 1, 1, 1, 5, 4, 1, 2, 3]
def baseStart_7243665 : Nat := 118140960795 + 7243665 * 2 ^ 59
def prefixEnd_7243665 : Nat := 4983230072969 + 3 ^ 40 * 7243665 * 2
def baseEnd_7243665 : Nat := 3719481845150506861074497

theorem tailTrace_7243665 : CollatzResearch.WordTrace tailWord_7243665 prefixEnd_7243665 3719481845150506861074497 := by
  unfold tailWord_7243665
  simp only [CollatzResearch.WordTrace]
  refine ⟨264198167302446299334996449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176132111534964199556664299 264198167302446299334996449)
  ·
    refine ⟨198148625476834724501247337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 264198167302446299334996449 198148625476834724501247337)
    ·
      refine ⟨148611469107626043375935503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 198148625476834724501247337 148611469107626043375935503)
      ·
        refine ⟨222917203661439065063903255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148611469107626043375935503 222917203661439065063903255)
        ·
          refine ⟨334375805492158597595854883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 222917203661439065063903255 334375805492158597595854883)
          ·
            refine ⟨501563708238237896393782325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 334375805492158597595854883 501563708238237896393782325)
            ·
              refine ⟨47021597647334802786917093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 501563708238237896393782325 47021597647334802786917093)
              ·
                refine ⟨8816549558875275522546955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47021597647334802786917093 8816549558875275522546955)
                ·
                  refine ⟨13224824338312913283820433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8816549558875275522546955 13224824338312913283820433)
                  ·
                    refine ⟨9918618253734684962865325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13224824338312913283820433 9918618253734684962865325)
                    ·
                      refine ⟨3719481845150506861074497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9918618253734684962865325 3719481845150506861074497)
                      ·
                        rfl

theorem cell23_7243665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 2, 3].length) (baseStart_7243665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7243665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7243665 prefixEnd_7243665 := by exact prefixLift 7243665
  have htrace : WordTrace (prefixWord ++ tailWord_7243665) baseStart_7243665 baseEnd_7243665 := by
    simpa [prefixWord, tailWord_7243665, baseEnd_7243665] using wordTrace_append hprefix tailTrace_7243665
  have hstable : (prefixWord ++ tailWord_7243665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7243665).length < 2 ^ (prefixWord ++ tailWord_7243665).sum := by decide
  have hdescent : baseEnd_7243665 < baseStart_7243665 := by decide
  rcases family_descends (prefixWord ++ tailWord_7243665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7243682 : List Nat := [3, 3, 1, 2, 3, 1, 2, 1, 1, 1, 5]
def baseStart_7243682 : Nat := 118140960795 + 7243682 * 2 ^ 59
def prefixEnd_7243682 : Nat := 4983230072969 + 3 ^ 40 * 7243682 * 2
def baseEnd_7243682 : Nat := 3719490574321633294561919

theorem tailTrace_7243682 : CollatzResearch.WordTrace tailWord_7243682 prefixEnd_7243682 3719490574321633294561919 := by
  unfold tailWord_7243682
  simp only [CollatzResearch.WordTrace]
  refine ⟨66049696835846177809591325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176132524895589807492243533 66049696835846177809591325)
  ·
    refine ⟨24768636313442316678596747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66049696835846177809591325 24768636313442316678596747)
    ·
      refine ⟨37152954470163475017895121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24768636313442316678596747 37152954470163475017895121)
      ·
        refine ⟨27864715852622606263421341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37152954470163475017895121 27864715852622606263421341)
        ·
          refine ⟨10449268444733477348783003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27864715852622606263421341 10449268444733477348783003)
          ·
            refine ⟨15673902667100216023174505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10449268444733477348783003 15673902667100216023174505)
            ·
              refine ⟨11755427000325162017380879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15673902667100216023174505 11755427000325162017380879)
              ·
                refine ⟨17633140500487743026071319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11755427000325162017380879 17633140500487743026071319)
                ·
                  refine ⟨26449710750731614539106979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17633140500487743026071319 26449710750731614539106979)
                  ·
                    refine ⟨39674566126097421808660469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26449710750731614539106979 39674566126097421808660469)
                    ·
                      refine ⟨3719490574321633294561919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39674566126097421808660469 3719490574321633294561919)
                      ·
                        rfl

theorem cell23_7243682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 2, 1, 1, 1, 5].length) (baseStart_7243682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7243682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7243682 prefixEnd_7243682 := by exact prefixLift 7243682
  have htrace : WordTrace (prefixWord ++ tailWord_7243682) baseStart_7243682 baseEnd_7243682 := by
    simpa [prefixWord, tailWord_7243682, baseEnd_7243682] using wordTrace_append hprefix tailTrace_7243682
  have hstable : (prefixWord ++ tailWord_7243682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7243682).length < 2 ^ (prefixWord ++ tailWord_7243682).sum := by decide
  have hdescent : baseEnd_7243682 < baseStart_7243682 := by decide
  rcases family_descends (prefixWord ++ tailWord_7243682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7243695 : List Nat := [1, 1, 2, 1, 2, 2, 3, 3, 4, 1, 3]
def baseStart_7243695 : Nat := 118140960795 + 7243695 * 2 ^ 59
def prefixEnd_7243695 : Nat := 4983230072969 + 3 ^ 40 * 7243695 * 2
def baseEnd_7243695 : Nat := 3719497249570141743699359

theorem tailTrace_7243695 : CollatzResearch.WordTrace tailWord_7243695 prefixEnd_7243695 3719497249570141743699359 := by
  unfold tailWord_7243695
  simp only [CollatzResearch.WordTrace]
  refine ⟨264199261492337614458588539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176132840994891742972392359 264199261492337614458588539)
  ·
    refine ⟨396298892238506421687882809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264199261492337614458588539 396298892238506421687882809)
    ·
      refine ⟨297224169178879816265912107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 396298892238506421687882809 297224169178879816265912107)
      ·
        refine ⟨445836253768319724398868161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 297224169178879816265912107 445836253768319724398868161)
        ·
          refine ⟨334377190326239793299151121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 445836253768319724398868161 334377190326239793299151121)
          ·
            refine ⟨250782892744679844974363341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 334377190326239793299151121 250782892744679844974363341)
            ·
              refine ⟨94043584779254941865386253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 250782892744679844974363341 94043584779254941865386253)
              ·
                refine ⟨35266344292220603199519845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 94043584779254941865386253 35266344292220603199519845)
                ·
                  refine ⟨6612439554791363099909971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35266344292220603199519845 6612439554791363099909971)
                  ·
                    refine ⟨9918659332187044649864957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6612439554791363099909971 9918659332187044649864957)
                    ·
                      refine ⟨3719497249570141743699359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9918659332187044649864957 3719497249570141743699359)
                      ·
                        rfl

theorem cell23_7243695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 3, 4, 1, 3].length) (baseStart_7243695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7243695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7243695 prefixEnd_7243695 := by exact prefixLift 7243695
  have htrace : WordTrace (prefixWord ++ tailWord_7243695) baseStart_7243695 baseEnd_7243695 := by
    simpa [prefixWord, tailWord_7243695, baseEnd_7243695] using wordTrace_append hprefix tailTrace_7243695
  have hstable : (prefixWord ++ tailWord_7243695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7243695).length < 2 ^ (prefixWord ++ tailWord_7243695).sum := by decide
  have hdescent : baseEnd_7243695 < baseStart_7243695 := by decide
  rcases family_descends (prefixWord ++ tailWord_7243695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7243712 : List Nat := [2, 1, 1, 2, 3, 2, 3, 3, 2, 1, 3]
def baseStart_7243712 : Nat := 118140960795 + 7243712 * 2 ^ 59
def prefixEnd_7243712 : Nat := 4983230072969 + 3 ^ 40 * 7243712 * 2
def baseEnd_7243712 : Nat := 3719505978741268177186781

theorem tailTrace_7243712 : CollatzResearch.WordTrace tailWord_7243712 prefixEnd_7243712 3719505978741268177186781 := by
  unfold tailWord_7243712
  simp only [CollatzResearch.WordTrace]
  refine ⟨132099940766638013180978695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176133254355517350907971593 132099940766638013180978695)
  ·
    refine ⟨198149911149957019771468043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132099940766638013180978695 198149911149957019771468043)
    ·
      refine ⟨297224866724935529657202065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198149911149957019771468043 297224866724935529657202065)
      ·
        refine ⟨222918650043701647242901549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 297224866724935529657202065 222918650043701647242901549)
        ·
          refine ⟨83594493766388117716088081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 222918650043701647242901549 83594493766388117716088081)
          ·
            refine ⟨62695870324791088287066061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83594493766388117716088081 62695870324791088287066061)
            ·
              refine ⟨23510951371796658107649773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62695870324791088287066061 23510951371796658107649773)
              ·
                refine ⟨8816606764423746790368665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23510951371796658107649773 8816606764423746790368665)
                ·
                  refine ⟨6612455073317810092776499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8816606764423746790368665 6612455073317810092776499)
                  ·
                    refine ⟨9918682609976715139164749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6612455073317810092776499 9918682609976715139164749)
                    ·
                      refine ⟨3719505978741268177186781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9918682609976715139164749 3719505978741268177186781)
                      ·
                        rfl

theorem cell23_7243712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 3, 3, 2, 1, 3].length) (baseStart_7243712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7243712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7243712 prefixEnd_7243712 := by exact prefixLift 7243712
  have htrace : WordTrace (prefixWord ++ tailWord_7243712) baseStart_7243712 baseEnd_7243712 := by
    simpa [prefixWord, tailWord_7243712, baseEnd_7243712] using wordTrace_append hprefix tailTrace_7243712
  have hstable : (prefixWord ++ tailWord_7243712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7243712).length < 2 ^ (prefixWord ++ tailWord_7243712).sum := by decide
  have hdescent : baseEnd_7243712 < baseStart_7243712 := by decide
  rcases family_descends (prefixWord ++ tailWord_7243712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7243769 : List Nat := [1, 2, 1, 3, 1, 4, 2, 3, 2, 2, 2]
def baseStart_7243769 : Nat := 118140960795 + 7243769 * 2 ^ 59
def prefixEnd_7243769 : Nat := 4983230072969 + 3 ^ 40 * 7243769 * 2
def baseEnd_7243769 : Nat := 3719535247138574454174019

theorem tailTrace_7243769 : CollatzResearch.WordTrace tailWord_7243769 prefixEnd_7243769 3719535247138574454174019 := by
  unfold tailWord_7243769
  simp only [CollatzResearch.WordTrace]
  refine ⟨264201960494069525096782361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176134640329379683397854907 264201960494069525096782361)
  ·
    refine ⟨198151470370552143822586771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 264201960494069525096782361 198151470370552143822586771)
    ·
      refine ⟨297227205555828215733880157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198151470370552143822586771 297227205555828215733880157)
      ·
        refine ⟨111460202083435580900205059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 297227205555828215733880157 111460202083435580900205059)
        ·
          refine ⟨167190303125153371350307589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111460202083435580900205059 167190303125153371350307589)
          ·
            refine ⟨31348181835966257128182673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 167190303125153371350307589 31348181835966257128182673)
            ·
              refine ⟨23511136376974692846137005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31348181835966257128182673 23511136376974692846137005)
              ·
                refine ⟨8816676141365509817301377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23511136376974692846137005 8816676141365509817301377)
                ·
                  refine ⟨6612507106024132362976033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8816676141365509817301377 6612507106024132362976033)
                  ·
                    refine ⟨4959380329518099272232025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6612507106024132362976033 4959380329518099272232025)
                    ·
                      refine ⟨3719535247138574454174019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4959380329518099272232025 3719535247138574454174019)
                      ·
                        rfl

theorem cell23_7243769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 2, 3, 2, 2, 2].length) (baseStart_7243769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7243769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7243769 prefixEnd_7243769 := by exact prefixLift 7243769
  have htrace : WordTrace (prefixWord ++ tailWord_7243769) baseStart_7243769 baseEnd_7243769 := by
    simpa [prefixWord, tailWord_7243769, baseEnd_7243769] using wordTrace_append hprefix tailTrace_7243769
  have hstable : (prefixWord ++ tailWord_7243769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7243769).length < 2 ^ (prefixWord ++ tailWord_7243769).sum := by decide
  have hdescent : baseEnd_7243769 < baseStart_7243769 := by decide
  rcases family_descends (prefixWord ++ tailWord_7243769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7243825 : List Nat := [1, 2, 2, 3, 1, 3, 1, 2, 1, 3, 4]
def baseStart_7243825 : Nat := 118140960795 + 7243825 * 2 ^ 59
def prefixEnd_7243825 : Nat := 4983230072969 + 3 ^ 40 * 7243825 * 2
def baseEnd_7243825 : Nat := 3719564002055226235073761

theorem tailTrace_7243825 : CollatzResearch.WordTrace tailWord_7243825 prefixEnd_7243825 3719564002055226235073761 := by
  unfold tailWord_7243825
  simp only [CollatzResearch.WordTrace]
  refine ⟨264204002981866646660820929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176136001987911097773880619 264204002981866646660820929)
  ·
    refine ⟨198153002236399984995615697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 264204002981866646660820929 198153002236399984995615697)
    ·
      refine ⟨148614751677299988746711773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 198153002236399984995615697 148614751677299988746711773)
      ·
        refine ⟨55730531878987495780016915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 148614751677299988746711773 55730531878987495780016915)
        ·
          refine ⟨83595797818481243670025373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55730531878987495780016915 83595797818481243670025373)
          ·
            refine ⟨31348424181930466376259515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 83595797818481243670025373 31348424181930466376259515)
            ·
              refine ⟨47022636272895699564389273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31348424181930466376259515 47022636272895699564389273)
              ·
                refine ⟨35266977204671774673291955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47022636272895699564389273 35266977204671774673291955)
                ·
                  refine ⟨52900465807007662009937933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35266977204671774673291955 52900465807007662009937933)
                  ·
                    refine ⟨19837674677627873253726725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 52900465807007662009937933 19837674677627873253726725)
                    ·
                      refine ⟨3719564002055226235073761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19837674677627873253726725 3719564002055226235073761)
                      ·
                        rfl

theorem cell23_7243825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 1, 2, 1, 3, 4].length) (baseStart_7243825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7243825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7243825 prefixEnd_7243825 := by exact prefixLift 7243825
  have htrace : WordTrace (prefixWord ++ tailWord_7243825) baseStart_7243825 baseEnd_7243825 := by
    simpa [prefixWord, tailWord_7243825, baseEnd_7243825] using wordTrace_append hprefix tailTrace_7243825
  have hstable : (prefixWord ++ tailWord_7243825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7243825).length < 2 ^ (prefixWord ++ tailWord_7243825).sum := by decide
  have hdescent : baseEnd_7243825 < baseStart_7243825 := by decide
  rcases family_descends (prefixWord ++ tailWord_7243825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7243865 : List Nat := [1, 2, 1, 2, 2, 1, 4, 4, 6]
def baseStart_7243865 : Nat := 118140960795 + 7243865 * 2 ^ 59
def prefixEnd_7243865 : Nat := 4983230072969 + 3 ^ 40 * 7243865 * 2
def baseEnd_7243865 : Nat := 413287171253489564285953

theorem tailTrace_7243865 : CollatzResearch.WordTrace tailWord_7243865 prefixEnd_7243865 413287171253489564285953 := by
  unfold tailWord_7243865
  simp only [CollatzResearch.WordTrace]
  refine ⟨264205461901721733492277049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176136974601147822328184699 264205461901721733492277049)
  ·
    refine ⟨198154096426291300119207787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 264205461901721733492277049 198154096426291300119207787)
    ·
      refine ⟨297231144639436950178811681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198154096426291300119207787 297231144639436950178811681)
      ·
        refine ⟨222923358479577712634108761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 297231144639436950178811681 222923358479577712634108761)
        ·
          refine ⟨167192518859683284475581571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 222923358479577712634108761 167192518859683284475581571)
          ·
            refine ⟨250788778289524926713372357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 167192518859683284475581571 250788778289524926713372357)
            ·
              refine ⟨47022895929285923758757317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 250788778289524926713372357 47022895929285923758757317)
              ·
                refine ⟨8816792986741110704766997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47022895929285923758757317 8816792986741110704766997)
                ·
                  refine ⟨413287171253489564285953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8816792986741110704766997 413287171253489564285953)
                  ·
                    rfl

theorem cell23_7243865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 4, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 4, 4, 6].length) (baseStart_7243865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7243865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7243865 prefixEnd_7243865 := by exact prefixLift 7243865
  have htrace : WordTrace (prefixWord ++ tailWord_7243865) baseStart_7243865 baseEnd_7243865 := by
    simpa [prefixWord, tailWord_7243865, baseEnd_7243865] using wordTrace_append hprefix tailTrace_7243865
  have hstable : (prefixWord ++ tailWord_7243865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7243865).length < 2 ^ (prefixWord ++ tailWord_7243865).sum := by decide
  have hdescent : baseEnd_7243865 < baseStart_7243865 := by decide
  rcases family_descends (prefixWord ++ tailWord_7243865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7243925 : List Nat := [1, 3, 2, 1, 1, 1, 3, 2, 3, 6]
def baseStart_7243925 : Nat := 118140960795 + 7243925 * 2 ^ 59
def prefixEnd_7243925 : Nat := 4983230072969 + 3 ^ 40 * 7243925 * 2
def baseEnd_7243925 : Nat := 1239871783373558614607767

theorem tailTrace_7243925 : CollatzResearch.WordTrace tailWord_7243925 prefixEnd_7243925 1239871783373558614607767 := by
  unfold tailWord_7243925
  simp only [CollatzResearch.WordTrace]
  refine ⟨264207650281504363739461229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176138433521002909159640819 264207650281504363739461229)
  ·
    refine ⟨99077868855564136402297961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 264207650281504363739461229 99077868855564136402297961)
    ·
      refine ⟨74308401641673102301723471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99077868855564136402297961 74308401641673102301723471)
      ·
        refine ⟨111462602462509653452585207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74308401641673102301723471 111462602462509653452585207)
        ·
          refine ⟨167193903693764480178877811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111462602462509653452585207 167193903693764480178877811)
          ·
            refine ⟨250790855540646720268316717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 167193903693764480178877811 250790855540646720268316717)
            ·
              refine ⟨94046570827742520100618769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 250790855540646720268316717 94046570827742520100618769)
              ·
                refine ⟨70534928120806890075464077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 94046570827742520100618769 70534928120806890075464077)
                ·
                  refine ⟨26450598045302583778299029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 70534928120806890075464077 26450598045302583778299029)
                  ·
                    refine ⟨1239871783373558614607767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26450598045302583778299029 1239871783373558614607767)
                    ·
                      rfl

theorem cell23_7243925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 2, 3, 6].length) (baseStart_7243925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7243925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7243925 prefixEnd_7243925 := by exact prefixLift 7243925
  have htrace : WordTrace (prefixWord ++ tailWord_7243925) baseStart_7243925 baseEnd_7243925 := by
    simpa [prefixWord, tailWord_7243925, baseEnd_7243925] using wordTrace_append hprefix tailTrace_7243925
  have hstable : (prefixWord ++ tailWord_7243925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7243925).length < 2 ^ (prefixWord ++ tailWord_7243925).sum := by decide
  have hdescent : baseEnd_7243925 < baseStart_7243925 := by decide
  rcases family_descends (prefixWord ++ tailWord_7243925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7243932 : List Nat := [2, 2, 3, 2, 1, 1, 1, 1, 5, 1, 4]
def baseStart_7243932 : Nat := 118140960795 + 7243932 * 2 ^ 59
def prefixEnd_7243932 : Nat := 4983230072969 + 3 ^ 40 * 7243932 * 2
def baseEnd_7243932 : Nat := 3719618944485257316435769

theorem tailTrace_7243932 : CollatzResearch.WordTrace tailWord_7243932 prefixEnd_7243932 3719618944485257316435769 := by
  unfold tailWord_7243932
  simp only [CollatzResearch.WordTrace]
  refine ⟨132103952796239501967483025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176138603728319335956644033 132103952796239501967483025)
  ·
    refine ⟨99077964597179626475612269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132103952796239501967483025 99077964597179626475612269)
    ·
      refine ⟨37154236723942359928354601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99077964597179626475612269 37154236723942359928354601)
      ·
        refine ⟨27865677542956769946265951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37154236723942359928354601 27865677542956769946265951)
        ·
          refine ⟨41798516314435154919398927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27865677542956769946265951 41798516314435154919398927)
          ·
            refine ⟨62697774471652732379098391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41798516314435154919398927 62697774471652732379098391)
            ·
              refine ⟨94046661707479098568647587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62697774471652732379098391 94046661707479098568647587)
              ·
                refine ⟨141069992561218647852971381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94046661707479098568647587 141069992561218647852971381)
                ·
                  refine ⟨13225311802614248236216067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 141069992561218647852971381 13225311802614248236216067)
                  ·
                    refine ⟨19837967703921372354324101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13225311802614248236216067 19837967703921372354324101)
                    ·
                      refine ⟨3719618944485257316435769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19837967703921372354324101 3719618944485257316435769)
                      ·
                        rfl

theorem cell23_7243932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 1, 5, 1, 4].length) (baseStart_7243932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7243932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7243932 prefixEnd_7243932 := by exact prefixLift 7243932
  have htrace : WordTrace (prefixWord ++ tailWord_7243932) baseStart_7243932 baseEnd_7243932 := by
    simpa [prefixWord, tailWord_7243932, baseEnd_7243932] using wordTrace_append hprefix tailTrace_7243932
  have hstable : (prefixWord ++ tailWord_7243932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7243932).length < 2 ^ (prefixWord ++ tailWord_7243932).sum := by decide
  have hdescent : baseEnd_7243932 < baseStart_7243932 := by decide
  rcases family_descends (prefixWord ++ tailWord_7243932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7243949 : List Nat := [1, 5, 2, 1, 2, 1, 2, 1, 3, 1, 4]
def baseStart_7243949 : Nat := 118140960795 + 7243949 * 2 ^ 59
def prefixEnd_7243949 : Nat := 4983230072969 + 3 ^ 40 * 7243949 * 2
def baseEnd_7243949 : Nat := 3719627673656383749923191

theorem tailTrace_7243949 : CollatzResearch.WordTrace tailWord_7243949 prefixEnd_7243949 3719627673656383749923191 := by
  unfold tailWord_7243949
  simp only [CollatzResearch.WordTrace]
  refine ⟨264208525633417415838334901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176139017088944943892223267 264208525633417415838334901)
  ·
    refine ⟨24769549278132882734843897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 264208525633417415838334901 24769549278132882734843897)
    ·
      refine ⟨18577161958599662051132923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24769549278132882734843897 18577161958599662051132923)
      ·
        refine ⟨27865742937899493076699385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18577161958599662051132923 27865742937899493076699385)
        ·
          refine ⟨20899307203424619807524539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27865742937899493076699385 20899307203424619807524539)
          ·
            refine ⟨31348960805136929711286809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20899307203424619807524539 31348960805136929711286809)
            ·
              refine ⟨23511720603852697283465107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31348960805136929711286809 23511720603852697283465107)
              ·
                refine ⟨35267580905779045925197661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23511720603852697283465107 35267580905779045925197661)
                ·
                  refine ⟨13225342839667142221949123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35267580905779045925197661 13225342839667142221949123)
                  ·
                    refine ⟨19838014259500713332923685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13225342839667142221949123 19838014259500713332923685)
                    ·
                      refine ⟨3719627673656383749923191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19838014259500713332923685 3719627673656383749923191)
                      ·
                        rfl

theorem cell23_7243949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 2, 1, 3, 1, 4].length) (baseStart_7243949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7243949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7243949 prefixEnd_7243949 := by exact prefixLift 7243949
  have htrace : WordTrace (prefixWord ++ tailWord_7243949) baseStart_7243949 baseEnd_7243949 := by
    simpa [prefixWord, tailWord_7243949, baseEnd_7243949] using wordTrace_append hprefix tailTrace_7243949
  have hstable : (prefixWord ++ tailWord_7243949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7243949).length < 2 ^ (prefixWord ++ tailWord_7243949).sum := by decide
  have hdescent : baseEnd_7243949 < baseStart_7243949 := by decide
  rcases family_descends (prefixWord ++ tailWord_7243949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7243953 : List Nat := [1, 2, 2, 5, 2, 2, 1, 1, 2, 3, 2]
def baseStart_7243953 : Nat := 118140960795 + 7243953 * 2 ^ 59
def prefixEnd_7243953 : Nat := 4983230072969 + 3 ^ 40 * 7243953 * 2
def baseEnd_7243953 : Nat := 3719629727579001734273173

theorem tailTrace_7243953 : CollatzResearch.WordTrace tailWord_7243953 prefixEnd_7243953 3719629727579001734273173 := by
  unfold tailWord_7243953
  simp only [CollatzResearch.WordTrace]
  refine ⟨264208671525402924521480513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176139114350268616347653675 264208671525402924521480513)
  ·
    refine ⟨198156503644052193391110385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 264208671525402924521480513 198156503644052193391110385)
    ·
      refine ⟨148617377733039145043332789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 198156503644052193391110385 148617377733039145043332789)
      ·
        refine ⟨13932879162472419847812449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 148617377733039145043332789 13932879162472419847812449)
        ·
          refine ⟨10449659371854314885859337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13932879162472419847812449 10449659371854314885859337)
          ·
            refine ⟨7837244528890736164394503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10449659371854314885859337 7837244528890736164394503)
            ·
              refine ⟨11755866793336104246591755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7837244528890736164394503 11755866793336104246591755)
              ·
                refine ⟨17633800190004156369887633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11755866793336104246591755 17633800190004156369887633)
                ·
                  refine ⟨13225350142503117277415725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17633800190004156369887633 13225350142503117277415725)
                  ·
                    refine ⟨4959506303438668979030897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13225350142503117277415725 4959506303438668979030897)
                    ·
                      refine ⟨3719629727579001734273173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4959506303438668979030897 3719629727579001734273173)
                      ·
                        rfl

theorem cell23_7243953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 2, 1, 1, 2, 3, 2].length) (baseStart_7243953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7243953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7243953 prefixEnd_7243953 := by exact prefixLift 7243953
  have htrace : WordTrace (prefixWord ++ tailWord_7243953) baseStart_7243953 baseEnd_7243953 := by
    simpa [prefixWord, tailWord_7243953, baseEnd_7243953] using wordTrace_append hprefix tailTrace_7243953
  have hstable : (prefixWord ++ tailWord_7243953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7243953).length < 2 ^ (prefixWord ++ tailWord_7243953).sum := by decide
  have hdescent : baseEnd_7243953 < baseStart_7243953 := by decide
  rcases family_descends (prefixWord ++ tailWord_7243953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7243962 : List Nat := [3, 1, 1, 1, 2, 2, 4, 2, 1, 2, 4]
def baseStart_7243962 : Nat := 118140960795 + 7243962 * 2 ^ 59
def prefixEnd_7243962 : Nat := 4983230072969 + 3 ^ 40 * 7243962 * 2
def baseEnd_7243962 : Nat := 3719634348904892199060631

theorem tailTrace_7243962 : CollatzResearch.WordTrace tailWord_7243962 prefixEnd_7243962 3719634348904892199060631 := by
  unfold tailWord_7243962
  simp only [CollatzResearch.WordTrace]
  refine ⟨66052249945592579764639535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176139333188246879372372093 66052249945592579764639535)
  ·
    refine ⟨99078374918388869646959303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66052249945592579764639535 99078374918388869646959303)
    ·
      refine ⟨148617562377583304470438955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99078374918388869646959303 148617562377583304470438955)
      ·
        refine ⟨222926343566374956705658433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148617562377583304470438955 222926343566374956705658433)
        ·
          refine ⟨167194757674781217529243825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 222926343566374956705658433 167194757674781217529243825)
          ·
            refine ⟨125396068256085913146932869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 167194757674781217529243825 125396068256085913146932869)
            ·
              refine ⟨23511762798016108715049913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 125396068256085913146932869 23511762798016108715049913)
              ·
                refine ⟨17633822098512081536287435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23511762798016108715049913 17633822098512081536287435)
                ·
                  refine ⟨26450733147768122304431153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17633822098512081536287435 26450733147768122304431153)
                  ·
                    refine ⟨19838049860826091728323365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26450733147768122304431153 19838049860826091728323365)
                    ·
                      refine ⟨3719634348904892199060631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19838049860826091728323365 3719634348904892199060631)
                      ·
                        rfl

theorem cell23_7243962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 4, 2, 1, 2, 4].length) (baseStart_7243962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7243962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7243962 prefixEnd_7243962 := by exact prefixLift 7243962
  have htrace : WordTrace (prefixWord ++ tailWord_7243962) baseStart_7243962 baseEnd_7243962 := by
    simpa [prefixWord, tailWord_7243962, baseEnd_7243962] using wordTrace_append hprefix tailTrace_7243962
  have hstable : (prefixWord ++ tailWord_7243962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7243962).length < 2 ^ (prefixWord ++ tailWord_7243962).sum := by decide
  have hdescent : baseEnd_7243962 < baseStart_7243962 := by decide
  rcases family_descends (prefixWord ++ tailWord_7243962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7243966 : List Nat := [4, 2, 1, 1, 4, 1, 1, 3, 1, 1, 4]
def baseStart_7243966 : Nat := 118140960795 + 7243966 * 2 ^ 59
def prefixEnd_7243966 : Nat := 4983230072969 + 3 ^ 40 * 7243966 * 2
def baseEnd_7243966 : Nat := 3719636402827510183410613

theorem tailTrace_7243966 : CollatzResearch.WordTrace tailWord_7243966 prefixEnd_7243966 3719636402827510183410613 := by
  unfold tailWord_7243966
  simp only [CollatzResearch.WordTrace]
  refine ⟨33026143209294478467712969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 176139430449570551827802501 33026143209294478467712969)
  ·
    refine ⟨24769607406970858850784727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33026143209294478467712969 24769607406970858850784727)
    ·
      refine ⟨37154411110456288276177091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24769607406970858850784727 37154411110456288276177091)
      ·
        refine ⟨55731616665684432414265637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37154411110456288276177091 55731616665684432414265637)
        ·
          refine ⟨10449678124815831077674807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55731616665684432414265637 10449678124815831077674807)
          ·
            refine ⟨15674517187223746616512211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10449678124815831077674807 15674517187223746616512211)
            ·
              refine ⟨23511775780835619924768317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15674517187223746616512211 23511775780835619924768317)
              ·
                refine ⟨8816915917813357471788119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23511775780835619924768317 8816915917813357471788119)
                ·
                  refine ⟨13225373876720036207682179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8816915917813357471788119 13225373876720036207682179)
                  ·
                    refine ⟨19838060815080054311523269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13225373876720036207682179 19838060815080054311523269)
                    ·
                      refine ⟨3719636402827510183410613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19838060815080054311523269 3719636402827510183410613)
                      ·
                        rfl

theorem cell23_7243966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 1, 3, 1, 1, 4].length) (baseStart_7243966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7243966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7243966 prefixEnd_7243966 := by exact prefixLift 7243966
  have htrace : WordTrace (prefixWord ++ tailWord_7243966) baseStart_7243966 baseEnd_7243966 := by
    simpa [prefixWord, tailWord_7243966, baseEnd_7243966] using wordTrace_append hprefix tailTrace_7243966
  have hstable : (prefixWord ++ tailWord_7243966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7243966).length < 2 ^ (prefixWord ++ tailWord_7243966).sum := by decide
  have hdescent : baseEnd_7243966 < baseStart_7243966 := by decide
  rcases family_descends (prefixWord ++ tailWord_7243966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7243972 : List Nat := [2, 3, 3, 1, 2, 2, 10]
def baseStart_7243972 : Nat := 118140960795 + 7243972 * 2 ^ 59
def prefixEnd_7243972 : Nat := 4983230072969 + 3 ^ 40 * 7243972 * 2
def baseEnd_7243972 : Nat := 45921475107548606912785

theorem tailTrace_7243972 : CollatzResearch.WordTrace tailWord_7243972 prefixEnd_7243972 45921475107548606912785 := by
  unfold tailWord_7243972
  simp only [CollatzResearch.WordTrace]
  refine ⟨132104682256167045383211085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176139576341556060510948113 132104682256167045383211085)
  ·
    refine ⟨49539255846062642018704157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132104682256167045383211085 49539255846062642018704157)
    ·
      refine ⟨18577220942273490757014059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49539255846062642018704157 18577220942273490757014059)
      ·
        refine ⟨27865831413410236135521089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18577220942273490757014059 27865831413410236135521089)
        ·
          refine ⟨20899373560057677101640817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27865831413410236135521089 20899373560057677101640817)
          ·
            refine ⟨15674530170043257826230613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20899373560057677101640817 15674530170043257826230613)
            ·
              refine ⟨45921475107548606912785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 15674530170043257826230613 45921475107548606912785)
              ·
                rfl

theorem cell23_7243972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 10].length) (baseStart_7243972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7243972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7243972 prefixEnd_7243972 := by exact prefixLift 7243972
  have htrace : WordTrace (prefixWord ++ tailWord_7243972) baseStart_7243972 baseEnd_7243972 := by
    simpa [prefixWord, tailWord_7243972, baseEnd_7243972] using wordTrace_append hprefix tailTrace_7243972
  have hstable : (prefixWord ++ tailWord_7243972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7243972).length < 2 ^ (prefixWord ++ tailWord_7243972).sum := by decide
  have hdescent : baseEnd_7243972 < baseStart_7243972 := by decide
  rcases family_descends (prefixWord ++ tailWord_7243972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7243975 : List Nat := [1, 1, 4, 1, 1, 1, 1, 1, 4, 2, 6]
def baseStart_7243975 : Nat := 118140960795 + 7243975 * 2 ^ 59
def prefixEnd_7243975 : Nat := 4983230072969 + 3 ^ 40 * 7243975 * 2
def baseEnd_7243975 : Nat := 3719641024153400648198071

theorem tailTrace_7243975 : CollatzResearch.WordTrace tailWord_7243975 prefixEnd_7243975 3719641024153400648198071 := by
  unfold tailWord_7243975
  simp only [CollatzResearch.WordTrace]
  refine ⟨264209473931323222278781379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176139649287548814852520919 264209473931323222278781379)
  ·
    refine ⟨396314210896984833418172069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264209473931323222278781379 396314210896984833418172069)
    ·
      refine ⟨74308914543184656265907263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 396314210896984833418172069 74308914543184656265907263)
      ·
        refine ⟨111463371814776984398860895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74308914543184656265907263 111463371814776984398860895)
        ·
          refine ⟨167195057722165476598291343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111463371814776984398860895 167195057722165476598291343)
          ·
            refine ⟨250792586583248214897437015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 167195057722165476598291343 250792586583248214897437015)
            ·
              refine ⟨376188879874872322346155523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 250792586583248214897437015 376188879874872322346155523)
              ·
                refine ⟨564283319812308483519233285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 376188879874872322346155523 564283319812308483519233285)
                ·
                  refine ⟨105803122464807840659856241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 564283319812308483519233285 105803122464807840659856241)
                  ·
                    refine ⟨79352341848605880494892181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 105803122464807840659856241 79352341848605880494892181)
                    ·
                      refine ⟨3719641024153400648198071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 79352341848605880494892181 3719641024153400648198071)
                      ·
                        rfl

theorem cell23_7243975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 1, 4, 2, 6].length) (baseStart_7243975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7243975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7243975 prefixEnd_7243975 := by exact prefixLift 7243975
  have htrace : WordTrace (prefixWord ++ tailWord_7243975) baseStart_7243975 baseEnd_7243975 := by
    simpa [prefixWord, tailWord_7243975, baseEnd_7243975] using wordTrace_append hprefix tailTrace_7243975
  have hstable : (prefixWord ++ tailWord_7243975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7243975).length < 2 ^ (prefixWord ++ tailWord_7243975).sum := by decide
  have hdescent : baseEnd_7243975 < baseStart_7243975 := by decide
  rcases family_descends (prefixWord ++ tailWord_7243975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7243985 : List Nat := [1, 2, 2, 1, 2, 2, 2, 1, 1, 9]
def baseStart_7243985 : Nat := 118140960795 + 7243985 * 2 ^ 59
def prefixEnd_7243985 : Nat := 4983230072969 + 3 ^ 40 * 7243985 * 2
def baseEnd_7243985 : Nat := 1239882052986648536357675

theorem tailTrace_7243985 : CollatzResearch.WordTrace tailWord_7243985 prefixEnd_7243985 1239882052986648536357675 := by
  unfold tailWord_7243985
  simp only [CollatzResearch.WordTrace]
  refine ⟨264209838661286993986645409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176139892440857995991096939 264209838661286993986645409)
  ·
    refine ⟨198157378995965245489984057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 264209838661286993986645409 198157378995965245489984057)
    ·
      refine ⟨148618034246973934117488043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 198157378995965245489984057 148618034246973934117488043)
      ·
        refine ⟨222927051370460901176232065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148618034246973934117488043 222927051370460901176232065)
        ·
          refine ⟨167195288527845675882174049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 222927051370460901176232065 167195288527845675882174049)
          ·
            refine ⟨125396466395884256911630537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 167195288527845675882174049 125396466395884256911630537)
            ·
              refine ⟨94047349796913192683722903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 125396466395884256911630537 94047349796913192683722903)
              ·
                refine ⟨141071024695369789025584355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94047349796913192683722903 141071024695369789025584355)
                ·
                  refine ⟨211606537043054683538376533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 141071024695369789025584355 211606537043054683538376533)
                  ·
                    refine ⟨1239882052986648536357675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 211606537043054683538376533 1239882052986648536357675)
                    ·
                      rfl

theorem cell23_7243985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 1, 1, 9].length) (baseStart_7243985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7243985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7243985 prefixEnd_7243985 := by exact prefixLift 7243985
  have htrace : WordTrace (prefixWord ++ tailWord_7243985) baseStart_7243985 baseEnd_7243985 := by
    simpa [prefixWord, tailWord_7243985, baseEnd_7243985] using wordTrace_append hprefix tailTrace_7243985
  have hstable : (prefixWord ++ tailWord_7243985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7243985).length < 2 ^ (prefixWord ++ tailWord_7243985).sum := by decide
  have hdescent : baseEnd_7243985 < baseStart_7243985 := by decide
  rcases family_descends (prefixWord ++ tailWord_7243985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7243995 : List Nat := [1, 1, 1, 1, 1, 1, 1, 6, 1, 4, 5]
def baseStart_7243995 : Nat := 118140960795 + 7243995 * 2 ^ 59
def prefixEnd_7243995 : Nat := 4983230072969 + 3 ^ 40 * 7243995 * 2
def baseEnd_7243995 : Nat := 3719651293766490569947979

theorem tailTrace_7243995 : CollatzResearch.WordTrace tailWord_7243995 prefixEnd_7243995 3719651293766490569947979 := by
  unfold tailWord_7243995
  simp only [CollatzResearch.WordTrace]
  refine ⟨264210203391250765694509439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176140135594167177129672959 264210203391250765694509439)
  ·
    refine ⟨396315305086876148541764159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264210203391250765694509439 396315305086876148541764159)
    ·
      refine ⟨594472957630314222812646239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 396315305086876148541764159 594472957630314222812646239)
      ·
        refine ⟨891709436445471334218969359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 594472957630314222812646239 891709436445471334218969359)
        ·
          refine ⟨1337564154668207001328454039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 891709436445471334218969359 1337564154668207001328454039)
          ·
            refine ⟨2006346232002310501992681059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1337564154668207001328454039 2006346232002310501992681059)
            ·
              refine ⟨3009519348003465752989021589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2006346232002310501992681059 3009519348003465752989021589)
              ·
                refine ⟨141071219437662457171360387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3009519348003465752989021589 141071219437662457171360387)
                ·
                  refine ⟨211606829156493685757040581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 141071219437662457171360387 211606829156493685757040581)
                  ·
                    refine ⟨39676280466842566079445109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 211606829156493685757040581 39676280466842566079445109)
                    ·
                      refine ⟨3719651293766490569947979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39676280466842566079445109 3719651293766490569947979)
                      ·
                        rfl

theorem cell23_7243995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 6, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 6, 1, 4, 5].length) (baseStart_7243995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7243995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7243995 prefixEnd_7243995 := by exact prefixLift 7243995
  have htrace : WordTrace (prefixWord ++ tailWord_7243995) baseStart_7243995 baseEnd_7243995 := by
    simpa [prefixWord, tailWord_7243995, baseEnd_7243995] using wordTrace_append hprefix tailTrace_7243995
  have hstable : (prefixWord ++ tailWord_7243995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7243995).length < 2 ^ (prefixWord ++ tailWord_7243995).sum := by decide
  have hdescent : baseEnd_7243995 < baseStart_7243995 := by decide
  rcases family_descends (prefixWord ++ tailWord_7243995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7243996 : List Nat := [2, 2, 5, 2, 1, 1, 1, 1, 1, 1, 6]
def baseStart_7243996 : Nat := 118140960795 + 7243996 * 2 ^ 59
def prefixEnd_7243996 : Nat := 4983230072969 + 3 ^ 40 * 7243996 * 2
def baseEnd_7243996 : Nat := 3719651807247145066035475

theorem tailTrace_7243996 : CollatzResearch.WordTrace tailWord_7243996 prefixEnd_7243996 3719651807247145066035475 := by
  unfold tailWord_7243996
  simp only [CollatzResearch.WordTrace]
  refine ⟨132105119932123571432647921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176140159909498095243530561 132105119932123571432647921)
  ·
    refine ⟨99078839949092678574485941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132105119932123571432647921 99078839949092678574485941)
    ·
      refine ⟨9288641245227438616358057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 99078839949092678574485941 9288641245227438616358057)
      ·
        refine ⟨6966480933920578962268543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9288641245227438616358057 6966480933920578962268543)
        ·
          refine ⟨10449721400880868443402815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6966480933920578962268543 10449721400880868443402815)
          ·
            refine ⟨15674582101321302665104223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10449721400880868443402815 15674582101321302665104223)
            ·
              refine ⟨23511873151981953997656335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15674582101321302665104223 23511873151981953997656335)
              ·
                refine ⟨35267809727972930996484503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23511873151981953997656335 35267809727972930996484503)
                ·
                  refine ⟨52901714591959396494726755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35267809727972930996484503 52901714591959396494726755)
                  ·
                    refine ⟨79352571887939094742090133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 52901714591959396494726755 79352571887939094742090133)
                    ·
                      refine ⟨3719651807247145066035475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 79352571887939094742090133 3719651807247145066035475)
                      ·
                        rfl

theorem cell23_7243996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 1, 1, 1, 1, 6].length) (baseStart_7243996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7243996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7243996 prefixEnd_7243996 := by exact prefixLift 7243996
  have htrace : WordTrace (prefixWord ++ tailWord_7243996) baseStart_7243996 baseEnd_7243996 := by
    simpa [prefixWord, tailWord_7243996, baseEnd_7243996] using wordTrace_append hprefix tailTrace_7243996
  have hstable : (prefixWord ++ tailWord_7243996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7243996).length < 2 ^ (prefixWord ++ tailWord_7243996).sum := by decide
  have hdescent : baseEnd_7243996 < baseStart_7243996 := by decide
  rcases family_descends (prefixWord ++ tailWord_7243996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7244003 : List Nat := [1, 1, 1, 8, 1, 1, 2, 2, 1, 2, 3]
def baseStart_7244003 : Nat := 118140960795 + 7244003 * 2 ^ 59
def prefixEnd_7244003 : Nat := 4983230072969 + 3 ^ 40 * 7244003 * 2
def baseEnd_7244003 : Nat := 3719655401611726538647943

theorem tailTrace_7244003 : CollatzResearch.WordTrace tailWord_7244003 prefixEnd_7244003 3719655401611726538647943 := by
  unfold tailWord_7244003
  simp only [CollatzResearch.WordTrace]
  refine ⟨264210495175221783060800663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176140330116814522040533775 264210495175221783060800663)
  ·
    refine ⟨396315742762832674591200995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264210495175221783060800663 396315742762832674591200995)
    ·
      refine ⟨594473614144249011886801493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 396315742762832674591200995 594473614144249011886801493)
      ·
        refine ⟨6966487665752918108048455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 594473614144249011886801493 6966487665752918108048455)
        ·
          refine ⟨10449731498629377162072683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6966487665752918108048455 10449731498629377162072683)
          ·
            refine ⟨15674597247944065743109025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10449731498629377162072683 15674597247944065743109025)
            ·
              refine ⟨11755947935958049307331769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15674597247944065743109025 11755947935958049307331769)
              ·
                refine ⟨8816960951968536980498827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11755947935958049307331769 8816960951968536980498827)
                ·
                  refine ⟨13225441427952805470748241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8816960951968536980498827 13225441427952805470748241)
                  ·
                    refine ⟨9919081070964604103061181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13225441427952805470748241 9919081070964604103061181)
                    ·
                      refine ⟨3719655401611726538647943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9919081070964604103061181 3719655401611726538647943)
                      ·
                        rfl

theorem cell23_7244003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 2, 2, 1, 2, 3].length) (baseStart_7244003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7244003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7244003 prefixEnd_7244003 := by exact prefixLift 7244003
  have htrace : WordTrace (prefixWord ++ tailWord_7244003) baseStart_7244003 baseEnd_7244003 := by
    simpa [prefixWord, tailWord_7244003, baseEnd_7244003] using wordTrace_append hprefix tailTrace_7244003
  have hstable : (prefixWord ++ tailWord_7244003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7244003).length < 2 ^ (prefixWord ++ tailWord_7244003).sum := by decide
  have hdescent : baseEnd_7244003 < baseStart_7244003 := by decide
  rcases family_descends (prefixWord ++ tailWord_7244003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7244026 : List Nat := [3, 1, 1, 1, 1, 5, 2, 3, 1, 3, 2]
def baseStart_7244026 : Nat := 118140960795 + 7244026 * 2 ^ 59
def prefixEnd_7244026 : Nat := 4983230072969 + 3 ^ 40 * 7244026 * 2
def baseEnd_7244026 : Nat := 3719667211666779948660337

theorem tailTrace_7244026 : CollatzResearch.WordTrace tailWord_7244026 prefixEnd_7244026 3719667211666779948660337 := by
  unfold tailWord_7244026
  simp only [CollatzResearch.WordTrace]
  refine ⟨66052833513534614497221983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176140889369425638659258621 66052833513534614497221983)
  ·
    refine ⟨99079250270301921745832975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66052833513534614497221983 99079250270301921745832975)
    ·
      refine ⟨148618875405452882618749463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99079250270301921745832975 148618875405452882618749463)
      ·
        refine ⟨222928313108179323928124195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148618875405452882618749463 222928313108179323928124195)
        ·
          refine ⟨334392469662268985892186293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 222928313108179323928124195 334392469662268985892186293)
          ·
            refine ⟨31349294030837717427392465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 334392469662268985892186293 31349294030837717427392465)
            ·
              refine ⟨23511970523128288070544349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31349294030837717427392465 23511970523128288070544349)
              ·
                refine ⟨8816988946173108026454131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23511970523128288070544349 8816988946173108026454131)
                ·
                  refine ⟨13225483419259662039681197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8816988946173108026454131 13225483419259662039681197)
                  ·
                    refine ⟨4959556282222373264880449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13225483419259662039681197 4959556282222373264880449)
                    ·
                      refine ⟨3719667211666779948660337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4959556282222373264880449 3719667211666779948660337)
                      ·
                        rfl

theorem cell23_7244026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 2, 3, 1, 3, 2].length) (baseStart_7244026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7244026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7244026 prefixEnd_7244026 := by exact prefixLift 7244026
  have htrace : WordTrace (prefixWord ++ tailWord_7244026) baseStart_7244026 baseEnd_7244026 := by
    simpa [prefixWord, tailWord_7244026, baseEnd_7244026] using wordTrace_append hprefix tailTrace_7244026
  have hstable : (prefixWord ++ tailWord_7244026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7244026).length < 2 ^ (prefixWord ++ tailWord_7244026).sum := by decide
  have hdescent : baseEnd_7244026 < baseStart_7244026 := by decide
  rcases family_descends (prefixWord ++ tailWord_7244026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7244077 : List Nat := [1, 5, 3, 1, 2, 1, 3, 1, 1, 3, 2]
def baseStart_7244077 : Nat := 118140960795 + 7244077 * 2 ^ 59
def prefixEnd_7244077 : Nat := 4983230072969 + 3 ^ 40 * 7244077 * 2
def baseEnd_7244077 : Nat := 3719693399180159249122603

theorem tailTrace_7244077 : CollatzResearch.WordTrace tailWord_7244077 prefixEnd_7244077 3719693399180159249122603 := by
  unfold tailWord_7244077
  simp only [CollatzResearch.WordTrace]
  refine ⟨264213194176953693698994485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176142129451302462465996323 264213194176953693698994485)
  ·
    refine ⟨24769986954089408784280733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 264213194176953693698994485 24769986954089408784280733)
    ·
      refine ⟨9288745107783528294105275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24769986954089408784280733 9288745107783528294105275)
      ·
        refine ⟨13933117661675292441157913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9288745107783528294105275 13933117661675292441157913)
        ·
          refine ⟨10449838246256469330868435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13933117661675292441157913 10449838246256469330868435)
          ·
            refine ⟨15674757369384703996302653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10449838246256469330868435 15674757369384703996302653)
            ·
              refine ⟨5878034013519263998613495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15674757369384703996302653 5878034013519263998613495)
              ·
                refine ⟨8817051020278895997920243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5878034013519263998613495 8817051020278895997920243)
                ·
                  refine ⟨13225576530418343996880365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8817051020278895997920243 13225576530418343996880365)
                  ·
                    refine ⟨4959591198906878998830137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13225576530418343996880365 4959591198906878998830137)
                    ·
                      refine ⟨3719693399180159249122603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4959591198906878998830137 3719693399180159249122603)
                      ·
                        rfl

theorem cell23_7244077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 3, 1, 1, 3, 2].length) (baseStart_7244077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7244077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7244077 prefixEnd_7244077 := by exact prefixLift 7244077
  have htrace : WordTrace (prefixWord ++ tailWord_7244077) baseStart_7244077 baseEnd_7244077 := by
    simpa [prefixWord, tailWord_7244077, baseEnd_7244077] using wordTrace_append hprefix tailTrace_7244077
  have hstable : (prefixWord ++ tailWord_7244077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7244077).length < 2 ^ (prefixWord ++ tailWord_7244077).sum := by decide
  have hdescent : baseEnd_7244077 < baseStart_7244077 := by decide
  rcases family_descends (prefixWord ++ tailWord_7244077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7244099 : List Nat := [1, 1, 1, 3, 1, 3, 3, 1, 2, 5, 2]
def baseStart_7244099 : Nat := 118140960795 + 7244099 * 2 ^ 59
def prefixEnd_7244099 : Nat := 4983230072969 + 3 ^ 40 * 7244099 * 2
def baseEnd_7244099 : Nat := 3719704695754558163047501

theorem tailTrace_7244099 : CollatzResearch.WordTrace tailWord_7244099 prefixEnd_7244099 3719704695754558163047501 := by
  unfold tailWord_7244099
  simp only [CollatzResearch.WordTrace]
  refine ⟨264213996582873991456295351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176142664388582660970863567 264213996582873991456295351)
  ·
    refine ⟨396320994874310987184443027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264213996582873991456295351 396320994874310987184443027)
    ·
      refine ⟨594481492311466480776664541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 396320994874310987184443027 594481492311466480776664541)
      ·
        refine ⟨222930559616799930291249203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 594481492311466480776664541 222930559616799930291249203)
        ·
          refine ⟨334395839425199895436873805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 222930559616799930291249203 334395839425199895436873805)
          ·
            refine ⟨125398439784449960788827677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 334395839425199895436873805 125398439784449960788827677)
            ·
              refine ⟨47024414919168735295810379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 125398439784449960788827677 47024414919168735295810379)
              ·
                refine ⟨70536622378753102943715569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47024414919168735295810379 70536622378753102943715569)
                ·
                  refine ⟨52902466784064827207786677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 70536622378753102943715569 52902466784064827207786677)
                  ·
                    refine ⟨4959606261006077550730001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 52902466784064827207786677 4959606261006077550730001)
                    ·
                      refine ⟨3719704695754558163047501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4959606261006077550730001 3719704695754558163047501)
                      ·
                        rfl

theorem cell23_7244099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 3, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 3, 1, 2, 5, 2].length) (baseStart_7244099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7244099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7244099 prefixEnd_7244099 := by exact prefixLift 7244099
  have htrace : WordTrace (prefixWord ++ tailWord_7244099) baseStart_7244099 baseEnd_7244099 := by
    simpa [prefixWord, tailWord_7244099, baseEnd_7244099] using wordTrace_append hprefix tailTrace_7244099
  have hstable : (prefixWord ++ tailWord_7244099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7244099).length < 2 ^ (prefixWord ++ tailWord_7244099).sum := by decide
  have hdescent : baseEnd_7244099 < baseStart_7244099 := by decide
  rcases family_descends (prefixWord ++ tailWord_7244099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7244146 : List Nat := [3, 2, 1, 2, 1, 3, 1, 2, 2, 4, 2]
def baseStart_7244146 : Nat := 118140960795 + 7244146 * 2 ^ 59
def prefixEnd_7244146 : Nat := 4983230072969 + 3 ^ 40 * 7244146 * 2
def baseEnd_7244146 : Nat := 3719728829345319479159785

theorem tailTrace_7244146 : CollatzResearch.WordTrace tailWord_7244146 prefixEnd_7244146 3719728829345319479159785 := by
  unfold tailWord_7244146
  simp only [CollatzResearch.WordTrace]
  refine ⟨66053927703425929620814073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176143807209135812322170861 66053927703425929620814073)
  ·
    refine ⟨49540445777569447215610555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66053927703425929620814073 49540445777569447215610555)
    ·
      refine ⟨74310668666354170823415833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49540445777569447215610555 74310668666354170823415833)
      ·
        refine ⟨55733001499765628117561875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74310668666354170823415833 55733001499765628117561875)
        ·
          refine ⟨83599502249648442176342813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55733001499765628117561875 83599502249648442176342813)
          ·
            refine ⟨31349813343618165816128555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 83599502249648442176342813 31349813343618165816128555)
            ·
              refine ⟨47024720015427248724192833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31349813343618165816128555 47024720015427248724192833)
              ·
                refine ⟨35268540011570436543144625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47024720015427248724192833 35268540011570436543144625)
                ·
                  refine ⟨26451405008677827407358469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35268540011570436543144625 26451405008677827407358469)
                  ·
                    refine ⟨4959638439127092638879713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26451405008677827407358469 4959638439127092638879713)
                    ·
                      refine ⟨3719728829345319479159785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4959638439127092638879713 3719728829345319479159785)
                      ·
                        rfl

theorem cell23_7244146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 1, 2, 2, 4, 2].length) (baseStart_7244146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7244146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7244146 prefixEnd_7244146 := by exact prefixLift 7244146
  have htrace : WordTrace (prefixWord ++ tailWord_7244146) baseStart_7244146 baseEnd_7244146 := by
    simpa [prefixWord, tailWord_7244146, baseEnd_7244146] using wordTrace_append hprefix tailTrace_7244146
  have hstable : (prefixWord ++ tailWord_7244146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7244146).length < 2 ^ (prefixWord ++ tailWord_7244146).sum := by decide
  have hdescent : baseEnd_7244146 < baseStart_7244146 := by decide
  rcases family_descends (prefixWord ++ tailWord_7244146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7244196 : List Nat := [2, 3, 1, 2, 1, 1, 2, 2, 5, 1, 3]
def baseStart_7244196 : Nat := 118140960795 + 7244196 * 2 ^ 59
def prefixEnd_7244196 : Nat := 4983230072969 + 3 ^ 40 * 7244196 * 2
def baseEnd_7244196 : Nat := 3719754503378044283534555

theorem tailTrace_7244196 : CollatzResearch.WordTrace tailWord_7244196 prefixEnd_7244196 3719754503378044283534555 := by
  unfold tailWord_7244196
  simp only [CollatzResearch.WordTrace]
  refine ⟨132108767231761288511288221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176145022975681718015050961 132108767231761288511288221)
  ·
    refine ⟨49540787711910483191733083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132108767231761288511288221 49540787711910483191733083)
    ·
      refine ⟨74311181567865724787599625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49540787711910483191733083 74311181567865724787599625)
      ·
        refine ⟨55733386175899293590699719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74311181567865724787599625 55733386175899293590699719)
        ·
          refine ⟨83600079263848940386049579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55733386175899293590699719 83600079263848940386049579)
          ·
            refine ⟨125400118895773410579074369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83600079263848940386049579 125400118895773410579074369)
            ·
              refine ⟨94050089171830057934305777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 125400118895773410579074369 94050089171830057934305777)
              ·
                refine ⟨70537566878872543450729333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 94050089171830057934305777 70537566878872543450729333)
                ·
                  refine ⟨6612896894894300948505875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 70537566878872543450729333 6612896894894300948505875)
                  ·
                    refine ⟨9919345342341451422758813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6612896894894300948505875 9919345342341451422758813)
                    ·
                      refine ⟨3719754503378044283534555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9919345342341451422758813 3719754503378044283534555)
                      ·
                        rfl

theorem cell23_7244196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 2, 5, 1, 3].length) (baseStart_7244196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7244196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7244196 prefixEnd_7244196 := by exact prefixLift 7244196
  have htrace : WordTrace (prefixWord ++ tailWord_7244196) baseStart_7244196 baseEnd_7244196 := by
    simpa [prefixWord, tailWord_7244196, baseEnd_7244196] using wordTrace_append hprefix tailTrace_7244196
  have hstable : (prefixWord ++ tailWord_7244196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7244196).length < 2 ^ (prefixWord ++ tailWord_7244196).sum := by decide
  have hdescent : baseEnd_7244196 < baseStart_7244196 := by decide
  rcases family_descends (prefixWord ++ tailWord_7244196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7244259 : List Nat := [1, 1, 1, 6, 3, 11]
def baseStart_7244259 : Nat := 118140960795 + 7244259 * 2 ^ 59
def prefixEnd_7244259 : Nat := 4983230072969 + 3 ^ 40 * 7244259 * 2
def baseEnd_7244259 : Nat := 15307764825758343773855

theorem tailTrace_7244259 : CollatzResearch.WordTrace tailWord_7244259 prefixEnd_7244259 15307764825758343773855 := by
  unfold tailWord_7244259
  simp only [CollatzResearch.WordTrace]
  refine ⟨264219832262294338782119831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176146554841529559188079887 264219832262294338782119831)
  ·
    refine ⟨396329748393441508173179747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264219832262294338782119831 396329748393441508173179747)
    ·
      refine ⟨594494622590162262259769621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 396329748393441508173179747 594494622590162262259769621)
      ·
        refine ⟨27866935433913856043426701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 594494622590162262259769621 27866935433913856043426701)
        ·
          refine ⟨10450100787717696016285013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27866935433913856043426701 10450100787717696016285013)
          ·
            refine ⟨15307764825758343773855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 10450100787717696016285013 15307764825758343773855)
            ·
              rfl

theorem cell23_7244259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 11].length) (baseStart_7244259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7244259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7244259 prefixEnd_7244259 := by exact prefixLift 7244259
  have htrace : WordTrace (prefixWord ++ tailWord_7244259) baseStart_7244259 baseEnd_7244259 := by
    simpa [prefixWord, tailWord_7244259, baseEnd_7244259] using wordTrace_append hprefix tailTrace_7244259
  have hstable : (prefixWord ++ tailWord_7244259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7244259).length < 2 ^ (prefixWord ++ tailWord_7244259).sum := by decide
  have hdescent : baseEnd_7244259 < baseStart_7244259 := by decide
  rcases family_descends (prefixWord ++ tailWord_7244259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7244263 : List Nat := [1, 1, 5, 2, 1, 1, 4, 2, 2, 4]
def baseStart_7244263 : Nat := 118140960795 + 7244263 * 2 ^ 59
def prefixEnd_7244263 : Nat := 4983230072969 + 3 ^ 40 * 7244263 * 2
def baseEnd_7244263 : Nat := 1239929635527298507132249

theorem tailTrace_7244263 : CollatzResearch.WordTrace tailWord_7244263 prefixEnd_7244263 1239929635527298507132249 := by
  unfold tailWord_7244263
  simp only [CollatzResearch.WordTrace]
  refine ⟨264219978154279847465265443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176146652102853231643510295 264219978154279847465265443)
  ·
    refine ⟨396329967231419771197898165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264219978154279847465265443 396329967231419771197898165)
    ·
      refine ⟨37155934427945603549802953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 396329967231419771197898165 37155934427945603549802953)
      ·
        refine ⟨27866950820959202662352215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37155934427945603549802953 27866950820959202662352215)
        ·
          refine ⟨41800426231438803993528323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27866950820959202662352215 41800426231438803993528323)
          ·
            refine ⟨62700639347158205990292485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41800426231438803993528323 62700639347158205990292485)
            ·
              refine ⟨11756369877592163623179841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 62700639347158205990292485 11756369877592163623179841)
              ·
                refine ⟨8817277408194122717384881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11756369877592163623179841 8817277408194122717384881)
                ·
                  refine ⟨6612958056145592038038661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8817277408194122717384881 6612958056145592038038661)
                  ·
                    refine ⟨1239929635527298507132249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6612958056145592038038661 1239929635527298507132249)
                    ·
                      rfl

theorem cell23_7244263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 4, 2, 2, 4].length) (baseStart_7244263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7244263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7244263 prefixEnd_7244263 := by exact prefixLift 7244263
  have htrace : WordTrace (prefixWord ++ tailWord_7244263) baseStart_7244263 baseEnd_7244263 := by
    simpa [prefixWord, tailWord_7244263, baseEnd_7244263] using wordTrace_append hprefix tailTrace_7244263
  have hstable : (prefixWord ++ tailWord_7244263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7244263).length < 2 ^ (prefixWord ++ tailWord_7244263).sum := by decide
  have hdescent : baseEnd_7244263 < baseStart_7244263 := by decide
  rcases family_descends (prefixWord ++ tailWord_7244263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7244313 : List Nat := [1, 2, 1, 2, 1, 1, 2, 7, 1, 3, 2]
def baseStart_7244313 : Nat := 118140960795 + 7244313 * 2 ^ 59
def prefixEnd_7244313 : Nat := 4983230072969 + 3 ^ 40 * 7244313 * 2
def baseEnd_7244313 : Nat := 3719814580614620325771517

theorem tailTrace_7244313 : CollatzResearch.WordTrace tailWord_7244313 prefixEnd_7244313 3719814580614620325771517 := by
  unfold tailWord_7244313
  simp only [CollatzResearch.WordTrace]
  refine ⟨264221801804098706004585593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176147867869399137336390395 264221801804098706004585593)
  ·
    refine ⟨198166351353074029503439195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 264221801804098706004585593 198166351353074029503439195)
    ·
      refine ⟨297249527029611044255158793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198166351353074029503439195 297249527029611044255158793)
      ·
        refine ⟨222937145272208283191369095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 297249527029611044255158793 222937145272208283191369095)
        ·
          refine ⟨334405717908312424787053643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 222937145272208283191369095 334405717908312424787053643)
          ·
            refine ⟨501608576862468637180580465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 334405717908312424787053643 501608576862468637180580465)
            ·
              refine ⟨376206432646851477885435349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 501608576862468637180580465 376206432646851477885435349)
              ·
                refine ⟨8817338265160581512939891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 376206432646851477885435349 8817338265160581512939891)
                ·
                  refine ⟨13226007397740872269409837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8817338265160581512939891 13226007397740872269409837)
                  ·
                    refine ⟨4959752774152827101028689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13226007397740872269409837 4959752774152827101028689)
                    ·
                      refine ⟨3719814580614620325771517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4959752774152827101028689 3719814580614620325771517)
                      ·
                        rfl

theorem cell23_7244313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 7, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 7, 1, 3, 2].length) (baseStart_7244313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7244313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7244313 prefixEnd_7244313 := by exact prefixLift 7244313
  have htrace : WordTrace (prefixWord ++ tailWord_7244313) baseStart_7244313 baseEnd_7244313 := by
    simpa [prefixWord, tailWord_7244313, baseEnd_7244313] using wordTrace_append hprefix tailTrace_7244313
  have hstable : (prefixWord ++ tailWord_7244313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7244313).length < 2 ^ (prefixWord ++ tailWord_7244313).sum := by decide
  have hdescent : baseEnd_7244313 < baseStart_7244313 := by decide
  rcases family_descends (prefixWord ++ tailWord_7244313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7244320 : List Nat := [2, 1, 1, 6, 2, 1, 1, 1, 4, 1, 3]
def baseStart_7244320 : Nat := 118140960795 + 7244320 * 2 ^ 59
def prefixEnd_7244320 : Nat := 4983230072969 + 3 ^ 40 * 7244320 * 2
def baseEnd_7244320 : Nat := 3719818174979201798383985

theorem tailTrace_7244320 : CollatzResearch.WordTrace tailWord_7244320 prefixEnd_7244320 3719818174979201798383985 := by
  unfold tailWord_7244320
  simp only [CollatzResearch.WordTrace]
  refine ⟨132111028557536673100045207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176148038076715564133393609 132111028557536673100045207)
  ·
    refine ⟨198166542836305009650067811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132111028557536673100045207 198166542836305009650067811)
    ·
      refine ⟨297249814254457514475101717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198166542836305009650067811 297249814254457514475101717)
      ·
        refine ⟨13933585043177695991020393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 297249814254457514475101717 13933585043177695991020393)
        ·
          refine ⟨10450188782383271993265295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13933585043177695991020393 10450188782383271993265295)
          ·
            refine ⟨15675283173574907989897943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10450188782383271993265295 15675283173574907989897943)
            ·
              refine ⟨23512924760362361984846915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15675283173574907989897943 23512924760362361984846915)
              ·
                refine ⟨35269387140543542977270373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23512924760362361984846915 35269387140543542977270373)
                ·
                  refine ⟨6613010088851914308238195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35269387140543542977270373 6613010088851914308238195)
                  ·
                    refine ⟨9919515133277871462357293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6613010088851914308238195 9919515133277871462357293)
                    ·
                      refine ⟨3719818174979201798383985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9919515133277871462357293 3719818174979201798383985)
                      ·
                        rfl

theorem cell23_7244320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 1, 1, 4, 1, 3].length) (baseStart_7244320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7244320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7244320 prefixEnd_7244320 := by exact prefixLift 7244320
  have htrace : WordTrace (prefixWord ++ tailWord_7244320) baseStart_7244320 baseEnd_7244320 := by
    simpa [prefixWord, tailWord_7244320, baseEnd_7244320] using wordTrace_append hprefix tailTrace_7244320
  have hstable : (prefixWord ++ tailWord_7244320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7244320).length < 2 ^ (prefixWord ++ tailWord_7244320).sum := by decide
  have hdescent : baseEnd_7244320 < baseStart_7244320 := by decide
  rcases family_descends (prefixWord ++ tailWord_7244320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7244376 : List Nat := [2, 1, 2, 2, 1, 2, 2, 1, 4, 3, 3]
def baseStart_7244376 : Nat := 118140960795 + 7244376 * 2 ^ 59
def prefixEnd_7244376 : Nat := 4983230072969 + 3 ^ 40 * 7244376 * 2
def baseEnd_7244376 : Nat := 3719846929895853579283727

theorem tailTrace_7244376 : CollatzResearch.WordTrace tailWord_7244376 prefixEnd_7244376 3719846929895853579283727 := by
  unfold tailWord_7244376
  simp only [CollatzResearch.WordTrace]
  refine ⟨132112049801435233882064491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176149399735246978509419321 132112049801435233882064491)
  ·
    refine ⟨198168074702152850823096737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132112049801435233882064491 198168074702152850823096737)
    ·
      refine ⟨148626056026614638117322553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 198168074702152850823096737 148626056026614638117322553)
      ·
        refine ⟨111469542019960978587991915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148626056026614638117322553 111469542019960978587991915)
        ·
          refine ⟨167204313029941467881987873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111469542019960978587991915 167204313029941467881987873)
          ·
            refine ⟨125403234772456100911490905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 167204313029941467881987873 125403234772456100911490905)
            ·
              refine ⟨94052426079342075683618179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 125403234772456100911490905 94052426079342075683618179)
              ·
                refine ⟨141078639119013113525427269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94052426079342075683618179 141078639119013113525427269)
                ·
                  refine ⟨26452244834814958786017613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 141078639119013113525427269 26452244834814958786017613)
                  ·
                    refine ⟨9919591813055609544756605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26452244834814958786017613 9919591813055609544756605)
                    ·
                      refine ⟨3719846929895853579283727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9919591813055609544756605 3719846929895853579283727)
                      ·
                        rfl

theorem cell23_7244376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 1, 4, 3, 3].length) (baseStart_7244376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7244376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7244376 prefixEnd_7244376 := by exact prefixLift 7244376
  have htrace : WordTrace (prefixWord ++ tailWord_7244376) baseStart_7244376 baseEnd_7244376 := by
    simpa [prefixWord, tailWord_7244376, baseEnd_7244376] using wordTrace_append hprefix tailTrace_7244376
  have hstable : (prefixWord ++ tailWord_7244376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7244376).length < 2 ^ (prefixWord ++ tailWord_7244376).sum := by decide
  have hdescent : baseEnd_7244376 < baseStart_7244376 := by decide
  rcases family_descends (prefixWord ++ tailWord_7244376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7244477 : List Nat := [1, 4, 1, 2, 1, 4, 2, 3, 1, 4]
def baseStart_7244477 : Nat := 118140960795 + 7244477 * 2 ^ 59
def prefixEnd_7244477 : Nat := 4983230072969 + 3 ^ 40 * 7244477 * 2
def baseEnd_7244477 : Nat := 1239966263813985894706921

theorem tailTrace_7244477 : CollatzResearch.WordTrace tailWord_7244477 prefixEnd_7244477 1239966263813985894706921 := by
  unfold tailWord_7244477
  simp only [CollatzResearch.WordTrace]
  refine ⟨264227783375504562013555685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176151855583669708009037123 264227783375504562013555685)
  ·
    refine ⟨49542709382907105377541691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 264227783375504562013555685 49542709382907105377541691)
    ·
      refine ⟨74314064074360658066312537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49542709382907105377541691 74314064074360658066312537)
      ·
        refine ⟨55735548055770493549734403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74314064074360658066312537 55735548055770493549734403)
        ·
          refine ⟨83603322083655740324601605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55735548055770493549734403 83603322083655740324601605)
          ·
            refine ⟨15675622890685451310862801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 83603322083655740324601605 15675622890685451310862801)
            ·
              refine ⟨11756717168014088483147101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15675622890685451310862801 11756717168014088483147101)
              ·
                refine ⟨4408768938005283181180163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11756717168014088483147101 4408768938005283181180163)
                ·
                  refine ⟨6613153407007924771770245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4408768938005283181180163 6613153407007924771770245)
                  ·
                    refine ⟨1239966263813985894706921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6613153407007924771770245 1239966263813985894706921)
                    ·
                      rfl

theorem cell23_7244477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 2, 3, 1, 4].length) (baseStart_7244477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7244477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7244477 prefixEnd_7244477 := by exact prefixLift 7244477
  have htrace : WordTrace (prefixWord ++ tailWord_7244477) baseStart_7244477 baseEnd_7244477 := by
    simpa [prefixWord, tailWord_7244477, baseEnd_7244477] using wordTrace_append hprefix tailTrace_7244477
  have hstable : (prefixWord ++ tailWord_7244477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7244477).length < 2 ^ (prefixWord ++ tailWord_7244477).sum := by decide
  have hdescent : baseEnd_7244477 < baseStart_7244477 := by decide
  rcases family_descends (prefixWord ++ tailWord_7244477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7244490 : List Nat := [3, 1, 2, 1, 4, 3, 1, 2, 6]
def baseStart_7244490 : Nat := 118140960795 + 7244490 * 2 ^ 59
def prefixEnd_7244490 : Nat := 4983230072969 + 3 ^ 40 * 7244490 * 2
def baseEnd_7244490 : Nat := 413322829632274014806467

theorem tailTrace_7244490 : CollatzResearch.WordTrace tailWord_7244490 prefixEnd_7244490 413322829632274014806467 := by
  unfold tailWord_7244490
  simp only [CollatzResearch.WordTrace]
  refine ⟨66057064381114366308444731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176152171682971643489185949 66057064381114366308444731)
  ·
    refine ⟨99085596571671549462667097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66057064381114366308444731 99085596571671549462667097)
    ·
      refine ⟨74314197428753662097000323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99085596571671549462667097 74314197428753662097000323)
      ·
        refine ⟨111471296143130493145500485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74314197428753662097000323 111471296143130493145500485)
        ·
          refine ⟨20900868026836967464781341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 111471296143130493145500485 20900868026836967464781341)
          ·
            refine ⟨7837825510063862799293003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20900868026836967464781341 7837825510063862799293003)
            ·
              refine ⟨11756738265095794198939505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7837825510063862799293003 11756738265095794198939505)
              ·
                refine ⟨8817553698821845649204629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11756738265095794198939505 8817553698821845649204629)
                ·
                  refine ⟨413322829632274014806467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8817553698821845649204629 413322829632274014806467)
                  ·
                    rfl

theorem cell23_7244490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 3, 1, 2, 6].length) (baseStart_7244490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7244490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7244490 prefixEnd_7244490 := by exact prefixLift 7244490
  have htrace : WordTrace (prefixWord ++ tailWord_7244490) baseStart_7244490 baseEnd_7244490 := by
    simpa [prefixWord, tailWord_7244490, baseEnd_7244490] using wordTrace_append hprefix tailTrace_7244490
  have hstable : (prefixWord ++ tailWord_7244490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7244490).length < 2 ^ (prefixWord ++ tailWord_7244490).sum := by decide
  have hdescent : baseEnd_7244490 < baseStart_7244490 := by decide
  rcases family_descends (prefixWord ++ tailWord_7244490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7244523 : List Nat := [1, 1, 1, 1, 2, 4, 1, 1, 1, 8, 2]
def baseStart_7244523 : Nat := 118140960795 + 7244523 * 2 ^ 59
def prefixEnd_7244523 : Nat := 4983230072969 + 3 ^ 40 * 7244523 * 2
def baseEnd_7244523 : Nat := 3719922411552064504145551

theorem tailTrace_7244523 : CollatzResearch.WordTrace tailWord_7244523 prefixEnd_7244523 3719922411552064504145551 := by
  unfold tailWord_7244523
  simp only [CollatzResearch.WordTrace]
  refine ⟨264229461133337911869730223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176152974088891941246486815 264229461133337911869730223)
  ·
    refine ⟨396344191700006867804595335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264229461133337911869730223 396344191700006867804595335)
    ·
      refine ⟨594516287550010301706893003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 396344191700006867804595335 594516287550010301706893003)
      ·
        refine ⟨891774431325015452560339505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 594516287550010301706893003 891774431325015452560339505)
        ·
          refine ⟨668830823493761589420254629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 891774431325015452560339505 668830823493761589420254629)
          ·
            refine ⟨125405779405080298016297743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 668830823493761589420254629 125405779405080298016297743)
            ·
              refine ⟨188108669107620447024446615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125405779405080298016297743 188108669107620447024446615)
              ·
                refine ⟨282163003661430670536669923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 188108669107620447024446615 282163003661430670536669923)
                ·
                  refine ⟨423244505492146005805004885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 282163003661430670536669923 423244505492146005805004885)
                  ·
                    refine ⟨4959896548736086005527401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 423244505492146005805004885 4959896548736086005527401)
                    ·
                      refine ⟨3719922411552064504145551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4959896548736086005527401 3719922411552064504145551)
                      ·
                        rfl

theorem cell23_7244523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 1, 1, 8, 2].length) (baseStart_7244523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7244523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7244523 prefixEnd_7244523 := by exact prefixLift 7244523
  have htrace : WordTrace (prefixWord ++ tailWord_7244523) baseStart_7244523 baseEnd_7244523 := by
    simpa [prefixWord, tailWord_7244523, baseEnd_7244523] using wordTrace_append hprefix tailTrace_7244523
  have hstable : (prefixWord ++ tailWord_7244523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7244523).length < 2 ^ (prefixWord ++ tailWord_7244523).sum := by decide
  have hdescent : baseEnd_7244523 < baseStart_7244523 := by decide
  rcases family_descends (prefixWord ++ tailWord_7244523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7244540 : List Nat := [2, 2, 2, 1, 3, 2, 2, 3, 1, 1, 4]
def baseStart_7244540 : Nat := 118140960795 + 7244540 * 2 ^ 59
def prefixEnd_7244540 : Nat := 4983230072969 + 3 ^ 40 * 7244540 * 2
def baseEnd_7244540 : Nat := 3719931140723190937632973

theorem tailTrace_7244540 : CollatzResearch.WordTrace tailWord_7244540 prefixEnd_7244540 3719931140723190937632973 := by
  unfold tailWord_7244540
  simp only [CollatzResearch.WordTrace]
  refine ⟨132115040587138161886549537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176153387449517549182066049 132115040587138161886549537)
  ·
    refine ⟨99086280440353621414912153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132115040587138161886549537 99086280440353621414912153)
    ·
      refine ⟨74314710330265216061184115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99086280440353621414912153 74314710330265216061184115)
      ·
        refine ⟨111472065495397824091776173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74314710330265216061184115 111472065495397824091776173)
        ·
          refine ⟨41802024560774184034416065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 111472065495397824091776173 41802024560774184034416065)
          ·
            refine ⟨31351518420580638025812049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41802024560774184034416065 31351518420580638025812049)
            ·
              refine ⟨23513638815435478519359037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31351518420580638025812049 23513638815435478519359037)
              ·
                refine ⟨8817614555788304444759639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23513638815435478519359037 8817614555788304444759639)
                ·
                  refine ⟨13226421833682456667139459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8817614555788304444759639 13226421833682456667139459)
                  ·
                    refine ⟨19839632750523685000709189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13226421833682456667139459 19839632750523685000709189)
                    ·
                      refine ⟨3719931140723190937632973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19839632750523685000709189 3719931140723190937632973)
                      ·
                        rfl

theorem cell23_7244540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 2, 3, 1, 1, 4].length) (baseStart_7244540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7244540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7244540 prefixEnd_7244540 := by exact prefixLift 7244540
  have htrace : WordTrace (prefixWord ++ tailWord_7244540) baseStart_7244540 baseEnd_7244540 := by
    simpa [prefixWord, tailWord_7244540, baseEnd_7244540] using wordTrace_append hprefix tailTrace_7244540
  have hstable : (prefixWord ++ tailWord_7244540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7244540).length < 2 ^ (prefixWord ++ tailWord_7244540).sum := by decide
  have hdescent : baseEnd_7244540 < baseStart_7244540 := by decide
  rcases family_descends (prefixWord ++ tailWord_7244540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7244543 : List Nat := [1, 1, 2, 2, 1, 3, 1, 2, 5, 2, 3]
def baseStart_7244543 : Nat := 118140960795 + 7244543 * 2 ^ 59
def prefixEnd_7244543 : Nat := 4983230072969 + 3 ^ 40 * 7244543 * 2
def baseEnd_7244543 : Nat := 3719932681165154425895459

theorem tailTrace_7244543 : CollatzResearch.WordTrace tailWord_7244543 prefixEnd_7244543 3719932681165154425895459 := by
  unfold tailWord_7244543
  simp only [CollatzResearch.WordTrace]
  refine ⟨264230190593265455285458283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176153460395510303523638855 264230190593265455285458283)
  ·
    refine ⟨396345285889898182928187425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264230190593265455285458283 396345285889898182928187425)
    ·
      refine ⟨297258964417423637196140569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 396345285889898182928187425 297258964417423637196140569)
      ·
        refine ⟨222944223313067727897105427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 297258964417423637196140569 222944223313067727897105427)
        ·
          refine ⟨334416334969601591845658141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 222944223313067727897105427 334416334969601591845658141)
          ·
            refine ⟨125406125613600596942121803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 334416334969601591845658141 125406125613600596942121803)
            ·
              refine ⟨188109188420400895413182705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125406125613600596942121803 188109188420400895413182705)
              ·
                refine ⟨141081891315300671559887029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 188109188420400895413182705 141081891315300671559887029)
                ·
                  refine ⟨13226427310809437958739409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 141081891315300671559887029 13226427310809437958739409)
                  ·
                    refine ⟨9919820483107078469054557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13226427310809437958739409 9919820483107078469054557)
                    ·
                      refine ⟨3719932681165154425895459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9919820483107078469054557 3719932681165154425895459)
                      ·
                        rfl

theorem cell23_7244543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 2, 5, 2, 3].length) (baseStart_7244543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7244543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7244543 prefixEnd_7244543 := by exact prefixLift 7244543
  have htrace : WordTrace (prefixWord ++ tailWord_7244543) baseStart_7244543 baseEnd_7244543 := by
    simpa [prefixWord, tailWord_7244543, baseEnd_7244543] using wordTrace_append hprefix tailTrace_7244543
  have hstable : (prefixWord ++ tailWord_7244543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7244543).length < 2 ^ (prefixWord ++ tailWord_7244543).sum := by decide
  have hdescent : baseEnd_7244543 < baseStart_7244543 := by decide
  rcases family_descends (prefixWord ++ tailWord_7244543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7244551 : List Nat := [1, 1, 4, 4, 1, 2, 3, 2, 1, 1, 3]
def baseStart_7244551 : Nat := 118140960795 + 7244551 * 2 ^ 59
def prefixEnd_7244551 : Nat := 4983230072969 + 3 ^ 40 * 7244551 * 2
def baseEnd_7244551 : Nat := 3719936789010390394595423

theorem tailTrace_7244551 : CollatzResearch.WordTrace tailWord_7244551 prefixEnd_7244551 3719936789010390394595423 := by
  unfold tailWord_7244551
  simp only [CollatzResearch.WordTrace]
  refine ⟨264230482377236472651749507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176153654918157648434499671 264230482377236472651749507)
  ·
    refine ⟨396345723565854708977624261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264230482377236472651749507 396345723565854708977624261)
    ·
      refine ⟨74314823168597757933304549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 396345723565854708977624261 74314823168597757933304549)
      ·
        refine ⟨13934029344112079612494603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 74314823168597757933304549 13934029344112079612494603)
        ·
          refine ⟨20901044016168119418741905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13934029344112079612494603 20901044016168119418741905)
          ·
            refine ⟨15675783012126089564056429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20901044016168119418741905 15675783012126089564056429)
            ·
              refine ⟨5878418629547283586521161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15675783012126089564056429 5878418629547283586521161)
              ·
                refine ⟨4408813972160462689890871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5878418629547283586521161 4408813972160462689890871)
                ·
                  refine ⟨6613220958240694034836307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4408813972160462689890871 6613220958240694034836307)
                  ·
                    refine ⟨9919831437361041052254461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6613220958240694034836307 9919831437361041052254461)
                    ·
                      refine ⟨3719936789010390394595423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9919831437361041052254461 3719936789010390394595423)
                      ·
                        rfl

theorem cell23_7244551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 3, 2, 1, 1, 3].length) (baseStart_7244551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7244551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7244551 prefixEnd_7244551 := by exact prefixLift 7244551
  have htrace : WordTrace (prefixWord ++ tailWord_7244551) baseStart_7244551 baseEnd_7244551 := by
    simpa [prefixWord, tailWord_7244551, baseEnd_7244551] using wordTrace_append hprefix tailTrace_7244551
  have hstable : (prefixWord ++ tailWord_7244551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7244551).length < 2 ^ (prefixWord ++ tailWord_7244551).sum := by decide
  have hdescent : baseEnd_7244551 < baseStart_7244551 := by decide
  rcases family_descends (prefixWord ++ tailWord_7244551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7244567 : List Nat := [1, 1, 3, 4, 3, 1, 1, 3, 2, 4]
def baseStart_7244567 : Nat := 118140960795 + 7244567 * 2 ^ 59
def prefixEnd_7244567 : Nat := 4983230072969 + 3 ^ 40 * 7244567 * 2
def baseEnd_7244567 : Nat := 1239981668233620777331783

theorem tailTrace_7244567 : CollatzResearch.WordTrace tailWord_7244567 prefixEnd_7244567 1239981668233620777331783 := by
  unfold tailWord_7244567
  simp only [CollatzResearch.WordTrace]
  refine ⟨264231065945178507384331955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176154043963452338256221303 264231065945178507384331955)
  ·
    refine ⟨396346598917767761076497933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264231065945178507384331955 396346598917767761076497933)
    ·
      refine ⟨148629974594162910403686725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 396346598917767761076497933 148629974594162910403686725)
      ·
        refine ⟨27868120236405545700691261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 148629974594162910403686725 27868120236405545700691261)
        ·
          refine ⟨10450545088652079637759223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27868120236405545700691261 10450545088652079637759223)
          ·
            refine ⟨15675817632978119456638835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10450545088652079637759223 15675817632978119456638835)
            ·
              refine ⟨23513726449467179184958253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15675817632978119456638835 23513726449467179184958253)
              ·
                refine ⟨8817647418550192194359345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23513726449467179184958253 8817647418550192194359345)
                ·
                  refine ⟨6613235563912644145769509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8817647418550192194359345 6613235563912644145769509)
                  ·
                    refine ⟨1239981668233620777331783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6613235563912644145769509 1239981668233620777331783)
                    ·
                      rfl

theorem cell23_7244567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 1, 3, 2, 4].length) (baseStart_7244567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7244567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7244567 prefixEnd_7244567 := by exact prefixLift 7244567
  have htrace : WordTrace (prefixWord ++ tailWord_7244567) baseStart_7244567 baseEnd_7244567 := by
    simpa [prefixWord, tailWord_7244567, baseEnd_7244567] using wordTrace_append hprefix tailTrace_7244567
  have hstable : (prefixWord ++ tailWord_7244567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7244567).length < 2 ^ (prefixWord ++ tailWord_7244567).sum := by decide
  have hdescent : baseEnd_7244567 < baseStart_7244567 := by decide
  rcases family_descends (prefixWord ++ tailWord_7244567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7244607 : List Nat := [1, 1, 2, 2, 5, 1, 1, 4, 2, 1, 3]
def baseStart_7244607 : Nat := 118140960795 + 7244607 * 2 ^ 59
def prefixEnd_7244607 : Nat := 4983230072969 + 3 ^ 40 * 7244607 * 2
def baseEnd_7244607 : Nat := 3719965543927042175495165

theorem tailTrace_7244607 : CollatzResearch.WordTrace tailWord_7244607 prefixEnd_7244607 3719965543927042175495165 := by
  unfold tailWord_7244607
  simp only [CollatzResearch.WordTrace]
  refine ⟨264232524865033594215788075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176155016576689062810525383 264232524865033594215788075)
  ·
    refine ⟨396348787297550391323682113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264232524865033594215788075 396348787297550391323682113)
    ·
      refine ⟨297261590473162793492761585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 396348787297550391323682113 297261590473162793492761585)
      ·
        refine ⟨222946192854872095119571189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 297261590473162793492761585 222946192854872095119571189)
        ·
          refine ⟨20901205580144258917459799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 222946192854872095119571189 20901205580144258917459799)
          ·
            refine ⟨31351808370216388376189699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20901205580144258917459799 31351808370216388376189699)
            ·
              refine ⟨47027712555324582564284549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31351808370216388376189699 47027712555324582564284549)
              ·
                refine ⟨8817696104123359230803353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47027712555324582564284549 8817696104123359230803353)
                ·
                  refine ⟨6613272078092519423102515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8817696104123359230803353 6613272078092519423102515)
                  ·
                    refine ⟨9919908117138779134653773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6613272078092519423102515 9919908117138779134653773)
                    ·
                      refine ⟨3719965543927042175495165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9919908117138779134653773 3719965543927042175495165)
                      ·
                        rfl

theorem cell23_7244607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 1, 4, 2, 1, 3].length) (baseStart_7244607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7244607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7244607 prefixEnd_7244607 := by exact prefixLift 7244607
  have htrace : WordTrace (prefixWord ++ tailWord_7244607) baseStart_7244607 baseEnd_7244607 := by
    simpa [prefixWord, tailWord_7244607, baseEnd_7244607] using wordTrace_append hprefix tailTrace_7244607
  have hstable : (prefixWord ++ tailWord_7244607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7244607).length < 2 ^ (prefixWord ++ tailWord_7244607).sum := by decide
  have hdescent : baseEnd_7244607 < baseStart_7244607 := by decide
  rcases family_descends (prefixWord ++ tailWord_7244607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7244614 : List Nat := [6, 1, 1, 2, 2, 2, 1, 8]
def baseStart_7244614 : Nat := 118140960795 + 7244614 * 2 ^ 59
def prefixEnd_7244614 : Nat := 4983230072969 + 3 ^ 40 * 7244614 * 2
def baseEnd_7244614 : Nat := 137776634751541616596579

theorem tailTrace_7244614 : CollatzResearch.WordTrace tailWord_7244614 prefixEnd_7244614 137776634751541616596579 := by
  unfold tailWord_7244614
  simp only [CollatzResearch.WordTrace]
  refine ⟨8257274380500257325352903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 176155186784005489607528597 8257274380500257325352903)
  ·
    refine ⟨12385911570750385988029355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8257274380500257325352903 12385911570750385988029355)
    ·
      refine ⟨18578867356125578982044033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12385911570750385988029355 18578867356125578982044033)
      ·
        refine ⟨13934150517094184236533025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18578867356125578982044033 13934150517094184236533025)
        ·
          refine ⟨10450612887820638177399769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13934150517094184236533025 10450612887820638177399769)
          ·
            refine ⟨7837959665865478633049827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10450612887820638177399769 7837959665865478633049827)
            ·
              refine ⟨11756939498798217949574741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7837959665865478633049827 11756939498798217949574741)
              ·
                refine ⟨137776634751541616596579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11756939498798217949574741 137776634751541616596579)
                ·
                  rfl

theorem cell23_7244614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 2, 1, 8].length) (baseStart_7244614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7244614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7244614 prefixEnd_7244614 := by exact prefixLift 7244614
  have htrace : WordTrace (prefixWord ++ tailWord_7244614) baseStart_7244614 baseEnd_7244614 := by
    simpa [prefixWord, tailWord_7244614, baseEnd_7244614] using wordTrace_append hprefix tailTrace_7244614
  have hstable : (prefixWord ++ tailWord_7244614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7244614).length < 2 ^ (prefixWord ++ tailWord_7244614).sum := by decide
  have hdescent : baseEnd_7244614 < baseStart_7244614 := by decide
  rcases family_descends (prefixWord ++ tailWord_7244614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7244647 : List Nat := [1, 1, 5, 1, 2, 2, 2, 2, 1, 4, 2]
def baseStart_7244647 : Nat := 118140960795 + 7244647 * 2 ^ 59
def prefixEnd_7244647 : Nat := 4983230072969 + 3 ^ 40 * 7244647 * 2
def baseEnd_7244647 : Nat := 3719986083153222018994981

theorem tailTrace_7244647 : CollatzResearch.WordTrace tailWord_7244647 prefixEnd_7244647 3719986083153222018994981 := by
  unfold tailWord_7244647
  simp only [CollatzResearch.WordTrace]
  refine ⟨264233983784888681047244195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176155989189925787364829463 264233983784888681047244195)
  ·
    refine ⟨396350975677333021570866293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264233983784888681047244195 396350975677333021570866293)
    ·
      refine ⟨37157903969749970772268715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 396350975677333021570866293 37157903969749970772268715)
      ·
        refine ⟨55736855954624956158403073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37157903969749970772268715 55736855954624956158403073)
        ·
          refine ⟨41802641965968717118802305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55736855954624956158403073 41802641965968717118802305)
          ·
            refine ⟨31351981474476537839101729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41802641965968717118802305 31351981474476537839101729)
            ·
              refine ⟨23513986105857403379326297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31351981474476537839101729 23513986105857403379326297)
              ·
                refine ⟨17635489579393052534494723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23513986105857403379326297 17635489579393052534494723)
                ·
                  refine ⟨26453234369089578801742085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17635489579393052534494723 26453234369089578801742085)
                  ·
                    refine ⟨4959981444204296025326641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26453234369089578801742085 4959981444204296025326641)
                    ·
                      refine ⟨3719986083153222018994981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4959981444204296025326641 3719986083153222018994981)
                      ·
                        rfl

theorem cell23_7244647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 2, 2, 1, 4, 2].length) (baseStart_7244647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7244647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7244647 prefixEnd_7244647 := by exact prefixLift 7244647
  have htrace : WordTrace (prefixWord ++ tailWord_7244647) baseStart_7244647 baseEnd_7244647 := by
    simpa [prefixWord, tailWord_7244647, baseEnd_7244647] using wordTrace_append hprefix tailTrace_7244647
  have hstable : (prefixWord ++ tailWord_7244647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7244647).length < 2 ^ (prefixWord ++ tailWord_7244647).sum := by decide
  have hdescent : baseEnd_7244647 < baseStart_7244647 := by decide
  rcases family_descends (prefixWord ++ tailWord_7244647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7244653 : List Nat := [1, 5, 1, 1, 1, 1, 1, 1, 11]
def baseStart_7244653 : Nat := 118140960795 + 7244653 * 2 ^ 59
def prefixEnd_7244653 : Nat := 4983230072969 + 3 ^ 40 * 7244653 * 2
def baseEnd_7244653 : Nat := 413332129337460999502217

theorem tailTrace_7244653 : CollatzResearch.WordTrace tailWord_7244653 prefixEnd_7244653 413332129337460999502217 := by
  unfold tailWord_7244653
  simp only [CollatzResearch.WordTrace]
  refine ⟨264234202622866944071962613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176156135081911296047975075 264234202622866944071962613)
  ·
    refine ⟨24771956495893776006746495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 264234202622866944071962613 24771956495893776006746495)
    ·
      refine ⟨37157934743840664010119743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24771956495893776006746495 37157934743840664010119743)
      ·
        refine ⟨55736902115760996015179615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37157934743840664010119743 55736902115760996015179615)
        ·
          refine ⟨83605353173641494022769423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55736902115760996015179615 83605353173641494022769423)
          ·
            refine ⟨125408029760462241034154135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83605353173641494022769423 125408029760462241034154135)
            ·
              refine ⟨188112044640693361551231203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125408029760462241034154135 188112044640693361551231203)
              ·
                refine ⟨282168066961040042326846805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 188112044640693361551231203 282168066961040042326846805)
                ·
                  refine ⟨413332129337460999502217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 282168066961040042326846805 413332129337460999502217)
                  ·
                    rfl

theorem cell23_7244653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 1, 11].length) (baseStart_7244653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7244653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7244653 prefixEnd_7244653 := by exact prefixLift 7244653
  have htrace : WordTrace (prefixWord ++ tailWord_7244653) baseStart_7244653 baseEnd_7244653 := by
    simpa [prefixWord, tailWord_7244653, baseEnd_7244653] using wordTrace_append hprefix tailTrace_7244653
  have hstable : (prefixWord ++ tailWord_7244653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7244653).length < 2 ^ (prefixWord ++ tailWord_7244653).sum := by decide
  have hdescent : baseEnd_7244653 < baseStart_7244653 := by decide
  rcases family_descends (prefixWord ++ tailWord_7244653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7244681 : List Nat := [1, 2, 1, 1, 5, 3, 3, 1, 2, 2, 2]
def baseStart_7244681 : Nat := 118140960795 + 7244681 * 2 ^ 59
def prefixEnd_7244681 : Nat := 4983230072969 + 3 ^ 40 * 7244681 * 2
def baseEnd_7244681 : Nat := 3720003541495474885969825

theorem tailTrace_7244681 : CollatzResearch.WordTrace tailWord_7244681 prefixEnd_7244681 3720003541495474885969825 := by
  unfold tailWord_7244681
  simp only [CollatzResearch.WordTrace]
  refine ⟨264235223866765504853981897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176156815911177003235987931 264235223866765504853981897)
  ·
    refine ⟨198176417900074128640486423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 264235223866765504853981897 198176417900074128640486423)
    ·
      refine ⟨297264626850111192960729635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198176417900074128640486423 297264626850111192960729635)
      ·
        refine ⟨445896940275166789441094453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 297264626850111192960729635 445896940275166789441094453)
        ·
          refine ⟨41802838150796886510102605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 445896940275166789441094453 41802838150796886510102605)
          ·
            refine ⟨15676064306548832441288477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41802838150796886510102605 15676064306548832441288477)
            ·
              refine ⟨5878524114955812165483179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15676064306548832441288477 5878524114955812165483179)
              ·
                refine ⟨8817786172433718248224769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5878524114955812165483179 8817786172433718248224769)
                ·
                  refine ⟨6613339629325288686168577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8817786172433718248224769 6613339629325288686168577)
                  ·
                    refine ⟨4960004721993966514626433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6613339629325288686168577 4960004721993966514626433)
                    ·
                      refine ⟨3720003541495474885969825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4960004721993966514626433 3720003541495474885969825)
                      ·
                        rfl

theorem cell23_7244681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 3, 1, 2, 2, 2].length) (baseStart_7244681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7244681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7244681 prefixEnd_7244681 := by exact prefixLift 7244681
  have htrace : WordTrace (prefixWord ++ tailWord_7244681) baseStart_7244681 baseEnd_7244681 := by
    simpa [prefixWord, tailWord_7244681, baseEnd_7244681] using wordTrace_append hprefix tailTrace_7244681
  have hstable : (prefixWord ++ tailWord_7244681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7244681).length < 2 ^ (prefixWord ++ tailWord_7244681).sum := by decide
  have hdescent : baseEnd_7244681 < baseStart_7244681 := by decide
  rcases family_descends (prefixWord ++ tailWord_7244681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7244683 : List Nat := [1, 1, 1, 1, 4, 2, 3, 2, 1, 7]
def baseStart_7244683 : Nat := 118140960795 + 7244683 * 2 ^ 59
def prefixEnd_7244683 : Nat := 4983230072969 + 3 ^ 40 * 7244683 * 2
def baseEnd_7244683 : Nat := 1240001522818927959381605

theorem tailTrace_7244683 : CollatzResearch.WordTrace tailWord_7244683 prefixEnd_7244683 1240001522818927959381605 := by
  unfold tailWord_7244683
  simp only [CollatzResearch.WordTrace]
  refine ⟨264235296812758259195554703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176156864541838839463703135 264235296812758259195554703)
  ·
    refine ⟨396352945219137388793332055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264235296812758259195554703 396352945219137388793332055)
    ·
      refine ⟨594529417828706083189998083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 396352945219137388793332055 594529417828706083189998083)
      ·
        refine ⟨891794126743059124784997125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 594529417828706083189998083 891794126743059124784997125)
        ·
          refine ⟨167211398764323585897186961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 891794126743059124784997125 167211398764323585897186961)
          ·
            refine ⟨125408549073242689422890221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 167211398764323585897186961 125408549073242689422890221)
            ·
              refine ⟨47028205902466008533583833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 125408549073242689422890221 47028205902466008533583833)
              ·
                refine ⟨35271154426849506400187875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47028205902466008533583833 35271154426849506400187875)
                ·
                  refine ⟨52906731640274259600281813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35271154426849506400187875 52906731640274259600281813)
                  ·
                    refine ⟨1240001522818927959381605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 52906731640274259600281813 1240001522818927959381605)
                    ·
                      rfl

theorem cell23_7244683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 3, 2, 1, 7].length) (baseStart_7244683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7244683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7244683 prefixEnd_7244683 := by exact prefixLift 7244683
  have htrace : WordTrace (prefixWord ++ tailWord_7244683) baseStart_7244683 baseEnd_7244683 := by
    simpa [prefixWord, tailWord_7244683, baseEnd_7244683] using wordTrace_append hprefix tailTrace_7244683
  have hstable : (prefixWord ++ tailWord_7244683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7244683).length < 2 ^ (prefixWord ++ tailWord_7244683).sum := by decide
  have hdescent : baseEnd_7244683 < baseStart_7244683 := by decide
  rcases family_descends (prefixWord ++ tailWord_7244683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7244723 : List Nat := [1, 1, 1, 2, 3, 1, 2, 1, 1, 5, 5]
def baseStart_7244723 : Nat := 118140960795 + 7244723 * 2 ^ 59
def prefixEnd_7244723 : Nat := 4983230072969 + 3 ^ 40 * 7244723 * 2
def baseEnd_7244723 : Nat := 3720025107682963721644631

theorem tailTrace_7244723 : CollatzResearch.WordTrace tailWord_7244723 prefixEnd_7244723 3720025107682963721644631 := by
  unfold tailWord_7244723
  simp only [CollatzResearch.WordTrace]
  refine ⟨264236755732613346027010823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176157837155075564018007215 264236755732613346027010823)
  ·
    refine ⟨396355133598920019040516235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264236755732613346027010823 396355133598920019040516235)
    ·
      refine ⟨594532700398380028560774353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 396355133598920019040516235 594532700398380028560774353)
      ·
        refine ⟨445899525298785021420580765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 594532700398380028560774353 445899525298785021420580765)
        ·
          refine ⟨167212321987044383032717787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 445899525298785021420580765 167212321987044383032717787)
          ·
            refine ⟨250818482980566574549076681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 167212321987044383032717787 250818482980566574549076681)
            ·
              refine ⟨188113862235424930911807511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 250818482980566574549076681 188113862235424930911807511)
              ·
                refine ⟨282170793353137396367711267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 188113862235424930911807511 282170793353137396367711267)
                ·
                  refine ⟨423256190029706094551566901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 282170793353137396367711267 423256190029706094551566901)
                  ·
                    refine ⟨39680267815284946364209397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 423256190029706094551566901 39680267815284946364209397)
                    ·
                      refine ⟨3720025107682963721644631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39680267815284946364209397 3720025107682963721644631)
                      ·
                        rfl

theorem cell23_7244723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 1, 1, 5, 5].length) (baseStart_7244723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7244723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7244723 prefixEnd_7244723 := by exact prefixLift 7244723
  have htrace : WordTrace (prefixWord ++ tailWord_7244723) baseStart_7244723 baseEnd_7244723 := by
    simpa [prefixWord, tailWord_7244723, baseEnd_7244723] using wordTrace_append hprefix tailTrace_7244723
  have hstable : (prefixWord ++ tailWord_7244723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7244723).length < 2 ^ (prefixWord ++ tailWord_7244723).sum := by decide
  have hdescent : baseEnd_7244723 < baseStart_7244723 := by decide
  rcases family_descends (prefixWord ++ tailWord_7244723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7244754 : List Nat := [3, 2, 2, 3, 1, 2, 2, 1, 2, 1, 4]
def baseStart_7244754 : Nat := 118140960795 + 7244754 * 2 ^ 59
def prefixEnd_7244754 : Nat := 4983230072969 + 3 ^ 40 * 7244754 * 2
def baseEnd_7244754 : Nat := 3720041025583253100356989

theorem tailTrace_7244754 : CollatzResearch.WordTrace tailWord_7244754 prefixEnd_7244754 3720041025583253100356989 := by
  unfold tailWord_7244754
  simp only [CollatzResearch.WordTrace]
  refine ⟨66059471598875259580347329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176158590930334025547592877 66059471598875259580347329)
  ·
    refine ⟨49544603699156444685260497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66059471598875259580347329 49544603699156444685260497)
    ·
      refine ⟨37158452774367333513945373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49544603699156444685260497 37158452774367333513945373)
      ·
        refine ⟨13934419790387750067729515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37158452774367333513945373 13934419790387750067729515)
        ·
          refine ⟨20901629685581625101594273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13934419790387750067729515 20901629685581625101594273)
          ·
            refine ⟨15676222264186218826195705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20901629685581625101594273 15676222264186218826195705)
            ·
              refine ⟨11757166698139664119646779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15676222264186218826195705 11757166698139664119646779)
              ·
                refine ⟨17635750047209496179470169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11757166698139664119646779 17635750047209496179470169)
                ·
                  refine ⟨13226812535407122134602627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17635750047209496179470169 13226812535407122134602627)
                  ·
                    refine ⟨19840218803110683201903941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13226812535407122134602627 19840218803110683201903941)
                    ·
                      refine ⟨3720041025583253100356989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19840218803110683201903941 3720041025583253100356989)
                      ·
                        rfl

theorem cell23_7244754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 2, 1, 2, 1, 4].length) (baseStart_7244754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7244754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7244754 prefixEnd_7244754 := by exact prefixLift 7244754
  have htrace : WordTrace (prefixWord ++ tailWord_7244754) baseStart_7244754 baseEnd_7244754 := by
    simpa [prefixWord, tailWord_7244754, baseEnd_7244754] using wordTrace_append hprefix tailTrace_7244754
  have hstable : (prefixWord ++ tailWord_7244754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7244754).length < 2 ^ (prefixWord ++ tailWord_7244754).sum := by decide
  have hdescent : baseEnd_7244754 < baseStart_7244754 := by decide
  rcases family_descends (prefixWord ++ tailWord_7244754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7244797 : List Nat := [1, 4, 1, 1, 1, 2, 1, 4, 1, 5, 2]
def baseStart_7244797 : Nat := 118140960795 + 7244797 * 2 ^ 59
def prefixEnd_7244797 : Nat := 4983230072969 + 3 ^ 40 * 7244797 * 2
def baseEnd_7244797 : Nat := 3720063105251396432119291

theorem tailTrace_7244797 : CollatzResearch.WordTrace tailWord_7244797 prefixEnd_7244797 3720063105251396432119291 := by
  unfold tailWord_7244797
  simp only [CollatzResearch.WordTrace]
  refine ⟨264239454734345256665204645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176159636489563504443469763 264239454734345256665204645)
  ·
    refine ⟨49544897762689735624725871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 264239454734345256665204645 49544897762689735624725871)
    ·
      refine ⟨74317346644034603437088807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49544897762689735624725871 74317346644034603437088807)
      ·
        refine ⟨111476019966051905155633211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74317346644034603437088807 111476019966051905155633211)
        ·
          refine ⟨167214029949077857733449817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111476019966051905155633211 167214029949077857733449817)
          ·
            refine ⟨125410522461808393300087363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 167214029949077857733449817 125410522461808393300087363)
            ·
              refine ⟨188115783692712589950131045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125410522461808393300087363 188115783692712589950131045)
              ·
                refine ⟨35271709442383610615649571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 188115783692712589950131045 35271709442383610615649571)
                ·
                  refine ⟨52907564163575415923474357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35271709442383610615649571 52907564163575415923474357)
                  ·
                    refine ⟨4960084140335195242825721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 52907564163575415923474357 4960084140335195242825721)
                    ·
                      refine ⟨3720063105251396432119291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4960084140335195242825721 3720063105251396432119291)
                      ·
                        rfl

theorem cell23_7244797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 4, 1, 5, 2].length) (baseStart_7244797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7244797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7244797 prefixEnd_7244797 := by exact prefixLift 7244797
  have htrace : WordTrace (prefixWord ++ tailWord_7244797) baseStart_7244797 baseEnd_7244797 := by
    simpa [prefixWord, tailWord_7244797, baseEnd_7244797] using wordTrace_append hprefix tailTrace_7244797
  have hstable : (prefixWord ++ tailWord_7244797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7244797).length < 2 ^ (prefixWord ++ tailWord_7244797).sum := by decide
  have hdescent : baseEnd_7244797 < baseStart_7244797 := by decide
  rcases family_descends (prefixWord ++ tailWord_7244797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7244807 : List Nat := [1, 1, 4, 3, 1, 1, 2, 4, 1, 5]
def baseStart_7244807 : Nat := 118140960795 + 7244807 * 2 ^ 59
def prefixEnd_7244807 : Nat := 4983230072969 + 3 ^ 40 * 7244807 * 2
def baseEnd_7244807 : Nat := 1240022746685980464331415

theorem tailTrace_7244807 : CollatzResearch.WordTrace tailWord_7244807 prefixEnd_7244807 1240022746685980464331415 := by
  unfold tailWord_7244807
  simp only [CollatzResearch.WordTrace]
  refine ⟨264239819464309028373068675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176159879642872685582045783 264239819464309028373068675)
  ·
    refine ⟨396359729196463542559603013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264239819464309028373068675 396359729196463542559603013)
    ·
      refine ⟨74317449224336914229925565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 396359729196463542559603013 74317449224336914229925565)
      ·
        refine ⟨27869043459126342836222087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74317449224336914229925565 27869043459126342836222087)
        ·
          refine ⟨41803565188689514254333131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27869043459126342836222087 41803565188689514254333131)
          ·
            refine ⟨62705347783034271381499697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41803565188689514254333131 62705347783034271381499697)
            ·
              refine ⟨47029010837275703536124773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62705347783034271381499697 47029010837275703536124773)
              ·
                refine ⟨8817939531989194413023395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47029010837275703536124773 8817939531989194413023395)
                ·
                  refine ⟨13226909297983791619535093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8817939531989194413023395 13226909297983791619535093)
                  ·
                    refine ⟨1240022746685980464331415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13226909297983791619535093 1240022746685980464331415)
                    ·
                      rfl

theorem cell23_7244807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 2, 4, 1, 5].length) (baseStart_7244807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7244807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7244807 prefixEnd_7244807 := by exact prefixLift 7244807
  have htrace : WordTrace (prefixWord ++ tailWord_7244807) baseStart_7244807 baseEnd_7244807 := by
    simpa [prefixWord, tailWord_7244807, baseEnd_7244807] using wordTrace_append hprefix tailTrace_7244807
  have hstable : (prefixWord ++ tailWord_7244807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7244807).length < 2 ^ (prefixWord ++ tailWord_7244807).sum := by decide
  have hdescent : baseEnd_7244807 < baseStart_7244807 := by decide
  rcases family_descends (prefixWord ++ tailWord_7244807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7244814 : List Nat := [4, 1, 1, 2, 2, 3, 1, 1, 1, 5, 2]
def baseStart_7244814 : Nat := 118140960795 + 7244814 * 2 ^ 59
def prefixEnd_7244814 : Nat := 4983230072969 + 3 ^ 40 * 7244814 * 2
def baseEnd_7244814 : Nat := 3720071834422522865606713

theorem tailTrace_7244814 : CollatzResearch.WordTrace tailWord_7244814 prefixEnd_7244814 3720071834422522865606713 := by
  unfold tailWord_7244814
  simp only [CollatzResearch.WordTrace]
  refine ⟨33030009346910458571071687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 176160049850189112379048997 33030009346910458571071687)
  ·
    refine ⟨49545014020365687856607531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33030009346910458571071687 49545014020365687856607531)
    ·
      refine ⟨74317521030548531784911297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49545014020365687856607531 74317521030548531784911297)
      ·
        refine ⟨55738140772911398838683473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74317521030548531784911297 55738140772911398838683473)
        ·
          refine ⟨41803605579683549129012605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55738140772911398838683473 41803605579683549129012605)
          ·
            refine ⟨15676352092381330923379727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41803605579683549129012605 15676352092381330923379727)
            ·
              refine ⟨23514528138571996385069591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15676352092381330923379727 23514528138571996385069591)
              ·
                refine ⟨35271792207857994577604387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23514528138571996385069591 35271792207857994577604387)
                ·
                  refine ⟨52907688311786991866406581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35271792207857994577604387 52907688311786991866406581)
                  ·
                    refine ⟨4960095779230030487475617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 52907688311786991866406581 4960095779230030487475617)
                    ·
                      refine ⟨3720071834422522865606713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4960095779230030487475617 3720071834422522865606713)
                      ·
                        rfl

theorem cell23_7244814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 1, 1, 1, 5, 2].length) (baseStart_7244814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7244814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7244814 prefixEnd_7244814 := by exact prefixLift 7244814
  have htrace : WordTrace (prefixWord ++ tailWord_7244814) baseStart_7244814 baseEnd_7244814 := by
    simpa [prefixWord, tailWord_7244814, baseEnd_7244814] using wordTrace_append hprefix tailTrace_7244814
  have hstable : (prefixWord ++ tailWord_7244814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7244814).length < 2 ^ (prefixWord ++ tailWord_7244814).sum := by decide
  have hdescent : baseEnd_7244814 < baseStart_7244814 := by decide
  rcases family_descends (prefixWord ++ tailWord_7244814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7244821 : List Nat := [1, 3, 2, 1, 4, 1, 1, 5, 1, 1, 3]
def baseStart_7244821 : Nat := 118140960795 + 7244821 * 2 ^ 59
def prefixEnd_7244821 : Nat := 4983230072969 + 3 ^ 40 * 7244821 * 2
def baseEnd_7244821 : Nat := 3720075428787104338219181

theorem tailTrace_7244821 : CollatzResearch.WordTrace tailWord_7244821 prefixEnd_7244821 3720075428787104338219181 := by
  unfold tailWord_7244821
  simp only [CollatzResearch.WordTrace]
  refine ⟨264240330086258308764078317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176160220057505539176052211 264240330086258308764078317)
  ·
    refine ⟨99090123782346865786529369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 264240330086258308764078317 99090123782346865786529369)
    ·
      refine ⟨74317592836760149339897027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99090123782346865786529369 74317592836760149339897027)
      ·
        refine ⟨111476389255140224009845541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74317592836760149339897027 111476389255140224009845541)
        ·
          refine ⟨20901822985338792001846039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 111476389255140224009845541 20901822985338792001846039)
          ·
            refine ⟨31352734478008188002769059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20901822985338792001846039 31352734478008188002769059)
            ·
              refine ⟨47029101717012282004153589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31352734478008188002769059 47029101717012282004153589)
              ·
                refine ⟨4408978285969901437889399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 47029101717012282004153589 4408978285969901437889399)
                ·
                  refine ⟨6613467428954852156834099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4408978285969901437889399 6613467428954852156834099)
                  ·
                    refine ⟨9920201143432278235251149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6613467428954852156834099 9920201143432278235251149)
                    ·
                      refine ⟨3720075428787104338219181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9920201143432278235251149 3720075428787104338219181)
                      ·
                        rfl

theorem cell23_7244821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 1, 5, 1, 1, 3].length) (baseStart_7244821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7244821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7244821 prefixEnd_7244821 := by exact prefixLift 7244821
  have htrace : WordTrace (prefixWord ++ tailWord_7244821) baseStart_7244821 baseEnd_7244821 := by
    simpa [prefixWord, tailWord_7244821, baseEnd_7244821] using wordTrace_append hprefix tailTrace_7244821
  have hstable : (prefixWord ++ tailWord_7244821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7244821).length < 2 ^ (prefixWord ++ tailWord_7244821).sum := by decide
  have hdescent : baseEnd_7244821 < baseStart_7244821 := by decide
  rcases family_descends (prefixWord ++ tailWord_7244821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7244824 : List Nat := [2, 1, 2, 3, 2, 2, 4, 1, 1, 5]
def baseStart_7244824 : Nat := 118140960795 + 7244824 * 2 ^ 59
def prefixEnd_7244824 : Nat := 4983230072969 + 3 ^ 40 * 7244824 * 2
def baseEnd_7244824 : Nat := 1240025656409689275493889

theorem tailTrace_7244824 : CollatzResearch.WordTrace tailWord_7244824 prefixEnd_7244824 1240025656409689275493889 := by
  unfold tailWord_7244824
  simp only [CollatzResearch.WordTrace]
  refine ⟨132120219752623720138218763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176160293003498293517625017 132120219752623720138218763)
  ·
    refine ⟨198180329628935580207328145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132120219752623720138218763 198180329628935580207328145)
    ·
      refine ⟨148635247221701685155496109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 198180329628935580207328145 148635247221701685155496109)
      ·
        refine ⟨55738217708138131933311041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 148635247221701685155496109 55738217708138131933311041)
        ·
          refine ⟨41803663281103598949983281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55738217708138131933311041 41803663281103598949983281)
          ·
            refine ⟨31352747460827699212487461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41803663281103598949983281 31352747460827699212487461)
            ·
              refine ⟨5878640148905193602341399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31352747460827699212487461 5878640148905193602341399)
              ·
                refine ⟨8817960223357790403512099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5878640148905193602341399 8817960223357790403512099)
                ·
                  refine ⟨13226940335036685605268149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8817960223357790403512099 13226940335036685605268149)
                  ·
                    refine ⟨1240025656409689275493889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13226940335036685605268149 1240025656409689275493889)
                    ·
                      rfl

theorem cell23_7244824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 4, 1, 1, 5].length) (baseStart_7244824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7244824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7244824 prefixEnd_7244824 := by exact prefixLift 7244824
  have htrace : WordTrace (prefixWord ++ tailWord_7244824) baseStart_7244824 baseEnd_7244824 := by
    simpa [prefixWord, tailWord_7244824, baseEnd_7244824] using wordTrace_append hprefix tailTrace_7244824
  have hstable : (prefixWord ++ tailWord_7244824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7244824).length < 2 ^ (prefixWord ++ tailWord_7244824).sum := by decide
  have hdescent : baseEnd_7244824 < baseStart_7244824 := by decide
  rcases family_descends (prefixWord ++ tailWord_7244824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7244837 : List Nat := [1, 3, 1, 2, 2, 2, 3, 1, 4, 4]
def baseStart_7244837 : Nat := 118140960795 + 7244837 * 2 ^ 59
def prefixEnd_7244837 : Nat := 4983230072969 + 3 ^ 40 * 7244837 * 2
def baseEnd_7244837 : Nat := 1240027881492525425206369

theorem tailTrace_7244837 : CollatzResearch.WordTrace tailWord_7244837 prefixEnd_7244837 1240027881492525425206369 := by
  unfold tailWord_7244837
  simp only [CollatzResearch.WordTrace]
  refine ⟨264240913654200343496660765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176160609102800228997773843 264240913654200343496660765)
  ·
    refine ⟨99090342620325128811247787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 264240913654200343496660765 99090342620325128811247787)
    ·
      refine ⟨148635513930487693216871681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99090342620325128811247787 148635513930487693216871681)
      ·
        refine ⟨111476635447865769912653761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148635513930487693216871681 111476635447865769912653761)
        ·
          refine ⟨83607476585899327434490321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111476635447865769912653761 83607476585899327434490321)
          ·
            refine ⟨62705607439424495575867741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83607476585899327434490321 62705607439424495575867741)
            ·
              refine ⟨23514602789784185840950403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62705607439424495575867741 23514602789784185840950403)
              ·
                refine ⟨35271904184676278761425605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23514602789784185840950403 35271904184676278761425605)
                ·
                  refine ⟨6613482034626802267767301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35271904184676278761425605 6613482034626802267767301)
                  ·
                    refine ⟨1240027881492525425206369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6613482034626802267767301 1240027881492525425206369)
                    ·
                      rfl

theorem cell23_7244837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 3, 1, 4, 4].length) (baseStart_7244837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7244837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7244837 prefixEnd_7244837 := by exact prefixLift 7244837
  have htrace : WordTrace (prefixWord ++ tailWord_7244837) baseStart_7244837 baseEnd_7244837 := by
    simpa [prefixWord, tailWord_7244837, baseEnd_7244837] using wordTrace_append hprefix tailTrace_7244837
  have hstable : (prefixWord ++ tailWord_7244837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7244837).length < 2 ^ (prefixWord ++ tailWord_7244837).sum := by decide
  have hdescent : baseEnd_7244837 < baseStart_7244837 := by decide
  rcases family_descends (prefixWord ++ tailWord_7244837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7244850 : List Nat := [3, 2, 1, 1, 2, 2, 2, 10]
def baseStart_7244850 : Nat := 118140960795 + 7244850 * 2 ^ 59
def prefixEnd_7244850 : Nat := 4983230072969 + 3 ^ 40 * 7244850 * 2
def baseEnd_7244850 : Nat := 137781122952817952768761

theorem tailTrace_7244850 : CollatzResearch.WordTrace tailWord_7244850 prefixEnd_7244850 137781122952817952768761 := by
  unfold tailWord_7244850
  simp only [CollatzResearch.WordTrace]
  refine ⟨66060346950788311679221001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176160925202102164477922669 66060346950788311679221001)
  ·
    refine ⟨49545260213091233759415751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66060346950788311679221001 49545260213091233759415751)
    ·
      refine ⟨74317890319636850639123627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49545260213091233759415751 74317890319636850639123627)
      ·
        refine ⟨111476835479455275958685441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74317890319636850639123627 111476835479455275958685441)
        ·
          refine ⟨83607626609591456969014081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111476835479455275958685441 83607626609591456969014081)
          ·
            refine ⟨62705719957193592726760561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83607626609591456969014081 62705719957193592726760561)
            ·
              refine ⟨47029289967895194545070421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62705719957193592726760561 47029289967895194545070421)
              ·
                refine ⟨137781122952817952768761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 47029289967895194545070421 137781122952817952768761)
                ·
                  rfl

theorem cell23_7244850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 2, 10].length) (baseStart_7244850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7244850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7244850 prefixEnd_7244850 := by exact prefixLift 7244850
  have htrace : WordTrace (prefixWord ++ tailWord_7244850) baseStart_7244850 baseEnd_7244850 := by
    simpa [prefixWord, tailWord_7244850, baseEnd_7244850] using wordTrace_append hprefix tailTrace_7244850
  have hstable : (prefixWord ++ tailWord_7244850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7244850).length < 2 ^ (prefixWord ++ tailWord_7244850).sum := by decide
  have hdescent : baseEnd_7244850 < baseStart_7244850 := by decide
  rcases family_descends (prefixWord ++ tailWord_7244850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7244854 : List Nat := [5, 1, 2, 1, 1, 2, 3, 1, 1, 6]
def baseStart_7244854 : Nat := 118140960795 + 7244854 * 2 ^ 59
def prefixEnd_7244854 : Nat := 4983230072969 + 3 ^ 40 * 7244854 * 2
def baseEnd_7244854 : Nat := 1240030791216234236368843

theorem tailTrace_7244854 : CollatzResearch.WordTrace tailWord_7244854 prefixEnd_7244854 1240030791216234236368843 := by
  unfold tailWord_7244854
  simp only [CollatzResearch.WordTrace]
  refine ⟨16515095855946172212501851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 176161022463425836933353077 16515095855946172212501851)
  ·
    refine ⟨24772643783919258318752777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16515095855946172212501851 24772643783919258318752777)
    ·
      refine ⟨18579482837939443739064583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24772643783919258318752777 18579482837939443739064583)
      ·
        refine ⟨27869224256909165608596875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18579482837939443739064583 27869224256909165608596875)
        ·
          refine ⟨41803836385363748412895313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27869224256909165608596875 41803836385363748412895313)
          ·
            refine ⟨31352877289022811309671485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41803836385363748412895313 31352877289022811309671485)
            ·
              refine ⟨11757328983383554241126807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31352877289022811309671485 11757328983383554241126807)
              ·
                refine ⟨17635993475075331361690211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11757328983383554241126807 17635993475075331361690211)
                ·
                  refine ⟨26453990212612997042535317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17635993475075331361690211 26453990212612997042535317)
                  ·
                    refine ⟨1240030791216234236368843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26453990212612997042535317 1240030791216234236368843)
                    ·
                      rfl

theorem cell23_7244854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 3, 1, 1, 6].length) (baseStart_7244854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7244854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7244854 prefixEnd_7244854 := by exact prefixLift 7244854
  have htrace : WordTrace (prefixWord ++ tailWord_7244854) baseStart_7244854 baseEnd_7244854 := by
    simpa [prefixWord, tailWord_7244854, baseEnd_7244854] using wordTrace_append hprefix tailTrace_7244854
  have hstable : (prefixWord ++ tailWord_7244854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7244854).length < 2 ^ (prefixWord ++ tailWord_7244854).sum := by decide
  have hdescent : baseEnd_7244854 < baseStart_7244854 := by decide
  rcases family_descends (prefixWord ++ tailWord_7244854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7244857 : List Nat := [1, 2, 1, 5, 2, 2, 1, 1, 1, 1, 6]
def baseStart_7244857 : Nat := 118140960795 + 7244857 * 2 ^ 59
def prefixEnd_7244857 : Nat := 4983230072969 + 3 ^ 40 * 7244857 * 2
def baseEnd_7244857 : Nat := 3720093914090666197369015

theorem tailTrace_7244857 : CollatzResearch.WordTrace tailWord_7244857 prefixEnd_7244857 3720093914090666197369015 := by
  unfold tailWord_7244857
  simp only [CollatzResearch.WordTrace]
  refine ⟨264241643114127886912388825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176161095409418591274925883 264241643114127886912388825)
  ·
    refine ⟨198181232335595915184291619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 264241643114127886912388825 198181232335595915184291619)
    ·
      refine ⟨297271848503393872776437429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198181232335595915184291619 297271848503393872776437429)
      ·
        refine ⟨27869235797193175572791009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 297271848503393872776437429 27869235797193175572791009)
        ·
          refine ⟨20901926847894881679593257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27869235797193175572791009 20901926847894881679593257)
          ·
            refine ⟨15676445135921161259694943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20901926847894881679593257 15676445135921161259694943)
            ·
              refine ⟨23514667703881741889542415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15676445135921161259694943 23514667703881741889542415)
              ·
                refine ⟨35272001555822612834313623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23514667703881741889542415 35272001555822612834313623)
                ·
                  refine ⟨52908002333733919251470435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35272001555822612834313623 52908002333733919251470435)
                  ·
                    refine ⟨79362003500600878877205653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 52908002333733919251470435 79362003500600878877205653)
                    ·
                      refine ⟨3720093914090666197369015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 79362003500600878877205653 3720093914090666197369015)
                      ·
                        rfl

theorem cell23_7244857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 1, 1, 1, 1, 6].length) (baseStart_7244857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7244857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7244857 prefixEnd_7244857 := by exact prefixLift 7244857
  have htrace : WordTrace (prefixWord ++ tailWord_7244857) baseStart_7244857 baseEnd_7244857 := by
    simpa [prefixWord, tailWord_7244857, baseEnd_7244857] using wordTrace_append hprefix tailTrace_7244857
  have hstable : (prefixWord ++ tailWord_7244857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7244857).length < 2 ^ (prefixWord ++ tailWord_7244857).sum := by decide
  have hdescent : baseEnd_7244857 < baseStart_7244857 := by decide
  rcases family_descends (prefixWord ++ tailWord_7244857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7244861 : List Nat := [1, 4, 1, 3, 1, 2, 2, 2, 3, 2, 2]
def baseStart_7244861 : Nat := 118140960795 + 7244861 * 2 ^ 59
def prefixEnd_7244861 : Nat := 4983230072969 + 3 ^ 40 * 7244861 * 2
def baseEnd_7244861 : Nat := 3720095968013284181718997

theorem tailTrace_7244861 : CollatzResearch.WordTrace tailWord_7244861 prefixEnd_7244861 3720095968013284181718997 := by
  unfold tailWord_7244861
  simp only [CollatzResearch.WordTrace]
  refine ⟨264241789006113395595534437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176161192670742263730356291 264241789006113395595534437)
  ·
    refine ⟨49545335438646261674162707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 264241789006113395595534437 49545335438646261674162707)
    ·
      refine ⟨74318003157969392511244061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49545335438646261674162707 74318003157969392511244061)
      ·
        refine ⟨27869251184238522191716523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74318003157969392511244061 27869251184238522191716523)
        ·
          refine ⟨41803876776357783287574785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27869251184238522191716523 41803876776357783287574785)
          ·
            refine ⟨31352907582268337465681089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41803876776357783287574785 31352907582268337465681089)
            ·
              refine ⟨23514680686701253099260817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31352907582268337465681089 23514680686701253099260817)
              ·
                refine ⟨17636010515025939824445613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23514680686701253099260817 17636010515025939824445613)
                ·
                  refine ⟨6613503943134727434167105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17636010515025939824445613 6613503943134727434167105)
                  ·
                    refine ⟨4960127957351045575625329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6613503943134727434167105 4960127957351045575625329)
                    ·
                      refine ⟨3720095968013284181718997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4960127957351045575625329 3720095968013284181718997)
                      ·
                        rfl

theorem cell23_7244861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 2, 2, 3, 2, 2].length) (baseStart_7244861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7244861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7244861 prefixEnd_7244861 := by exact prefixLift 7244861
  have htrace : WordTrace (prefixWord ++ tailWord_7244861) baseStart_7244861 baseEnd_7244861 := by
    simpa [prefixWord, tailWord_7244861, baseEnd_7244861] using wordTrace_append hprefix tailTrace_7244861
  have hstable : (prefixWord ++ tailWord_7244861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7244861).length < 2 ^ (prefixWord ++ tailWord_7244861).sum := by decide
  have hdescent : baseEnd_7244861 < baseStart_7244861 := by decide
  rcases family_descends (prefixWord ++ tailWord_7244861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7244864 : List Nat := [2, 1, 1, 2, 2, 3, 4, 2, 1, 2, 3]
def baseStart_7244864 : Nat := 118140960795 + 7244864 * 2 ^ 59
def prefixEnd_7244864 : Nat := 4983230072969 + 3 ^ 40 * 7244864 * 2
def baseEnd_7244864 : Nat := 3720097508455247669981483

theorem tailTrace_7244864 : CollatzResearch.WordTrace tailWord_7244864 prefixEnd_7244864 3720097508455247669981483 := by
  unfold tailWord_7244864
  simp only [CollatzResearch.WordTrace]
  refine ⟨132120949212551263553946823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176161265616735018071929097 132120949212551263553946823)
  ·
    refine ⟨198181423818826895330920235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132120949212551263553946823 198181423818826895330920235)
    ·
      refine ⟨297272135728240342996380353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198181423818826895330920235 297272135728240342996380353)
      ·
        refine ⟨222954101796180257247285265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 297272135728240342996380353 222954101796180257247285265)
        ·
          refine ⟨167215576347135192935463949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 222954101796180257247285265 167215576347135192935463949)
          ·
            refine ⟨62705841130175697350798981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 167215576347135192935463949 62705841130175697350798981)
            ·
              refine ⟨11757345211907943253274809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 62705841130175697350798981 11757345211907943253274809)
              ·
                refine ⟨8818008908930957439956107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11757345211907943253274809 8818008908930957439956107)
                ·
                  refine ⟨13227013363396436159934161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8818008908930957439956107 13227013363396436159934161)
                  ·
                    refine ⟨9920260022547327119950621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13227013363396436159934161 9920260022547327119950621)
                    ·
                      refine ⟨3720097508455247669981483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9920260022547327119950621 3720097508455247669981483)
                      ·
                        rfl

theorem cell23_7244864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 4, 2, 1, 2, 3].length) (baseStart_7244864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7244864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7244864 prefixEnd_7244864 := by exact prefixLift 7244864
  have htrace : WordTrace (prefixWord ++ tailWord_7244864) baseStart_7244864 baseEnd_7244864 := by
    simpa [prefixWord, tailWord_7244864, baseEnd_7244864] using wordTrace_append hprefix tailTrace_7244864
  have hstable : (prefixWord ++ tailWord_7244864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7244864).length < 2 ^ (prefixWord ++ tailWord_7244864).sum := by decide
  have hdescent : baseEnd_7244864 < baseStart_7244864 := by decide
  rcases family_descends (prefixWord ++ tailWord_7244864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7244921 : List Nat := [1, 2, 1, 3, 5, 1, 1, 1, 3, 3, 2]
def baseStart_7244921 : Nat := 118140960795 + 7244921 * 2 ^ 59
def prefixEnd_7244921 : Nat := 4983230072969 + 3 ^ 40 * 7244921 * 2
def baseEnd_7244921 : Nat := 3720126776852553946968721

theorem tailTrace_7244921 : CollatzResearch.WordTrace tailWord_7244921 prefixEnd_7244921 3720126776852553946968721 := by
  unfold tailWord_7244921
  simp only [CollatzResearch.WordTrace]
  refine ⟨264243977385896025842718617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176162651590597350561812411 264243977385896025842718617)
  ·
    refine ⟨198182983039422019382038963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 264243977385896025842718617 198182983039422019382038963)
    ·
      refine ⟨297274474559133029073058445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198182983039422019382038963 297274474559133029073058445)
      ·
        refine ⟨111477927959674885902396917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 297274474559133029073058445 111477927959674885902396917)
        ·
          refine ⟨10451055746219520553349711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 111477927959674885902396917 10451055746219520553349711)
          ·
            refine ⟨15676583619329280830024567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10451055746219520553349711 15676583619329280830024567)
            ·
              refine ⟨23514875428993921245036851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15676583619329280830024567 23514875428993921245036851)
              ·
                refine ⟨35272313143490881867555277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23514875428993921245036851 35272313143490881867555277)
                ·
                  refine ⟨13227117428809080700333229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35272313143490881867555277 13227117428809080700333229)
                  ·
                    refine ⟨4960169035803405262624961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13227117428809080700333229 4960169035803405262624961)
                    ·
                      refine ⟨3720126776852553946968721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4960169035803405262624961 3720126776852553946968721)
                      ·
                        rfl

theorem cell23_7244921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 1, 1, 3, 3, 2].length) (baseStart_7244921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7244921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7244921 prefixEnd_7244921 := by exact prefixLift 7244921
  have htrace : WordTrace (prefixWord ++ tailWord_7244921) baseStart_7244921 baseEnd_7244921 := by
    simpa [prefixWord, tailWord_7244921, baseEnd_7244921] using wordTrace_append hprefix tailTrace_7244921
  have hstable : (prefixWord ++ tailWord_7244921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7244921).length < 2 ^ (prefixWord ++ tailWord_7244921).sum := by decide
  have hdescent : baseEnd_7244921 < baseStart_7244921 := by decide
  rcases family_descends (prefixWord ++ tailWord_7244921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7244937 : List Nat := [1, 2, 1, 1, 4, 3, 2, 1, 2, 1, 5]
def baseStart_7244937 : Nat := 118140960795 + 7244937 * 2 ^ 59
def prefixEnd_7244937 : Nat := 4983230072969 + 3 ^ 40 * 7244937 * 2
def baseEnd_7244937 : Nat := 3720134992543025884368647

theorem tailTrace_7244937 : CollatzResearch.WordTrace tailWord_7244937 prefixEnd_7244937 3720134992543025884368647 := by
  unfold tailWord_7244937
  simp only [CollatzResearch.WordTrace]
  refine ⟨264244560953838060575301065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176163040635892040383534043 264244560953838060575301065)
  ·
    refine ⟨198183420715378545431475799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 264244560953838060575301065 198183420715378545431475799)
    ·
      refine ⟨297275131073067818147213699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198183420715378545431475799 297275131073067818147213699)
      ·
        refine ⟨445912696609601727220820549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 297275131073067818147213699 445912696609601727220820549)
        ·
          refine ⟨83608630614300323853903853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 445912696609601727220820549 83608630614300323853903853)
          ·
            refine ⟨31353236480362621445213945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 83608630614300323853903853 31353236480362621445213945)
            ·
              refine ⟨23514927360271966083910459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31353236480362621445213945 23514927360271966083910459)
              ·
                refine ⟨35272391040407949125865689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23514927360271966083910459 35272391040407949125865689)
                ·
                  refine ⟨26454293280305961844399267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35272391040407949125865689 26454293280305961844399267)
                  ·
                    refine ⟨39681439920458942766598901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26454293280305961844399267 39681439920458942766598901)
                    ·
                      refine ⟨3720134992543025884368647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39681439920458942766598901 3720134992543025884368647)
                      ·
                        rfl

theorem cell23_7244937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 2, 1, 2, 1, 5].length) (baseStart_7244937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7244937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7244937 prefixEnd_7244937 := by exact prefixLift 7244937
  have htrace : WordTrace (prefixWord ++ tailWord_7244937) baseStart_7244937 baseEnd_7244937 := by
    simpa [prefixWord, tailWord_7244937, baseEnd_7244937] using wordTrace_append hprefix tailTrace_7244937
  have hstable : (prefixWord ++ tailWord_7244937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7244937).length < 2 ^ (prefixWord ++ tailWord_7244937).sum := by decide
  have hdescent : baseEnd_7244937 < baseStart_7244937 := by decide
  rcases family_descends (prefixWord ++ tailWord_7244937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7244938 : List Nat := [3, 1, 2, 3, 1, 1, 5, 1, 1, 3, 2]
def baseStart_7244938 : Nat := 118140960795 + 7244938 * 2 ^ 59
def prefixEnd_7244938 : Nat := 4983230072969 + 3 ^ 40 * 7244938 * 2
def baseEnd_7244938 : Nat := 3720135506023680380456143

theorem tailTrace_7244938 : CollatzResearch.WordTrace tailWord_7244938 prefixEnd_7244938 3720135506023680380456143 := by
  unfold tailWord_7244938
  simp only [CollatzResearch.WordTrace]
  refine ⟨66061149356708609436521867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176163064951222958497391645 66061149356708609436521867)
  ·
    refine ⟨99091724035062914154782801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66061149356708609436521867 99091724035062914154782801)
    ·
      refine ⟨74318793026297185616087101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99091724035062914154782801 74318793026297185616087101)
      ·
        refine ⟨27869547384861444606032663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74318793026297185616087101 27869547384861444606032663)
        ·
          refine ⟨41804321077292166909048995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27869547384861444606032663 41804321077292166909048995)
          ·
            refine ⟨62706481615938250363573493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41804321077292166909048995 62706481615938250363573493)
            ·
              refine ⟨5878732651494210971585015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 62706481615938250363573493 5878732651494210971585015)
              ·
                refine ⟨8818098977241316457377523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5878732651494210971585015 8818098977241316457377523)
                ·
                  refine ⟨13227148465861974686066285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8818098977241316457377523 13227148465861974686066285)
                  ·
                    refine ⟨4960180674698240507274857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13227148465861974686066285 4960180674698240507274857)
                    ·
                      refine ⟨3720135506023680380456143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4960180674698240507274857 3720135506023680380456143)
                      ·
                        rfl

theorem cell23_7244938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 5, 1, 1, 3, 2].length) (baseStart_7244938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7244938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7244938 prefixEnd_7244938 := by exact prefixLift 7244938
  have htrace : WordTrace (prefixWord ++ tailWord_7244938) baseStart_7244938 baseEnd_7244938 := by
    simpa [prefixWord, tailWord_7244938, baseEnd_7244938] using wordTrace_append hprefix tailTrace_7244938
  have hstable : (prefixWord ++ tailWord_7244938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7244938).length < 2 ^ (prefixWord ++ tailWord_7244938).sum := by decide
  have hdescent : baseEnd_7244938 < baseStart_7244938 := by decide
  rcases family_descends (prefixWord ++ tailWord_7244938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7244954 : List Nat := [3, 1, 1, 5, 1, 1, 1, 1, 2, 4, 3]
def baseStart_7244954 : Nat := 118140960795 + 7244954 * 2 ^ 59
def prefixEnd_7244954 : Nat := 4983230072969 + 3 ^ 40 * 7244954 * 2
def baseEnd_7244954 : Nat := 3720143721714152317856069

theorem tailTrace_7244954 : CollatzResearch.WordTrace tailWord_7244954 prefixEnd_7244954 3720143721714152317856069 := by
  unfold tailWord_7244954
  simp only [CollatzResearch.WordTrace]
  refine ⟨66061295248694118119667479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176163453996517648319113277 66061295248694118119667479)
  ·
    refine ⟨99091942873041177179501219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66061295248694118119667479 99091942873041177179501219)
    ·
      refine ⟨148637914309561765769251829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99091942873041177179501219 148637914309561765769251829)
      ·
        refine ⟨13934804466521415540867359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 148637914309561765769251829 13934804466521415540867359)
        ·
          refine ⟨20902206699782123311301039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13934804466521415540867359 20902206699782123311301039)
          ·
            refine ⟨31353310049673184966951559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20902206699782123311301039 31353310049673184966951559)
            ·
              refine ⟨47029965074509777450427339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31353310049673184966951559 47029965074509777450427339)
              ·
                refine ⟨70544947611764666175641009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47029965074509777450427339 70544947611764666175641009)
                ·
                  refine ⟨52908710708823499631730757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 70544947611764666175641009 52908710708823499631730757)
                  ·
                    refine ⟨9920383257904406180949517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 52908710708823499631730757 9920383257904406180949517)
                    ·
                      refine ⟨3720143721714152317856069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9920383257904406180949517 3720143721714152317856069)
                      ·
                        rfl

theorem cell23_7244954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 1, 1, 2, 4, 3].length) (baseStart_7244954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7244954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7244954 prefixEnd_7244954 := by exact prefixLift 7244954
  have htrace : WordTrace (prefixWord ++ tailWord_7244954) baseStart_7244954 baseEnd_7244954 := by
    simpa [prefixWord, tailWord_7244954, baseEnd_7244954] using wordTrace_append hprefix tailTrace_7244954
  have hstable : (prefixWord ++ tailWord_7244954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7244954).length < 2 ^ (prefixWord ++ tailWord_7244954).sum := by decide
  have hdescent : baseEnd_7244954 < baseStart_7244954 := by decide
  rcases family_descends (prefixWord ++ tailWord_7244954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7244957 : List Nat := [1, 4, 2, 1, 1, 2, 2, 3, 7]
def baseStart_7244957 : Nat := 118140960795 + 7244957 * 2 ^ 59
def prefixEnd_7244957 : Nat := 4983230072969 + 3 ^ 40 * 7244957 * 2
def baseEnd_7244957 : Nat := 413349473572901756235395

theorem tailTrace_7244957 : CollatzResearch.WordTrace tailWord_7244957 prefixEnd_7244957 413349473572901756235395 := by
  unfold tailWord_7244957
  simp only [CollatzResearch.WordTrace]
  refine ⟨264245290413765603991029125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176163526942510402660686083 264245290413765603991029125)
  ·
    refine ⟨49545991952581050748317961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 264245290413765603991029125 49545991952581050748317961)
    ·
      refine ⟨37159493964435788061238471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49545991952581050748317961 37159493964435788061238471)
      ·
        refine ⟨55739240946653682091857707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37159493964435788061238471 55739240946653682091857707)
        ·
          refine ⟨83608861419980523137786561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55739240946653682091857707 83608861419980523137786561)
          ·
            refine ⟨62706646064985392353339921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83608861419980523137786561 62706646064985392353339921)
            ·
              refine ⟨47029984548739044265004941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62706646064985392353339921 47029984548739044265004941)
              ·
                refine ⟨17636244205777141599376853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47029984548739044265004941 17636244205777141599376853)
                ·
                  refine ⟨413349473572901756235395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17636244205777141599376853 413349473572901756235395)
                  ·
                    rfl

theorem cell23_7244957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 2, 3, 7].length) (baseStart_7244957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7244957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7244957 prefixEnd_7244957 := by exact prefixLift 7244957
  have htrace : WordTrace (prefixWord ++ tailWord_7244957) baseStart_7244957 baseEnd_7244957 := by
    simpa [prefixWord, tailWord_7244957, baseEnd_7244957] using wordTrace_append hprefix tailTrace_7244957
  have hstable : (prefixWord ++ tailWord_7244957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7244957).length < 2 ^ (prefixWord ++ tailWord_7244957).sum := by decide
  have hdescent : baseEnd_7244957 < baseStart_7244957 := by decide
  rcases family_descends (prefixWord ++ tailWord_7244957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7244964 : List Nat := [2, 3, 1, 2, 3, 2, 1, 1, 2, 2, 4]
def baseStart_7244964 : Nat := 118140960795 + 7244964 * 2 ^ 59
def prefixEnd_7244964 : Nat := 4983230072969 + 3 ^ 40 * 7244964 * 2
def baseEnd_7244964 : Nat := 3720148856520697278731023

theorem tailTrace_7244964 : CollatzResearch.WordTrace tailWord_7244964 prefixEnd_7244964 3720148856520697278731023 := by
  unfold tailWord_7244964
  simp only [CollatzResearch.WordTrace]
  refine ⟨132122772862370122093266973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176163697149826829457689297 132122772862370122093266973)
  ·
    refine ⟨49546039823388795784975115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132122772862370122093266973 49546039823388795784975115)
    ·
      refine ⟨74319059735083193677462673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49546039823388795784975115 74319059735083193677462673)
      ·
        refine ⟨55739294801312395258097005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74319059735083193677462673 55739294801312395258097005)
        ·
          refine ⟨20902235550492148221786377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55739294801312395258097005 20902235550492148221786377)
          ·
            refine ⟨15676676662869111166339783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20902235550492148221786377 15676676662869111166339783)
            ·
              refine ⟨23515014994303666749509675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15676676662869111166339783 23515014994303666749509675)
              ·
                refine ⟨35272522491455500124264513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23515014994303666749509675 35272522491455500124264513)
                ·
                  refine ⟨26454391868591625093198385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35272522491455500124264513 26454391868591625093198385)
                  ·
                    refine ⟨19840793901443718819898789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26454391868591625093198385 19840793901443718819898789)
                    ·
                      refine ⟨3720148856520697278731023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19840793901443718819898789 3720148856520697278731023)
                      ·
                        rfl

theorem cell23_7244964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 1, 1, 2, 2, 4].length) (baseStart_7244964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7244964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7244964 prefixEnd_7244964 := by exact prefixLift 7244964
  have htrace : WordTrace (prefixWord ++ tailWord_7244964) baseStart_7244964 baseEnd_7244964 := by
    simpa [prefixWord, tailWord_7244964, baseEnd_7244964] using wordTrace_append hprefix tailTrace_7244964
  have hstable : (prefixWord ++ tailWord_7244964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7244964).length < 2 ^ (prefixWord ++ tailWord_7244964).sum := by decide
  have hdescent : baseEnd_7244964 < baseStart_7244964 := by decide
  rcases family_descends (prefixWord ++ tailWord_7244964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7244987 : List Nat := [1, 1, 1, 1, 1, 2, 4, 5, 2, 5]
def baseStart_7244987 : Nat := 118140960795 + 7244987 * 2 ^ 59
def prefixEnd_7244987 : Nat := 4983230072969 + 3 ^ 40 * 7244987 * 2
def baseEnd_7244987 : Nat := 1240053555525250229581139

theorem tailTrace_7244987 : CollatzResearch.WordTrace tailWord_7244987 prefixEnd_7244987 1240053555525250229581139 := by
  unfold tailWord_7244987
  simp only [CollatzResearch.WordTrace]
  refine ⟨264246384603656919114621215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176164256402437946076414143 264246384603656919114621215)
  ·
    refine ⟨396369576905485378671931823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264246384603656919114621215 396369576905485378671931823)
    ·
      refine ⟨594554365358228068007897735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 396369576905485378671931823 594554365358228068007897735)
      ·
        refine ⟨891831548037342102011846603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 594554365358228068007897735 891831548037342102011846603)
        ·
          refine ⟨1337747322056013153017769905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 891831548037342102011846603 1337747322056013153017769905)
          ·
            refine ⟨1003310491542009864763327429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1337747322056013153017769905 1003310491542009864763327429)
            ·
              refine ⟨188120717164126849643123893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1003310491542009864763327429 188120717164126849643123893)
              ·
                refine ⟨17636317234136892154042865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 188120717164126849643123893 17636317234136892154042865)
                ·
                  refine ⟨13227237925602669115532149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17636317234136892154042865 13227237925602669115532149)
                  ·
                    refine ⟨1240053555525250229581139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13227237925602669115532149 1240053555525250229581139)
                    ·
                      rfl

theorem cell23_7244987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 5, 2, 5].length) (baseStart_7244987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7244987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7244987 prefixEnd_7244987 := by exact prefixLift 7244987
  have htrace : WordTrace (prefixWord ++ tailWord_7244987) baseStart_7244987 baseEnd_7244987 := by
    simpa [prefixWord, tailWord_7244987, baseEnd_7244987] using wordTrace_append hprefix tailTrace_7244987
  have hstable : (prefixWord ++ tailWord_7244987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7244987).length < 2 ^ (prefixWord ++ tailWord_7244987).sum := by decide
  have hdescent : baseEnd_7244987 < baseStart_7244987 := by decide
  rcases family_descends (prefixWord ++ tailWord_7244987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7245058 : List Nat := [3, 4, 1, 1, 3, 1, 1, 2, 2, 1, 4]
def baseStart_7245058 : Nat := 118140960795 + 7245058 * 2 ^ 59
def prefixEnd_7245058 : Nat := 4983230072969 + 3 ^ 40 * 7245058 * 2
def baseEnd_7245058 : Nat := 3720197123702219910955591

theorem tailTrace_7245058 : CollatzResearch.WordTrace tailWord_7245058 prefixEnd_7245058 3720197123702219910955591 := by
  unfold tailWord_7245058
  simp only [CollatzResearch.WordTrace]
  refine ⟨66062243546599924560113957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176165982790933132160303885 66062243546599924560113957)
  ·
    refine ⟨12386670664987485855021367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 66062243546599924560113957 12386670664987485855021367)
    ·
      refine ⟨18580005997481228782532051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12386670664987485855021367 18580005997481228782532051)
      ·
        refine ⟨27870008996221843173798077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18580005997481228782532051 27870008996221843173798077)
        ·
          refine ⟨10451253373583191190174279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27870008996221843173798077 10451253373583191190174279)
          ·
            refine ⟨15676880060374786785261419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10451253373583191190174279 15676880060374786785261419)
            ·
              refine ⟨23515320090562180177892129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15676880060374786785261419 23515320090562180177892129)
              ·
                refine ⟨17636490067921635133419097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23515320090562180177892129 17636490067921635133419097)
                ·
                  refine ⟨13227367550941226350064323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17636490067921635133419097 13227367550941226350064323)
                  ·
                    refine ⟨19841051326411839525096485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13227367550941226350064323 19841051326411839525096485)
                    ·
                      refine ⟨3720197123702219910955591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19841051326411839525096485 3720197123702219910955591)
                      ·
                        rfl

theorem cell23_7245058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 1, 2, 2, 1, 4].length) (baseStart_7245058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7245058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7245058 prefixEnd_7245058 := by exact prefixLift 7245058
  have htrace : WordTrace (prefixWord ++ tailWord_7245058) baseStart_7245058 baseEnd_7245058 := by
    simpa [prefixWord, tailWord_7245058, baseEnd_7245058] using wordTrace_append hprefix tailTrace_7245058
  have hstable : (prefixWord ++ tailWord_7245058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7245058).length < 2 ^ (prefixWord ++ tailWord_7245058).sum := by decide
  have hdescent : baseEnd_7245058 < baseStart_7245058 := by decide
  rcases family_descends (prefixWord ++ tailWord_7245058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7245077 : List Nat := [1, 3, 2, 1, 2, 1, 1, 1, 2, 9]
def baseStart_7245077 : Nat := 118140960795 + 7245077 * 2 ^ 59
def prefixEnd_7245077 : Nat := 4983230072969 + 3 ^ 40 * 7245077 * 2
def baseEnd_7245077 : Nat := 1240068959944885112206001

theorem tailTrace_7245077 : CollatzResearch.WordTrace tailWord_7245077 prefixEnd_7245077 1240068959944885112206001 := by
  unfold tailWord_7245077
  simp only [CollatzResearch.WordTrace]
  refine ⟨264249667173330864485397485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176166444782220576323598323 264249667173330864485397485)
  ·
    refine ⟨99093625189999074182024057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 264249667173330864485397485 99093625189999074182024057)
    ·
      refine ⟨74320218892499305636518043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99093625189999074182024057 74320218892499305636518043)
      ·
        refine ⟨111480328338748958454777065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74320218892499305636518043 111480328338748958454777065)
        ·
          refine ⟨83610246254061718841082799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111480328338748958454777065 83610246254061718841082799)
          ·
            refine ⟨125415369381092578261624199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83610246254061718841082799 125415369381092578261624199)
            ·
              refine ⟨188123054071638867392436299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125415369381092578261624199 188123054071638867392436299)
              ·
                refine ⟨282184581107458301088654449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 188123054071638867392436299 282184581107458301088654449)
                ·
                  refine ⟨211638435830593725816490837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 282184581107458301088654449 211638435830593725816490837)
                  ·
                    refine ⟨1240068959944885112206001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 211638435830593725816490837 1240068959944885112206001)
                    ·
                      rfl

theorem cell23_7245077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 1, 2, 9].length) (baseStart_7245077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7245077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7245077 prefixEnd_7245077 := by exact prefixLift 7245077
  have htrace : WordTrace (prefixWord ++ tailWord_7245077) baseStart_7245077 baseEnd_7245077 := by
    simpa [prefixWord, tailWord_7245077, baseEnd_7245077] using wordTrace_append hprefix tailTrace_7245077
  have hstable : (prefixWord ++ tailWord_7245077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7245077).length < 2 ^ (prefixWord ++ tailWord_7245077).sum := by decide
  have hdescent : baseEnd_7245077 < baseStart_7245077 := by decide
  rcases family_descends (prefixWord ++ tailWord_7245077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7245118 : List Nat := [4, 2, 1, 2, 1, 1, 1, 4, 2, 3, 2]
def baseStart_7245118 : Nat := 118140960795 + 7245118 * 2 ^ 59
def prefixEnd_7245118 : Nat := 4983230072969 + 3 ^ 40 * 7245118 * 2
def baseEnd_7245118 : Nat := 3720227932541489676205315

theorem tailTrace_7245118 : CollatzResearch.WordTrace tailWord_7245118 prefixEnd_7245118 3720227932541489676205315 := by
  unfold tailWord_7245118
  simp only [CollatzResearch.WordTrace]
  refine ⟨33031395320772791060955001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 176167441710788218991760005 33031395320772791060955001)
  ·
    refine ⟨24773546490579593295716251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33031395320772791060955001 24773546490579593295716251)
    ·
      refine ⟨37160319735869389943574377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24773546490579593295716251 37160319735869389943574377)
      ·
        refine ⟨27870239801902042457680783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37160319735869389943574377 27870239801902042457680783)
        ·
          refine ⟨41805359702853063686521175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27870239801902042457680783 41805359702853063686521175)
          ·
            refine ⟨62708039554279595529781763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41805359702853063686521175 62708039554279595529781763)
            ·
              refine ⟨94062059331419393294672645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62708039554279595529781763 94062059331419393294672645)
              ·
                refine ⟨17636636124641136242751121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 94062059331419393294672645 17636636124641136242751121)
                ·
                  refine ⟨13227477093480852182063341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17636636124641136242751121 13227477093480852182063341)
                  ·
                    refine ⟨4960303910055319568273753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13227477093480852182063341 4960303910055319568273753)
                    ·
                      refine ⟨3720227932541489676205315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4960303910055319568273753 3720227932541489676205315)
                      ·
                        rfl

theorem cell23_7245118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 4, 2, 3, 2].length) (baseStart_7245118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7245118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7245118 prefixEnd_7245118 := by exact prefixLift 7245118
  have htrace : WordTrace (prefixWord ++ tailWord_7245118) baseStart_7245118 baseEnd_7245118 := by
    simpa [prefixWord, tailWord_7245118, baseEnd_7245118] using wordTrace_append hprefix tailTrace_7245118
  have hstable : (prefixWord ++ tailWord_7245118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7245118).length < 2 ^ (prefixWord ++ tailWord_7245118).sum := by decide
  have hdescent : baseEnd_7245118 < baseStart_7245118 := by decide
  rcases family_descends (prefixWord ++ tailWord_7245118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7245134 : List Nat := [4, 1, 1, 1, 1, 1, 4, 1, 3, 1, 5]
def baseStart_7245134 : Nat := 118140960795 + 7245134 * 2 ^ 59
def prefixEnd_7245134 : Nat := 4983230072969 + 3 ^ 40 * 7245134 * 2
def baseEnd_7245134 : Nat := 3720236148231961613605241

theorem tailTrace_7245134 : CollatzResearch.WordTrace tailWord_7245134 prefixEnd_7245134 3720236148231961613605241 := by
  unfold tailWord_7245134
  simp only [CollatzResearch.WordTrace]
  refine ⟨33031468266765545402527807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 176167830756082908813481637 33031468266765545402527807)
  ·
    refine ⟨49547202400148318103791711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33031468266765545402527807 49547202400148318103791711)
    ·
      refine ⟨74320803600222477155687567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49547202400148318103791711 74320803600222477155687567)
      ·
        refine ⟨111481205400333715733531351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74320803600222477155687567 111481205400333715733531351)
        ·
          refine ⟨167221808100500573600297027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111481205400333715733531351 167221808100500573600297027)
          ·
            refine ⟨250832712150750860400445541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 167221808100500573600297027 250832712150750860400445541)
            ·
              refine ⟨47031133528265786325083539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 250832712150750860400445541 47031133528265786325083539)
              ·
                refine ⟨70546700292398679487625309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47031133528265786325083539 70546700292398679487625309)
                ·
                  refine ⟨26455012609649504807859491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 70546700292398679487625309 26455012609649504807859491)
                  ·
                    refine ⟨39682518914474257211789237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26455012609649504807859491 39682518914474257211789237)
                    ·
                      refine ⟨3720236148231961613605241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39682518914474257211789237 3720236148231961613605241)
                      ·
                        rfl

theorem cell23_7245134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 4, 1, 3, 1, 5].length) (baseStart_7245134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7245134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7245134 prefixEnd_7245134 := by exact prefixLift 7245134
  have htrace : WordTrace (prefixWord ++ tailWord_7245134) baseStart_7245134 baseEnd_7245134 := by
    simpa [prefixWord, tailWord_7245134, baseEnd_7245134] using wordTrace_append hprefix tailTrace_7245134
  have hstable : (prefixWord ++ tailWord_7245134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7245134).length < 2 ^ (prefixWord ++ tailWord_7245134).sum := by decide
  have hdescent : baseEnd_7245134 < baseStart_7245134 := by decide
  rcases family_descends (prefixWord ++ tailWord_7245134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7245141 : List Nat := [1, 3, 2, 2, 3, 2, 2, 1, 1, 6]
def baseStart_7245141 : Nat := 118140960795 + 7245141 * 2 ^ 59
def prefixEnd_7245141 : Nat := 4983230072969 + 3 ^ 40 * 7245141 * 2
def baseEnd_7245141 : Nat := 1240079914198847695405903

theorem tailTrace_7245141 : CollatzResearch.WordTrace tailWord_7245141 prefixEnd_7245141 1240079914198847695405903 := by
  unfold tailWord_7245141
  simp only [CollatzResearch.WordTrace]
  refine ⟨264252001445099003415727277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176168000963399335610484851 264252001445099003415727277)
  ·
    refine ⟨99094500541912126280897729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 264252001445099003415727277 99094500541912126280897729)
    ·
      refine ⟨74320875406434094710673297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99094500541912126280897729 74320875406434094710673297)
      ·
        refine ⟨55740656554825571033004973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74320875406434094710673297 55740656554825571033004973)
        ·
          refine ⟨20902746208059589137376865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55740656554825571033004973 20902746208059589137376865)
          ·
            refine ⟨15677059656044691853032649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20902746208059589137376865 15677059656044691853032649)
            ·
              refine ⟨11757794742033518889774487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15677059656044691853032649 11757794742033518889774487)
              ·
                refine ⟨17636692113050278334661731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11757794742033518889774487 17636692113050278334661731)
                ·
                  refine ⟨26455038169575417501992597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17636692113050278334661731 26455038169575417501992597)
                  ·
                    refine ⟨1240079914198847695405903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26455038169575417501992597 1240079914198847695405903)
                    ·
                      rfl

theorem cell23_7245141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 2, 1, 1, 6].length) (baseStart_7245141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7245141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7245141 prefixEnd_7245141 := by exact prefixLift 7245141
  have htrace : WordTrace (prefixWord ++ tailWord_7245141) baseStart_7245141 baseEnd_7245141 := by
    simpa [prefixWord, tailWord_7245141, baseEnd_7245141] using wordTrace_append hprefix tailTrace_7245141
  have hstable : (prefixWord ++ tailWord_7245141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7245141).length < 2 ^ (prefixWord ++ tailWord_7245141).sum := by decide
  have hdescent : baseEnd_7245141 < baseStart_7245141 := by decide
  rcases family_descends (prefixWord ++ tailWord_7245141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7245151 : List Nat := [1, 1, 2, 3, 1, 2, 1, 6, 1, 2, 3]
def baseStart_7245151 : Nat := 118140960795 + 7245151 * 2 ^ 59
def prefixEnd_7245151 : Nat := 4983230072969 + 3 ^ 40 * 7245151 * 2
def baseEnd_7245151 : Nat := 3720244877403088047092663

theorem tailTrace_7245151 : CollatzResearch.WordTrace tailWord_7245151 prefixEnd_7245151 3720244877403088047092663 := by
  unfold tailWord_7245151
  simp only [CollatzResearch.WordTrace]
  refine ⟨264252366175062775123591307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176168244116708516749060871 264252366175062775123591307)
  ·
    refine ⟨396378549262594162685386961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264252366175062775123591307 396378549262594162685386961)
    ·
      refine ⟨297283911946945622014040221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 396378549262594162685386961 297283911946945622014040221)
      ·
        refine ⟨111481466980104608255265083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 297283911946945622014040221 111481466980104608255265083)
        ·
          refine ⟨167222200470156912382897625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111481466980104608255265083 167222200470156912382897625)
          ·
            refine ⟨125416650352617684287173219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 167222200470156912382897625 125416650352617684287173219)
            ·
              refine ⟨188124975528926526430759829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125416650352617684287173219 188124975528926526430759829)
              ·
                refine ⟨8818358227918430926441867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 188124975528926526430759829 8818358227918430926441867)
                ·
                  refine ⟨13227537341877646389662801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8818358227918430926441867 13227537341877646389662801)
                  ·
                    refine ⟨9920653006408234792247101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13227537341877646389662801 9920653006408234792247101)
                    ·
                      refine ⟨3720244877403088047092663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9920653006408234792247101 3720244877403088047092663)
                      ·
                        rfl

theorem cell23_7245151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 6, 1, 2, 3].length) (baseStart_7245151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7245151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7245151 prefixEnd_7245151 := by exact prefixLift 7245151
  have htrace : WordTrace (prefixWord ++ tailWord_7245151) baseStart_7245151 baseEnd_7245151 := by
    simpa [prefixWord, tailWord_7245151, baseEnd_7245151] using wordTrace_append hprefix tailTrace_7245151
  have hstable : (prefixWord ++ tailWord_7245151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7245151).length < 2 ^ (prefixWord ++ tailWord_7245151).sum := by decide
  have hdescent : baseEnd_7245151 < baseStart_7245151 := by decide
  rcases family_descends (prefixWord ++ tailWord_7245151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7245162 : List Nat := [3, 1, 3, 3, 3, 1, 2, 1, 1, 5]
def baseStart_7245162 : Nat := 118140960795 + 7245162 * 2 ^ 59
def prefixEnd_7245162 : Nat := 4983230072969 + 3 ^ 40 * 7245162 * 2
def baseEnd_7245162 : Nat := 1240083508563429168018371

theorem tailTrace_7245162 : CollatzResearch.WordTrace tailWord_7245162 prefixEnd_7245162 1240083508563429168018371 := by
  unfold tailWord_7245162
  simp only [CollatzResearch.WordTrace]
  refine ⟨66063191844505731000560435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176168511585348616001494493 66063191844505731000560435)
  ·
    refine ⟨99094787766758596500840653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66063191844505731000560435 99094787766758596500840653)
    ·
      refine ⟨37160545412534473687815245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99094787766758596500840653 37160545412534473687815245)
      ·
        refine ⟨13935204529700427632930717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37160545412534473687815245 13935204529700427632930717)
        ·
          refine ⟨5225701698637660362349019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13935204529700427632930717 5225701698637660362349019)
          ·
            refine ⟨7838552547956490543523529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5225701698637660362349019 7838552547956490543523529)
            ·
              refine ⟨5878914410967367907642647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7838552547956490543523529 5878914410967367907642647)
              ·
                refine ⟨8818371616451051861463971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5878914410967367907642647 8818371616451051861463971)
                ·
                  refine ⟨13227557424676577792195957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8818371616451051861463971 13227557424676577792195957)
                  ·
                    refine ⟨1240083508563429168018371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13227557424676577792195957 1240083508563429168018371)
                    ·
                      rfl

theorem cell23_7245162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 3, 1, 2, 1, 1, 5].length) (baseStart_7245162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7245162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7245162 prefixEnd_7245162 := by exact prefixLift 7245162
  have htrace : WordTrace (prefixWord ++ tailWord_7245162) baseStart_7245162 baseEnd_7245162 := by
    simpa [prefixWord, tailWord_7245162, baseEnd_7245162] using wordTrace_append hprefix tailTrace_7245162
  have hstable : (prefixWord ++ tailWord_7245162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7245162).length < 2 ^ (prefixWord ++ tailWord_7245162).sum := by decide
  have hdescent : baseEnd_7245162 < baseStart_7245162 := by decide
  rcases family_descends (prefixWord ++ tailWord_7245162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7245165 : List Nat := [1, 5, 1, 1, 1, 5, 2, 1, 1, 1, 4]
def baseStart_7245165 : Nat := 118140960795 + 7245165 * 2 ^ 59
def prefixEnd_7245165 : Nat := 4983230072969 + 3 ^ 40 * 7245165 * 2
def baseEnd_7245165 : Nat := 3720252066132250992317599

theorem tailTrace_7245165 : CollatzResearch.WordTrace tailWord_7245165 prefixEnd_7245165 3720252066132250992317599 := by
  unfold tailWord_7245165
  simp only [CollatzResearch.WordTrace]
  refine ⟨264252876797012055514600949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176168584531341370343067299 264252876797012055514600949)
  ·
    refine ⟨24773707199719880204493839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 264252876797012055514600949 24773707199719880204493839)
    ·
      refine ⟨37160560799579820306740759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24773707199719880204493839 37160560799579820306740759)
      ·
        refine ⟨55740841199369730460111139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37160560799579820306740759 55740841199369730460111139)
        ·
          refine ⟨83611261799054595690166709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55740841199369730460111139 83611261799054595690166709)
          ·
            refine ⟨7838555793661368345953129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 83611261799054595690166709 7838555793661368345953129)
            ·
              refine ⟨5878916845246026259464847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7838555793661368345953129 5878916845246026259464847)
              ·
                refine ⟨8818375267869039389197271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5878916845246026259464847 8818375267869039389197271)
                ·
                  refine ⟨13227562901803559083795907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8818375267869039389197271 13227562901803559083795907)
                  ·
                    refine ⟨19841344352705338625693861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13227562901803559083795907 19841344352705338625693861)
                    ·
                      refine ⟨3720252066132250992317599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19841344352705338625693861 3720252066132250992317599)
                      ·
                        rfl

theorem cell23_7245165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 5, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 5, 2, 1, 1, 1, 4].length) (baseStart_7245165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7245165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7245165 prefixEnd_7245165 := by exact prefixLift 7245165
  have htrace : WordTrace (prefixWord ++ tailWord_7245165) baseStart_7245165 baseEnd_7245165 := by
    simpa [prefixWord, tailWord_7245165, baseEnd_7245165] using wordTrace_append hprefix tailTrace_7245165
  have hstable : (prefixWord ++ tailWord_7245165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7245165).length < 2 ^ (prefixWord ++ tailWord_7245165).sum := by decide
  have hdescent : baseEnd_7245165 < baseStart_7245165 := by decide
  rcases family_descends (prefixWord ++ tailWord_7245165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7245202 : List Nat := [3, 2, 3, 3, 1, 1, 2, 2, 1, 2, 3]
def baseStart_7245202 : Nat := 118140960795 + 7245202 * 2 ^ 59
def prefixEnd_7245202 : Nat := 4983230072969 + 3 ^ 40 * 7245202 * 2
def baseEnd_7245202 : Nat := 3720271064916467347554929

theorem tailTrace_7245202 : CollatzResearch.WordTrace tailWord_7245202 prefixEnd_7245202 3720271064916467347554929 := by
  unfold tailWord_7245202
  simp only [CollatzResearch.WordTrace]
  refine ⟨66063556574469502708424465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176169484198585340555798573 66063556574469502708424465)
  ·
    refine ⟨49547667430852127031318349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66063556574469502708424465 49547667430852127031318349)
    ·
      refine ⟨18580375286569547636744381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49547667430852127031318349 18580375286569547636744381)
      ·
        refine ⟨6967640732463580363779143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18580375286569547636744381 6967640732463580363779143)
        ·
          refine ⟨10451461098695370545668715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6967640732463580363779143 10451461098695370545668715)
          ·
            refine ⟨15677191648043055818503073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10451461098695370545668715 15677191648043055818503073)
            ·
              refine ⟨11757893736032291863877305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15677191648043055818503073 11757893736032291863877305)
              ·
                refine ⟨8818420302024218897907979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11757893736032291863877305 8818420302024218897907979)
                ·
                  refine ⟨13227630453036328346861969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8818420302024218897907979 13227630453036328346861969)
                  ·
                    refine ⟨9920722839777246260146477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13227630453036328346861969 9920722839777246260146477)
                    ·
                      refine ⟨3720271064916467347554929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9920722839777246260146477 3720271064916467347554929)
                      ·
                        rfl

theorem cell23_7245202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 2, 2, 1, 2, 3].length) (baseStart_7245202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7245202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7245202 prefixEnd_7245202 := by exact prefixLift 7245202
  have htrace : WordTrace (prefixWord ++ tailWord_7245202) baseStart_7245202 baseEnd_7245202 := by
    simpa [prefixWord, tailWord_7245202, baseEnd_7245202] using wordTrace_append hprefix tailTrace_7245202
  have hstable : (prefixWord ++ tailWord_7245202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7245202).length < 2 ^ (prefixWord ++ tailWord_7245202).sum := by decide
  have hdescent : baseEnd_7245202 < baseStart_7245202 := by decide
  rcases family_descends (prefixWord ++ tailWord_7245202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7245234 : List Nat := [3, 2, 1, 1, 1, 1, 2, 1, 2, 3, 6]
def baseStart_7245234 : Nat := 118140960795 + 7245234 * 2 ^ 59
def prefixEnd_7245234 : Nat := 4983230072969 + 3 ^ 40 * 7245234 * 2
def baseEnd_7245234 : Nat := 3720287496297411222354781

theorem tailTrace_7245234 : CollatzResearch.WordTrace tailWord_7245234 prefixEnd_7245234 3720287496297411222354781 := by
  unfold tailWord_7245234
  simp only [CollatzResearch.WordTrace]
  refine ⟨66063848358440520074715689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176170262289174720199241837 66063848358440520074715689)
  ·
    refine ⟨49547886268830390056036767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66063848358440520074715689 49547886268830390056036767)
    ·
      refine ⟨74321829403245585084055151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49547886268830390056036767 74321829403245585084055151)
      ·
        refine ⟨111482744104868377626082727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74321829403245585084055151 111482744104868377626082727)
        ·
          refine ⟨167224116157302566439124091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111482744104868377626082727 167224116157302566439124091)
          ·
            refine ⟨250836174235953849658686137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 167224116157302566439124091 250836174235953849658686137)
            ·
              refine ⟨188127130676965387244014603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 250836174235953849658686137 188127130676965387244014603)
              ·
                refine ⟨282190696015448080866021905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 188127130676965387244014603 282190696015448080866021905)
                ·
                  refine ⟨211643022011586060649516429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 282190696015448080866021905 211643022011586060649516429)
                  ·
                    refine ⟨79366133254344772743568661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 211643022011586060649516429 79366133254344772743568661)
                    ·
                      refine ⟨3720287496297411222354781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 79366133254344772743568661 3720287496297411222354781)
                      ·
                        rfl

theorem cell23_7245234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 1, 2, 3, 6].length) (baseStart_7245234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7245234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7245234 prefixEnd_7245234 := by exact prefixLift 7245234
  have htrace : WordTrace (prefixWord ++ tailWord_7245234) baseStart_7245234 baseEnd_7245234 := by
    simpa [prefixWord, tailWord_7245234, baseEnd_7245234] using wordTrace_append hprefix tailTrace_7245234
  have hstable : (prefixWord ++ tailWord_7245234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7245234).length < 2 ^ (prefixWord ++ tailWord_7245234).sum := by decide
  have hdescent : baseEnd_7245234 < baseStart_7245234 := by decide
  rcases family_descends (prefixWord ++ tailWord_7245234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7245255 : List Nat := [1, 1, 4, 1, 1, 3, 3, 3, 2, 2, 2]
def baseStart_7245255 : Nat := 118140960795 + 7245255 * 2 ^ 59
def prefixEnd_7245255 : Nat := 4983230072969 + 3 ^ 40 * 7245255 * 2
def baseEnd_7245255 : Nat := 3720298279391155640192185

theorem tailTrace_7245255 : CollatzResearch.WordTrace tailWord_7245255 prefixEnd_7245255 3720298279391155640192185 := by
  unfold tailWord_7245255
  simp only [CollatzResearch.WordTrace]
  refine ⟨264256159366686000885377219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176170772911124000590251479 264256159366686000885377219)
  ·
    refine ⟨396384239050029001328065829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264256159366686000885377219 396384239050029001328065829)
    ·
      refine ⟨74322044821880437749012343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 396384239050029001328065829 74322044821880437749012343)
      ·
        refine ⟨111483067232820656623518515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74322044821880437749012343 111483067232820656623518515)
        ·
          refine ⟨167224600849230984935277773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111483067232820656623518515 167224600849230984935277773)
          ·
            refine ⟨62709225318461619350729165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 167224600849230984935277773 62709225318461619350729165)
            ·
              refine ⟨23515959494423107256523437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62709225318461619350729165 23515959494423107256523437)
              ·
                refine ⟨8818484810408665221196289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23515959494423107256523437 8818484810408665221196289)
                ·
                  refine ⟨6613863607806498915897217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8818484810408665221196289 6613863607806498915897217)
                  ·
                    refine ⟨4960397705854874186922913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6613863607806498915897217 4960397705854874186922913)
                    ·
                      refine ⟨3720298279391155640192185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4960397705854874186922913 3720298279391155640192185)
                      ·
                        rfl

theorem cell23_7245255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 3, 3, 2, 2, 2].length) (baseStart_7245255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7245255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7245255 prefixEnd_7245255 := by exact prefixLift 7245255
  have htrace : WordTrace (prefixWord ++ tailWord_7245255) baseStart_7245255 baseEnd_7245255 := by
    simpa [prefixWord, tailWord_7245255, baseEnd_7245255] using wordTrace_append hprefix tailTrace_7245255
  have hstable : (prefixWord ++ tailWord_7245255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7245255).length < 2 ^ (prefixWord ++ tailWord_7245255).sum := by decide
  have hdescent : baseEnd_7245255 < baseStart_7245255 := by decide
  rcases family_descends (prefixWord ++ tailWord_7245255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7245341 : List Nat := [1, 4, 2, 2, 1, 1, 1, 1, 1, 3, 6]
def baseStart_7245341 : Nat := 118140960795 + 7245341 * 2 ^ 59
def prefixEnd_7245341 : Nat := 4983230072969 + 3 ^ 40 * 7245341 * 2
def baseEnd_7245341 : Nat := 3720342438727442303716789

theorem tailTrace_7245341 : CollatzResearch.WordTrace tailWord_7245341 prefixEnd_7245341 3720342438727442303716789 := by
  unfold tailWord_7245341
  simp only [CollatzResearch.WordTrace]
  refine ⟨264259296044374437573007877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176172864029582958382005251 264259296044374437573007877)
  ·
    refine ⟨49548618008320207044938977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 264259296044374437573007877 49548618008320207044938977)
    ·
      refine ⟨37161463506240155283704233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49548618008320207044938977 37161463506240155283704233)
      ·
        refine ⟨27871097629680116462778175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37161463506240155283704233 27871097629680116462778175)
        ·
          refine ⟨41806646444520174694167263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27871097629680116462778175 41806646444520174694167263)
          ·
            refine ⟨62709969666780262041250895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41806646444520174694167263 62709969666780262041250895)
            ·
              refine ⟨94064954500170393061876343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62709969666780262041250895 94064954500170393061876343)
              ·
                refine ⟨141097431750255589592814515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94064954500170393061876343 141097431750255589592814515)
                ·
                  refine ⟨211646147625383384389221773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 141097431750255589592814515 211646147625383384389221773)
                  ·
                    refine ⟨79367305359518769145958165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 211646147625383384389221773 79367305359518769145958165)
                    ·
                      refine ⟨3720342438727442303716789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 79367305359518769145958165 3720342438727442303716789)
                      ·
                        rfl

theorem cell23_7245341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 1, 1, 3, 6].length) (baseStart_7245341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7245341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7245341 prefixEnd_7245341 := by exact prefixLift 7245341
  have htrace : WordTrace (prefixWord ++ tailWord_7245341) baseStart_7245341 baseEnd_7245341 := by
    simpa [prefixWord, tailWord_7245341, baseEnd_7245341] using wordTrace_append hprefix tailTrace_7245341
  have hstable : (prefixWord ++ tailWord_7245341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7245341).length < 2 ^ (prefixWord ++ tailWord_7245341).sum := by decide
  have hdescent : baseEnd_7245341 < baseStart_7245341 := by decide
  rcases family_descends (prefixWord ++ tailWord_7245341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7245412 : List Nat := [2, 3, 1, 1, 2, 5, 1, 1, 3, 1, 3]
def baseStart_7245412 : Nat := 118140960795 + 7245412 * 2 ^ 59
def prefixEnd_7245412 : Nat := 4983230072969 + 3 ^ 40 * 7245412 * 2
def baseEnd_7245412 : Nat := 3720378895853911525928963

theorem tailTrace_7245412 : CollatzResearch.WordTrace tailWord_7245412 prefixEnd_7245412 3720378895853911525928963 := by
  unfold tailWord_7245412
  simp only [CollatzResearch.WordTrace]
  refine ⟨132130942813558608349421245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176174590418078144465894993 132130942813558608349421245)
  ·
    refine ⟨49549103555084478131032967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132130942813558608349421245 49549103555084478131032967)
    ·
      refine ⟨74323655332626717196549451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49549103555084478131032967 74323655332626717196549451)
      ·
        refine ⟨111485482998940075794824177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74323655332626717196549451 111485482998940075794824177)
        ·
          refine ⟨83614112249205056846118133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111485482998940075794824177 83614112249205056846118133)
          ·
            refine ⟨7838823023362974079323575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 83614112249205056846118133 7838823023362974079323575)
            ·
              refine ⟨11758234535044461118985363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7838823023362974079323575 11758234535044461118985363)
              ·
                refine ⟨17637351802566691678478045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11758234535044461118985363 17637351802566691678478045)
                ·
                  refine ⟨6614006925962509379429267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17637351802566691678478045 6614006925962509379429267)
                  ·
                    refine ⟨9921010388943764069143901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6614006925962509379429267 9921010388943764069143901)
                    ·
                      refine ⟨3720378895853911525928963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9921010388943764069143901 3720378895853911525928963)
                      ·
                        rfl

theorem cell23_7245412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 5, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 5, 1, 1, 3, 1, 3].length) (baseStart_7245412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7245412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7245412 prefixEnd_7245412 := by exact prefixLift 7245412
  have htrace : WordTrace (prefixWord ++ tailWord_7245412) baseStart_7245412 baseEnd_7245412 := by
    simpa [prefixWord, tailWord_7245412, baseEnd_7245412] using wordTrace_append hprefix tailTrace_7245412
  have hstable : (prefixWord ++ tailWord_7245412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7245412).length < 2 ^ (prefixWord ++ tailWord_7245412).sum := by decide
  have hdescent : baseEnd_7245412 < baseStart_7245412 := by decide
  rcases family_descends (prefixWord ++ tailWord_7245412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7245435 : List Nat := [1, 1, 1, 1, 1, 4, 4, 1, 5, 2, 2]
def baseStart_7245435 : Nat := 118140960795 + 7245435 * 2 ^ 59
def prefixEnd_7245435 : Nat := 4983230072969 + 3 ^ 40 * 7245435 * 2
def baseEnd_7245435 : Nat := 3720390705908964935941357

theorem tailTrace_7245435 : CollatzResearch.WordTrace tailWord_7245435 prefixEnd_7245435 3720390705908964935941357 := by
  unfold tailWord_7245435
  simp only [CollatzResearch.WordTrace]
  refine ⟨264262724506033891626929759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176175149670689261084619839 264262724506033891626929759)
  ·
    refine ⟨396394086759050837440394639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264262724506033891626929759 396394086759050837440394639)
    ·
      refine ⟨594591130138576256160591959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 396394086759050837440394639 594591130138576256160591959)
      ·
        refine ⟨891886695207864384240887939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 594591130138576256160591959 891886695207864384240887939)
        ·
          refine ⟨1337830042811796576361331909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 891886695207864384240887939 1337830042811796576361331909)
          ·
            refine ⟨250843133027211858067749733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1337830042811796576361331909 250843133027211858067749733)
            ·
              refine ⟨47033087442602223387703075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 250843133027211858067749733 47033087442602223387703075)
              ·
                refine ⟨70549631163903335081554613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47033087442602223387703075 70549631163903335081554613)
                ·
                  refine ⟨6614027921615937663895745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 70549631163903335081554613 6614027921615937663895745)
                  ·
                    refine ⟨4960520941211953247921809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6614027921615937663895745 4960520941211953247921809)
                    ·
                      refine ⟨3720390705908964935941357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4960520941211953247921809 3720390705908964935941357)
                      ·
                        rfl

theorem cell23_7245435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 4, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 4, 1, 5, 2, 2].length) (baseStart_7245435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7245435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7245435 prefixEnd_7245435 := by exact prefixLift 7245435
  have htrace : WordTrace (prefixWord ++ tailWord_7245435) baseStart_7245435 baseEnd_7245435 := by
    simpa [prefixWord, tailWord_7245435, baseEnd_7245435] using wordTrace_append hprefix tailTrace_7245435
  have hstable : (prefixWord ++ tailWord_7245435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7245435).length < 2 ^ (prefixWord ++ tailWord_7245435).sum := by decide
  have hdescent : baseEnd_7245435 < baseStart_7245435 := by decide
  rcases family_descends (prefixWord ++ tailWord_7245435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7245458 : List Nat := [3, 2, 3, 1, 3, 11]
def baseStart_7245458 : Nat := 118140960795 + 7245458 * 2 ^ 59
def prefixEnd_7245458 : Nat := 4983230072969 + 3 ^ 40 * 7245458 * 2
def baseEnd_7245458 : Nat := 15310298419605013769357

theorem tailTrace_7245458 : CollatzResearch.WordTrace tailWord_7245458 prefixEnd_7245458 15310298419605013769357 := by
  unfold tailWord_7245458
  simp only [CollatzResearch.WordTrace]
  refine ⟨66065890846237641638754257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176175708923300377703344685 66065890846237641638754257)
  ·
    refine ⟨49549418134678231229065693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66065890846237641638754257 49549418134678231229065693)
    ·
      refine ⟨18581031800504336710899635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49549418134678231229065693 18581031800504336710899635)
      ·
        refine ⟨27871547700756505066349453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18581031800504336710899635 27871547700756505066349453)
        ·
          refine ⟨10451830387783689399881045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27871547700756505066349453 10451830387783689399881045)
          ·
            refine ⟨15310298419605013769357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 10451830387783689399881045 15310298419605013769357)
            ·
              rfl

theorem cell23_7245458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 11].length) (baseStart_7245458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7245458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7245458 prefixEnd_7245458 := by exact prefixLift 7245458
  have htrace : WordTrace (prefixWord ++ tailWord_7245458) baseStart_7245458 baseEnd_7245458 := by
    simpa [prefixWord, tailWord_7245458, baseEnd_7245458] using wordTrace_append hprefix tailTrace_7245458
  have hstable : (prefixWord ++ tailWord_7245458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7245458).length < 2 ^ (prefixWord ++ tailWord_7245458).sum := by decide
  have hdescent : baseEnd_7245458 < baseStart_7245458 := by decide
  rcases family_descends (prefixWord ++ tailWord_7245458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7245486 : List Nat := [4, 1, 4, 1, 2, 1, 1, 2, 3, 2, 2]
def baseStart_7245486 : Nat := 118140960795 + 7245486 * 2 ^ 59
def prefixEnd_7245486 : Nat := 4983230072969 + 3 ^ 40 * 7245486 * 2
def baseEnd_7245486 : Nat := 3720416893422344236403623

theorem tailTrace_7245486 : CollatzResearch.WordTrace tailWord_7245486 prefixEnd_7245486 3720416893422344236403623 := by
  unfold tailWord_7245486
  simp only [CollatzResearch.WordTrace]
  refine ⟨33033073078606140917129539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 176176389752566084891357541 33033073078606140917129539)
  ·
    refine ⟨49549609617909211375694309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33033073078606140917129539 49549609617909211375694309)
    ·
      refine ⟨9290551803357977132942683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49549609617909211375694309 9290551803357977132942683)
      ·
        refine ⟨13935827705036965699414025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9290551803357977132942683 13935827705036965699414025)
        ·
          refine ⟨10451870778777724274560519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13935827705036965699414025 10451870778777724274560519)
          ·
            refine ⟨15677806168166586411840779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10451870778777724274560519 15677806168166586411840779)
            ·
              refine ⟨23516709252249879617761169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15677806168166586411840779 23516709252249879617761169)
              ·
                refine ⟨17637531939187409713320877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23516709252249879617761169 17637531939187409713320877)
                ·
                  refine ⟨6614074477195278642495329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17637531939187409713320877 6614074477195278642495329)
                  ·
                    refine ⟨4960555857896458981871497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6614074477195278642495329 4960555857896458981871497)
                    ·
                      refine ⟨3720416893422344236403623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4960555857896458981871497 3720416893422344236403623)
                      ·
                        rfl

theorem cell23_7245486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 1, 2, 3, 2, 2].length) (baseStart_7245486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7245486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7245486 prefixEnd_7245486 := by exact prefixLift 7245486
  have htrace : WordTrace (prefixWord ++ tailWord_7245486) baseStart_7245486 baseEnd_7245486 := by
    simpa [prefixWord, tailWord_7245486, baseEnd_7245486] using wordTrace_append hprefix tailTrace_7245486
  have hstable : (prefixWord ++ tailWord_7245486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7245486).length < 2 ^ (prefixWord ++ tailWord_7245486).sum := by decide
  have hdescent : baseEnd_7245486 < baseStart_7245486 := by decide
  rcases family_descends (prefixWord ++ tailWord_7245486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7245512 : List Nat := [2, 1, 3, 1, 2, 2, 3, 3, 1, 3, 2]
def baseStart_7245512 : Nat := 118140960795 + 7245512 * 2 ^ 59
def prefixEnd_7245512 : Nat := 4983230072969 + 3 ^ 40 * 7245512 * 2
def baseEnd_7245512 : Nat := 3720430243919361134678503

theorem tailTrace_7245512 : CollatzResearch.WordTrace tailWord_7245512 prefixEnd_7245512 3720430243919361134678503 := by
  unfold tailWord_7245512
  simp only [CollatzResearch.WordTrace]
  refine ⟨132132766463377466888741395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176177021951169955851655193 132132766463377466888741395)
  ·
    refine ⟨198199149695066200333112093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132132766463377466888741395 198199149695066200333112093)
    ·
      refine ⟨74324681135649825124917035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 198199149695066200333112093 74324681135649825124917035)
      ·
        refine ⟨111487021703474737687375553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74324681135649825124917035 111487021703474737687375553)
        ·
          refine ⟨83615266277606053265531665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111487021703474737687375553 83615266277606053265531665)
          ·
            refine ⟨62711449708204539949148749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83615266277606053265531665 62711449708204539949148749)
            ·
              refine ⟨23516793640576702480930781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62711449708204539949148749 23516793640576702480930781)
              ·
                refine ⟨8818797615216263430349043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23516793640576702480930781 8818797615216263430349043)
                ·
                  refine ⟨13228196422824395145523565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8818797615216263430349043 13228196422824395145523565)
                  ·
                    refine ⟨4960573658559148179571337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13228196422824395145523565 4960573658559148179571337)
                    ·
                      refine ⟨3720430243919361134678503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4960573658559148179571337 3720430243919361134678503)
                      ·
                        rfl

theorem cell23_7245512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 3, 3, 1, 3, 2].length) (baseStart_7245512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7245512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7245512 prefixEnd_7245512 := by exact prefixLift 7245512
  have htrace : WordTrace (prefixWord ++ tailWord_7245512) baseStart_7245512 baseEnd_7245512 := by
    simpa [prefixWord, tailWord_7245512, baseEnd_7245512] using wordTrace_append hprefix tailTrace_7245512
  have hstable : (prefixWord ++ tailWord_7245512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7245512).length < 2 ^ (prefixWord ++ tailWord_7245512).sum := by decide
  have hdescent : baseEnd_7245512 < baseStart_7245512 := by decide
  rcases family_descends (prefixWord ++ tailWord_7245512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7245518 : List Nat := [4, 1, 1, 1, 3, 1, 1, 1, 4, 6]
def baseStart_7245518 : Nat := 118140960795 + 7245518 * 2 ^ 59
def prefixEnd_7245518 : Nat := 4983230072969 + 3 ^ 40 * 7245518 * 2
def baseEnd_7245518 : Nat := 1240144441601096037067825

theorem tailTrace_7245518 : CollatzResearch.WordTrace tailWord_7245518 prefixEnd_7245518 1240144441601096037067825 := by
  unfold tailWord_7245518
  simp only [CollatzResearch.WordTrace]
  refine ⟨33033218970591649600275151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 176177167843155464534800805 33033218970591649600275151)
  ·
    refine ⟨49549828455887474400412727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33033218970591649600275151 49549828455887474400412727)
    ·
      refine ⟨74324742683831211600619091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49549828455887474400412727 74324742683831211600619091)
      ·
        refine ⟨111487114025746817400928637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74324742683831211600619091 111487114025746817400928637)
        ·
          refine ⟨41807667759655056525348239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 111487114025746817400928637 41807667759655056525348239)
          ·
            refine ⟨62711501639482584788022359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41807667759655056525348239 62711501639482584788022359)
            ·
              refine ⟨94067252459223877182033539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62711501639482584788022359 94067252459223877182033539)
              ·
                refine ⟨141100878688835815773050309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94067252459223877182033539 141100878688835815773050309)
                ·
                  refine ⟨26456414754156715457446933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 141100878688835815773050309 26456414754156715457446933)
                  ·
                    refine ⟨1240144441601096037067825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26456414754156715457446933 1240144441601096037067825)
                    ·
                      rfl

theorem cell23_7245518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 1, 4, 6].length) (baseStart_7245518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7245518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7245518 prefixEnd_7245518 := by exact prefixLift 7245518
  have htrace : WordTrace (prefixWord ++ tailWord_7245518) baseStart_7245518 baseEnd_7245518 := by
    simpa [prefixWord, tailWord_7245518, baseEnd_7245518] using wordTrace_append hprefix tailTrace_7245518
  have hstable : (prefixWord ++ tailWord_7245518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7245518).length < 2 ^ (prefixWord ++ tailWord_7245518).sum := by decide
  have hdescent : baseEnd_7245518 < baseStart_7245518 := by decide
  rcases family_descends (prefixWord ++ tailWord_7245518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7245548 : List Nat := [2, 2, 1, 1, 2, 2, 4, 2, 7]
def baseStart_7245548 : Nat := 118140960795 + 7245548 * 2 ^ 59
def prefixEnd_7245548 : Nat := 4983230072969 + 3 ^ 40 * 7245548 * 2
def baseEnd_7245548 : Nat := 413383192135880332647593

theorem tailTrace_7245548 : CollatzResearch.WordTrace tailWord_7245548 prefixEnd_7245548 413383192135880332647593 := by
  unfold tailWord_7245548
  simp only [CollatzResearch.WordTrace]
  refine ⟨132133422977312255962896649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176177897303083007950528865 132133422977312255962896649)
  ·
    refine ⟨99100067232984191972172487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132133422977312255962896649 99100067232984191972172487)
    ·
      refine ⟨148650100849476287958258731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99100067232984191972172487 148650100849476287958258731)
      ·
        refine ⟨222975151274214431937388097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148650100849476287958258731 222975151274214431937388097)
        ·
          refine ⟨167231363455660823953041073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 222975151274214431937388097 167231363455660823953041073)
          ·
            refine ⟨125423522591745617964780805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 167231363455660823953041073 125423522591745617964780805)
            ·
              refine ⟨23516910485952303368396401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 125423522591745617964780805 23516910485952303368396401)
              ·
                refine ⟨17637682864464227526297301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23516910485952303368396401 17637682864464227526297301)
                ·
                  refine ⟨413383192135880332647593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17637682864464227526297301 413383192135880332647593)
                  ·
                    rfl

theorem cell23_7245548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 7].length) (baseStart_7245548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7245548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7245548 prefixEnd_7245548 := by exact prefixLift 7245548
  have htrace : WordTrace (prefixWord ++ tailWord_7245548) baseStart_7245548 baseEnd_7245548 := by
    simpa [prefixWord, tailWord_7245548, baseEnd_7245548] using wordTrace_append hprefix tailTrace_7245548
  have hstable : (prefixWord ++ tailWord_7245548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7245548).length < 2 ^ (prefixWord ++ tailWord_7245548).sum := by decide
  have hdescent : baseEnd_7245548 < baseStart_7245548 := by decide
  rcases family_descends (prefixWord ++ tailWord_7245548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7245565 : List Nat := [1, 4, 1, 1, 1, 1, 2, 7, 5]
def baseStart_7245565 : Nat := 118140960795 + 7245565 * 2 ^ 59
def prefixEnd_7245565 : Nat := 4983230072969 + 3 ^ 40 * 7245565 * 2
def baseEnd_7245565 : Nat := 413384162043783269701751

theorem tailTrace_7245565 : CollatzResearch.WordTrace tailWord_7245565 prefixEnd_7245565 413384162043783269701751 := by
  unfold tailWord_7245565
  simp only [CollatzResearch.WordTrace]
  refine ⟨264267465995562923829162149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176178310663708615886108099 264267465995562923829162149)
  ·
    refine ⟨49550149874168048217967903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 264267465995562923829162149 49550149874168048217967903)
    ·
      refine ⟨74325224811252072326951855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49550149874168048217967903 74325224811252072326951855)
      ·
        refine ⟨111487837216878108490427783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74325224811252072326951855 111487837216878108490427783)
        ·
          refine ⟨167231755825317162735641675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111487837216878108490427783 167231755825317162735641675)
          ·
            refine ⟨250847633737975744103462513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 167231755825317162735641675 250847633737975744103462513)
            ·
              refine ⟨188135725303481808077596885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 250847633737975744103462513 188135725303481808077596885)
              ·
                refine ⟨4409431061800354876818677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 188135725303481808077596885 4409431061800354876818677)
                ·
                  refine ⟨413384162043783269701751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4409431061800354876818677 413384162043783269701751)
                  ·
                    rfl

theorem cell23_7245565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 7, 5].length) (baseStart_7245565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7245565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7245565 prefixEnd_7245565 := by exact prefixLift 7245565
  have htrace : WordTrace (prefixWord ++ tailWord_7245565) baseStart_7245565 baseEnd_7245565 := by
    simpa [prefixWord, tailWord_7245565, baseEnd_7245565] using wordTrace_append hprefix tailTrace_7245565
  have hstable : (prefixWord ++ tailWord_7245565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7245565).length < 2 ^ (prefixWord ++ tailWord_7245565).sum := by decide
  have hdescent : baseEnd_7245565 < baseStart_7245565 := by decide
  rcases family_descends (prefixWord ++ tailWord_7245565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7245585 : List Nat := [1, 2, 2, 1, 1, 3, 1, 3, 2, 5, 2]
def baseStart_7245585 : Nat := 118140960795 + 7245585 * 2 ^ 59
def prefixEnd_7245585 : Nat := 4983230072969 + 3 ^ 40 * 7245585 * 2
def baseEnd_7245585 : Nat := 3720467728007139349065667

theorem tailTrace_7245585 : CollatzResearch.WordTrace tailWord_7245585 prefixEnd_7245585 3720467728007139349065667 := by
  unfold tailWord_7245585
  simp only [CollatzResearch.WordTrace]
  refine ⟨264268195455490467244890209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176178796970326978163260139 264268195455490467244890209)
  ·
    refine ⟨198201146591617850433667657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 264268195455490467244890209 198201146591617850433667657)
    ·
      refine ⟨148650859943713387825250743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 198201146591617850433667657 148650859943713387825250743)
      ·
        refine ⟨222976289915570081737876115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148650859943713387825250743 222976289915570081737876115)
        ·
          refine ⟨334464434873355122606814173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 222976289915570081737876115 334464434873355122606814173)
          ·
            refine ⟨125424163077508170977555315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 334464434873355122606814173 125424163077508170977555315)
            ·
              refine ⟨188136244616262256466332973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125424163077508170977555315 188136244616262256466332973)
              ·
                refine ⟨70551091731098346174874865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 188136244616262256466332973 70551091731098346174874865)
                ·
                  refine ⟨52913318798323759631156149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 70551091731098346174874865 52913318798323759631156149)
                  ·
                    refine ⟨4960623637342852465420889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 52913318798323759631156149 4960623637342852465420889)
                    ·
                      refine ⟨3720467728007139349065667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4960623637342852465420889 3720467728007139349065667)
                      ·
                        rfl

theorem cell23_7245585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 5, 2].length) (baseStart_7245585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7245585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7245585 prefixEnd_7245585 := by exact prefixLift 7245585
  have htrace : WordTrace (prefixWord ++ tailWord_7245585) baseStart_7245585 baseEnd_7245585 := by
    simpa [prefixWord, tailWord_7245585, baseEnd_7245585] using wordTrace_append hprefix tailTrace_7245585
  have hstable : (prefixWord ++ tailWord_7245585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7245585).length < 2 ^ (prefixWord ++ tailWord_7245585).sum := by decide
  have hdescent : baseEnd_7245585 < baseStart_7245585 := by decide
  rcases family_descends (prefixWord ++ tailWord_7245585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7245615 : List Nat := [1, 1, 2, 1, 2, 1, 2, 4, 1, 6, 2]
def baseStart_7245615 : Nat := 118140960795 + 7245615 * 2 ^ 59
def prefixEnd_7245615 : Nat := 4983230072969 + 3 ^ 40 * 7245615 * 2
def baseEnd_7245615 : Nat := 3720483132426774231690529

theorem tailTrace_7245615 : CollatzResearch.WordTrace tailWord_7245615 prefixEnd_7245615 3720483132426774231690529 := by
  unfold tailWord_7245615
  simp only [CollatzResearch.WordTrace]
  refine ⟨264269289645381782368482299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176179526430254521578988199 264269289645381782368482299)
  ·
    refine ⟨396403934468072673552723449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264269289645381782368482299 396403934468072673552723449)
    ·
      refine ⟨297302950851054505164542587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 396403934468072673552723449 297302950851054505164542587)
      ·
        refine ⟨445954426276581757746813881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 297302950851054505164542587 445954426276581757746813881)
        ·
          refine ⟨334465819707436318310110411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 445954426276581757746813881 334465819707436318310110411)
          ·
            refine ⟨501698729561154477465165617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 334465819707436318310110411 501698729561154477465165617)
            ·
              refine ⟨376274047170865858098874213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 501698729561154477465165617 376274047170865858098874213)
              ·
                refine ⟨70551383844537348393538915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 376274047170865858098874213 70551383844537348393538915)
                ·
                  refine ⟨105827075766806022590308373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70551383844537348393538915 105827075766806022590308373)
                  ·
                    refine ⟨4960644176569032308920705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 105827075766806022590308373 4960644176569032308920705)
                    ·
                      refine ⟨3720483132426774231690529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4960644176569032308920705 3720483132426774231690529)
                      ·
                        rfl

theorem cell23_7245615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 4, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 4, 1, 6, 2].length) (baseStart_7245615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7245615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7245615 prefixEnd_7245615 := by exact prefixLift 7245615
  have htrace : WordTrace (prefixWord ++ tailWord_7245615) baseStart_7245615 baseEnd_7245615 := by
    simpa [prefixWord, tailWord_7245615, baseEnd_7245615] using wordTrace_append hprefix tailTrace_7245615
  have hstable : (prefixWord ++ tailWord_7245615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7245615).length < 2 ^ (prefixWord ++ tailWord_7245615).sum := by decide
  have hdescent : baseEnd_7245615 < baseStart_7245615 := by decide
  rcases family_descends (prefixWord ++ tailWord_7245615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7245622 : List Nat := [5, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5]
def baseStart_7245622 : Nat := 118140960795 + 7245622 * 2 ^ 59
def prefixEnd_7245622 : Nat := 4983230072969 + 3 ^ 40 * 7245622 * 2
def baseEnd_7245622 : Nat := 3720486726791355704302997

theorem tailTrace_7245622 : CollatzResearch.WordTrace tailWord_7245622 prefixEnd_7245622 3720486726791355704302997 := by
  unfold tailWord_7245622
  simp only [CollatzResearch.WordTrace]
  refine ⟨16516846559772276410249195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 176179696637570948375991413 16516846559772276410249195)
  ·
    refine ⟨24775269839658414615373793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16516846559772276410249195 24775269839658414615373793)
    ·
      refine ⟨18581452379743810961530345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24775269839658414615373793 18581452379743810961530345)
      ·
        refine ⟨13936089284807858221147759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18581452379743810961530345 13936089284807858221147759)
        ·
          refine ⟨20904133927211787331721639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13936089284807858221147759 20904133927211787331721639)
          ·
            refine ⟨31356200890817680997582459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20904133927211787331721639 31356200890817680997582459)
            ·
              refine ⟨47034301336226521496373689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31356200890817680997582459 47034301336226521496373689)
              ·
                refine ⟨35275726002169891122280267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47034301336226521496373689 35275726002169891122280267)
                ·
                  refine ⟨52913589003254836683420401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35275726002169891122280267 52913589003254836683420401)
                  ·
                    refine ⟨39685191752441127512565301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 52913589003254836683420401 39685191752441127512565301)
                    ·
                      refine ⟨3720486726791355704302997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39685191752441127512565301 3720486726791355704302997)
                      ·
                        rfl

theorem cell23_7245622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5].length) (baseStart_7245622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7245622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7245622 prefixEnd_7245622 := by exact prefixLift 7245622
  have htrace : WordTrace (prefixWord ++ tailWord_7245622) baseStart_7245622 baseEnd_7245622 := by
    simpa [prefixWord, tailWord_7245622, baseEnd_7245622] using wordTrace_append hprefix tailTrace_7245622
  have hstable : (prefixWord ++ tailWord_7245622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7245622).length < 2 ^ (prefixWord ++ tailWord_7245622).sum := by decide
  have hdescent : baseEnd_7245622 < baseStart_7245622 := by decide
  rcases family_descends (prefixWord ++ tailWord_7245622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7245682 : List Nat := [3, 2, 1, 2, 1, 1, 1, 1, 7, 1, 3]
def baseStart_7245682 : Nat := 118140960795 + 7245682 * 2 ^ 59
def prefixEnd_7245682 : Nat := 4983230072969 + 3 ^ 40 * 7245682 * 2
def baseEnd_7245682 : Nat := 3720517535630625469552721

theorem tailTrace_7245682 : CollatzResearch.WordTrace tailWord_7245682 prefixEnd_7245682 3720517535630625469552721 := by
  unfold tailWord_7245682
  simp only [CollatzResearch.WordTrace]
  refine ⟨66067933334034763202792825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176181155557426035207447533 66067933334034763202792825)
  ·
    refine ⟨49550950000526072402094619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66067933334034763202792825 49550950000526072402094619)
    ·
      refine ⟨74326425000789108603141929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49550950000526072402094619 74326425000789108603141929)
      ·
        refine ⟨55744818750591831452356447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74326425000789108603141929 55744818750591831452356447)
        ·
          refine ⟨83617228125887747178534671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55744818750591831452356447 83617228125887747178534671)
          ·
            refine ⟨125425842188831620767802007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83617228125887747178534671 125425842188831620767802007)
            ·
              refine ⟨188138763283247431151703011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125425842188831620767802007 188138763283247431151703011)
              ·
                refine ⟨282208144924871146727554517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 188138763283247431151703011 282208144924871146727554517)
                ·
                  refine ⟨6614253396676667501427059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 282208144924871146727554517 6614253396676667501427059)
                  ·
                    refine ⟨9921380095015001252140589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6614253396676667501427059 9921380095015001252140589)
                    ·
                      refine ⟨3720517535630625469552721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9921380095015001252140589 3720517535630625469552721)
                      ·
                        rfl

theorem cell23_7245682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 1, 7, 1, 3].length) (baseStart_7245682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7245682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7245682 prefixEnd_7245682 := by exact prefixLift 7245682
  have htrace : WordTrace (prefixWord ++ tailWord_7245682) baseStart_7245682 baseEnd_7245682 := by
    simpa [prefixWord, tailWord_7245682, baseEnd_7245682] using wordTrace_append hprefix tailTrace_7245682
  have hstable : (prefixWord ++ tailWord_7245682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7245682).length < 2 ^ (prefixWord ++ tailWord_7245682).sum := by decide
  have hdescent : baseEnd_7245682 < baseStart_7245682 := by decide
  rcases family_descends (prefixWord ++ tailWord_7245682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7245699 : List Nat := [1, 1, 1, 3, 4, 3, 2, 1, 3, 1, 3]
def baseStart_7245699 : Nat := 118140960795 + 7245699 * 2 ^ 59
def prefixEnd_7245699 : Nat := 4983230072969 + 3 ^ 40 * 7245699 * 2
def baseEnd_7245699 : Nat := 3720526264801751903040143

theorem tailTrace_7245699 : CollatzResearch.WordTrace tailWord_7245699 prefixEnd_7245699 3720526264801751903040143 := by
  unfold tailWord_7245699
  simp only [CollatzResearch.WordTrace]
  refine ⟨264272353377077464714540151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176181568918051643143026767 264272353377077464714540151)
  ·
    refine ⟨396408530065616197071810227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264272353377077464714540151 396408530065616197071810227)
    ·
      refine ⟨594612795098424295607715341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 396408530065616197071810227 594612795098424295607715341)
      ·
        refine ⟨222979798161909110852893253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 594612795098424295607715341 222979798161909110852893253)
        ·
          refine ⟨41808712155357958284917485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 222979798161909110852893253 41808712155357958284917485)
          ·
            refine ⟨15678267058259234356844057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41808712155357958284917485 15678267058259234356844057)
            ·
              refine ⟨11758700293694425767633043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15678267058259234356844057 11758700293694425767633043)
              ·
                refine ⟨17638050440541638651449565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11758700293694425767633043 17638050440541638651449565)
                ·
                  refine ⟨6614268915203114494293587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17638050440541638651449565 6614268915203114494293587)
                  ·
                    refine ⟨9921403372804671741440381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6614268915203114494293587 9921403372804671741440381)
                    ·
                      refine ⟨3720526264801751903040143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9921403372804671741440381 3720526264801751903040143)
                      ·
                        rfl

theorem cell23_7245699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 2, 1, 3, 1, 3].length) (baseStart_7245699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7245699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7245699 prefixEnd_7245699 := by exact prefixLift 7245699
  have htrace : WordTrace (prefixWord ++ tailWord_7245699) baseStart_7245699 baseEnd_7245699 := by
    simpa [prefixWord, tailWord_7245699, baseEnd_7245699] using wordTrace_append hprefix tailTrace_7245699
  have hstable : (prefixWord ++ tailWord_7245699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7245699).length < 2 ^ (prefixWord ++ tailWord_7245699).sum := by decide
  have hdescent : baseEnd_7245699 < baseStart_7245699 := by decide
  rcases family_descends (prefixWord ++ tailWord_7245699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7245732 : List Nat := [2, 3, 1, 2, 1, 3, 1, 2, 4, 4]
def baseStart_7245732 : Nat := 118140960795 + 7245732 * 2 ^ 59
def prefixEnd_7245732 : Nat := 4983230072969 + 3 ^ 40 * 7245732 * 2
def baseEnd_7245732 : Nat := 1240181069887783424642497

theorem tailTrace_7245732 : CollatzResearch.WordTrace tailWord_7245732 prefixEnd_7245732 1240181069887783424642497 := by
  unfold tailWord_7245732
  simp only [CollatzResearch.WordTrace]
  refine ⟨132136778492978955675245725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176182371323971940900327633 132136778492978955675245725)
  ·
    refine ⟨49551291934867108378217147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132136778492978955675245725 49551291934867108378217147)
    ·
      refine ⟨74326937902300662567325721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49551291934867108378217147 74326937902300662567325721)
      ·
        refine ⟨55745203426725496925494291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74326937902300662567325721 55745203426725496925494291)
        ·
          refine ⟨83617805140088245388241437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55745203426725496925494291 83617805140088245388241437)
          ·
            refine ⟨31356676927533092020590539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 83617805140088245388241437 31356676927533092020590539)
            ·
              refine ⟨47035015391299638030885809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31356676927533092020590539 47035015391299638030885809)
              ·
                refine ⟨35276261543474728523164357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47035015391299638030885809 35276261543474728523164357)
                ·
                  refine ⟨6614299039401511598093317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35276261543474728523164357 6614299039401511598093317)
                  ·
                    refine ⟨1240181069887783424642497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6614299039401511598093317 1240181069887783424642497)
                    ·
                      rfl

theorem cell23_7245732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 1, 2, 4, 4].length) (baseStart_7245732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7245732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7245732 prefixEnd_7245732 := by exact prefixLift 7245732
  have htrace : WordTrace (prefixWord ++ tailWord_7245732) baseStart_7245732 baseEnd_7245732 := by
    simpa [prefixWord, tailWord_7245732, baseEnd_7245732] using wordTrace_append hprefix tailTrace_7245732
  have hstable : (prefixWord ++ tailWord_7245732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7245732).length < 2 ^ (prefixWord ++ tailWord_7245732).sum := by decide
  have hdescent : baseEnd_7245732 < baseStart_7245732 := by decide
  rcases family_descends (prefixWord ++ tailWord_7245732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7245745 : List Nat := [1, 2, 2, 4, 2, 1, 11]
def baseStart_7245745 : Nat := 118140960795 + 7245745 * 2 ^ 59
def prefixEnd_7245745 : Nat := 4983230072969 + 3 ^ 40 * 7245745 * 2
def baseEnd_7245745 : Nat := 45932714628541465716851

theorem tailTrace_7245745 : CollatzResearch.WordTrace tailWord_7245745 prefixEnd_7245745 45932714628541465716851 := by
  unfold tailWord_7245745
  simp only [CollatzResearch.WordTrace]
  refine ⟨264274031134910814570714689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176182687423273876380476459 264274031134910814570714689)
  ·
    refine ⟨198205523351183110928036017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 264274031134910814570714689 198205523351183110928036017)
    ·
      refine ⟨148654142513387333196027013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 198205523351183110928036017 148654142513387333196027013)
      ·
        refine ⟨27872651721260124974255065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 148654142513387333196027013 27872651721260124974255065)
        ·
          refine ⟨20904488790945093730691299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27872651721260124974255065 20904488790945093730691299)
          ·
            refine ⟨31356733186417640596036949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20904488790945093730691299 31356733186417640596036949)
            ·
              refine ⟨45932714628541465716851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 31356733186417640596036949 45932714628541465716851)
              ·
                rfl

theorem cell23_7245745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 11].length) (baseStart_7245745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7245745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7245745 prefixEnd_7245745 := by exact prefixLift 7245745
  have htrace : WordTrace (prefixWord ++ tailWord_7245745) baseStart_7245745 baseEnd_7245745 := by
    simpa [prefixWord, tailWord_7245745, baseEnd_7245745] using wordTrace_append hprefix tailTrace_7245745
  have hstable : (prefixWord ++ tailWord_7245745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7245745).length < 2 ^ (prefixWord ++ tailWord_7245745).sum := by decide
  have hdescent : baseEnd_7245745 < baseStart_7245745 := by decide
  rcases family_descends (prefixWord ++ tailWord_7245745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7245806 : List Nat := [4, 1, 2, 1, 3, 1, 1, 4, 2, 1, 3]
def baseStart_7245806 : Nat := 118140960795 + 7245806 * 2 ^ 59
def prefixEnd_7245806 : Nat := 4983230072969 + 3 ^ 40 * 7245806 * 2
def baseEnd_7245806 : Nat := 3720581207231782984402151

theorem tailTrace_7245806 : CollatzResearch.WordTrace tailWord_7245806 prefixEnd_7245806 3720581207231782984402151 := by
  unfold tailWord_7245806
  simp only [CollatzResearch.WordTrace]
  refine ⟨33034531998461227748585659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 176184170658459881325790181 33034531998461227748585659)
  ·
    refine ⟨49551797997691841622878489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33034531998461227748585659 49551797997691841622878489)
    ·
      refine ⟨37163848498268881217158867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49551797997691841622878489 37163848498268881217158867)
      ·
        refine ⟨55745772747403321825738301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37163848498268881217158867 55745772747403321825738301)
        ·
          refine ⟨20904664780276245684651863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55745772747403321825738301 20904664780276245684651863)
          ·
            refine ⟨31356997170414368526977795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20904664780276245684651863 31356997170414368526977795)
            ·
              refine ⟨47035495755621552790466693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31356997170414368526977795 47035495755621552790466693)
              ·
                refine ⟨8819155454179041148212505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47035495755621552790466693 8819155454179041148212505)
                ·
                  refine ⟨6614366590634280861159379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8819155454179041148212505 6614366590634280861159379)
                  ·
                    refine ⟨9921549885951421291739069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6614366590634280861159379 9921549885951421291739069)
                    ·
                      refine ⟨3720581207231782984402151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9921549885951421291739069 3720581207231782984402151)
                      ·
                        rfl

theorem cell23_7245806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 1, 4, 2, 1, 3].length) (baseStart_7245806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7245806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7245806 prefixEnd_7245806 := by exact prefixLift 7245806
  have htrace : WordTrace (prefixWord ++ tailWord_7245806) baseStart_7245806 baseEnd_7245806 := by
    simpa [prefixWord, tailWord_7245806, baseEnd_7245806] using wordTrace_append hprefix tailTrace_7245806
  have hstable : (prefixWord ++ tailWord_7245806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7245806).length < 2 ^ (prefixWord ++ tailWord_7245806).sum := by decide
  have hdescent : baseEnd_7245806 < baseStart_7245806 := by decide
  rcases family_descends (prefixWord ++ tailWord_7245806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7245829 : List Nat := [1, 3, 1, 1, 2, 4, 1, 3, 1, 4, 2]
def baseStart_7245829 : Nat := 118140960795 + 7245829 * 2 ^ 59
def prefixEnd_7245829 : Nat := 4983230072969 + 3 ^ 40 * 7245829 * 2
def baseEnd_7245829 : Nat := 3720593017286836394414545

theorem tailTrace_7245829 : CollatzResearch.WordTrace tailWord_7245829 prefixEnd_7245829 3720593017286836394414545 := by
  unfold tailWord_7245829
  simp only [CollatzResearch.WordTrace]
  refine ⟨264277094866606496916772541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176184729911070997944515027 264277094866606496916772541)
  ·
    refine ⟨99103910574977436343789703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 264277094866606496916772541 99103910574977436343789703)
    ·
      refine ⟨148655865862466154515684555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99103910574977436343789703 148655865862466154515684555)
      ·
        refine ⟨222983798793699231773526833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148655865862466154515684555 222983798793699231773526833)
        ·
          refine ⟨167237849095274423830145125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 222983798793699231773526833 167237849095274423830145125)
          ·
            refine ⟨31357096705363954468152211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 167237849095274423830145125 31357096705363954468152211)
            ·
              refine ⟨47035645058045931702228317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31357096705363954468152211 47035645058045931702228317)
              ·
                refine ⟨17638366896767224388335619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47035645058045931702228317 17638366896767224388335619)
                ·
                  refine ⟨26457550345150836582503429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17638366896767224388335619 26457550345150836582503429)
                  ·
                    refine ⟨4960790689715781859219393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26457550345150836582503429 4960790689715781859219393)
                    ·
                      refine ⟨3720593017286836394414545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4960790689715781859219393 3720593017286836394414545)
                      ·
                        rfl

theorem cell23_7245829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 1, 3, 1, 4, 2].length) (baseStart_7245829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7245829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7245829 prefixEnd_7245829 := by exact prefixLift 7245829
  have htrace : WordTrace (prefixWord ++ tailWord_7245829) baseStart_7245829 baseEnd_7245829 := by
    simpa [prefixWord, tailWord_7245829, baseEnd_7245829] using wordTrace_append hprefix tailTrace_7245829
  have hstable : (prefixWord ++ tailWord_7245829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7245829).length < 2 ^ (prefixWord ++ tailWord_7245829).sum := by decide
  have hdescent : baseEnd_7245829 < baseStart_7245829 := by decide
  rcases family_descends (prefixWord ++ tailWord_7245829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7245830 : List Nat := [6, 2, 1, 2, 1, 1, 3, 7]
def baseStart_7245830 : Nat := 118140960795 + 7245830 * 2 ^ 59
def prefixEnd_7245830 : Nat := 4983230072969 + 3 ^ 40 * 7245830 * 2
def baseEnd_7245830 : Nat := 137799760398795958907483

theorem tailTrace_7245830 : CollatzResearch.WordTrace tailWord_7245830 prefixEnd_7245830 137799760398795958907483 := by
  unfold tailWord_7245830
  simp only [CollatzResearch.WordTrace]
  refine ⟨8258660354362589815236217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 176184754226401916058372629 8258660354362589815236217)
  ·
    refine ⟨6193995265771942361427163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8258660354362589815236217 6193995265771942361427163)
    ·
      refine ⟨9290992898657913542140745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6193995265771942361427163 9290992898657913542140745)
      ·
        refine ⟨6968244673993435156605559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9290992898657913542140745 6968244673993435156605559)
        ·
          refine ⟨10452367010990152734908339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6968244673993435156605559 10452367010990152734908339)
          ·
            refine ⟨15678550516485229102362509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10452367010990152734908339 15678550516485229102362509)
            ·
              refine ⟨5879456443681960913385941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15678550516485229102362509 5879456443681960913385941)
              ·
                refine ⟨137799760398795958907483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5879456443681960913385941 137799760398795958907483)
                ·
                  rfl

theorem cell23_7245830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 3, 7].length) (baseStart_7245830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7245830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7245830 prefixEnd_7245830 := by exact prefixLift 7245830
  have htrace : WordTrace (prefixWord ++ tailWord_7245830) baseStart_7245830 baseEnd_7245830 := by
    simpa [prefixWord, tailWord_7245830, baseEnd_7245830] using wordTrace_append hprefix tailTrace_7245830
  have hstable : (prefixWord ++ tailWord_7245830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7245830).length < 2 ^ (prefixWord ++ tailWord_7245830).sum := by decide
  have hdescent : baseEnd_7245830 < baseStart_7245830 := by decide
  rcases family_descends (prefixWord ++ tailWord_7245830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7245832 : List Nat := [2, 1, 3, 2, 1, 2, 1, 2, 2, 4, 3]
def baseStart_7245832 : Nat := 118140960795 + 7245832 * 2 ^ 59
def prefixEnd_7245832 : Nat := 4983230072969 + 3 ^ 40 * 7245832 * 2
def baseEnd_7245832 : Nat := 3720594557728799882677031

theorem tailTrace_7245832 : CollatzResearch.WordTrace tailWord_7245832 prefixEnd_7245832 3720594557728799882677031 := by
  unfold tailWord_7245832
  simp only [CollatzResearch.WordTrace]
  refine ⟨132138602142797814214565875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176184802857063752286087833 132138602142797814214565875)
  ·
    refine ⟨198207903214196721321848813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132138602142797814214565875 198207903214196721321848813)
    ·
      refine ⟨74327963705323770495693305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 198207903214196721321848813 74327963705323770495693305)
      ·
        refine ⟨55745972778992827871769979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74327963705323770495693305 55745972778992827871769979)
        ·
          refine ⟨83618959168489241807654969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55745972778992827871769979 83618959168489241807654969)
          ·
            refine ⟨62714219376366931355741227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83618959168489241807654969 62714219376366931355741227)
            ·
              refine ⟨94071329064550397033611841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62714219376366931355741227 94071329064550397033611841)
              ·
                refine ⟨70553496798412797775208881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 94071329064550397033611841 70553496798412797775208881)
                ·
                  refine ⟨52915122598809598331406661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 70553496798412797775208881 52915122598809598331406661)
                  ·
                    refine ⟨9921585487276799687138749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 52915122598809598331406661 9921585487276799687138749)
                    ·
                      refine ⟨3720594557728799882677031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9921585487276799687138749 3720594557728799882677031)
                      ·
                        rfl

theorem cell23_7245832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 2, 2, 4, 3].length) (baseStart_7245832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7245832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7245832 prefixEnd_7245832 := by exact prefixLift 7245832
  have htrace : WordTrace (prefixWord ++ tailWord_7245832) baseStart_7245832 baseEnd_7245832 := by
    simpa [prefixWord, tailWord_7245832, baseEnd_7245832] using wordTrace_append hprefix tailTrace_7245832
  have hstable : (prefixWord ++ tailWord_7245832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7245832).length < 2 ^ (prefixWord ++ tailWord_7245832).sum := by decide
  have hdescent : baseEnd_7245832 < baseStart_7245832 := by decide
  rcases family_descends (prefixWord ++ tailWord_7245832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7245880 : List Nat := [2, 1, 2, 1, 6, 1, 3, 1, 2, 2, 2]
def baseStart_7245880 : Nat := 118140960795 + 7245880 * 2 ^ 59
def prefixEnd_7245880 : Nat := 4983230072969 + 3 ^ 40 * 7245880 * 2
def baseEnd_7245880 : Nat := 3720619204800215694876811

theorem tailTrace_7245880 : CollatzResearch.WordTrace tailWord_7245880 prefixEnd_7245880 3720619204800215694876811 := by
  unfold tailWord_7245880
  simp only [CollatzResearch.WordTrace]
  refine ⟨132139477494710866313439547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176185969992947821751252729 132139477494710866313439547)
  ·
    refine ⟨198209216242066299470159321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132139477494710866313439547 198209216242066299470159321)
    ·
      refine ⟨148656912181549724602619491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 198209216242066299470159321 148656912181549724602619491)
      ·
        refine ⟨222985368272324586903929237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148656912181549724602619491 222985368272324586903929237)
        ·
          refine ⟨10452439137765215011121683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 222985368272324586903929237 10452439137765215011121683)
          ·
            refine ⟨15678658706647822516682525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10452439137765215011121683 15678658706647822516682525)
            ·
              refine ⟨5879497014992933443755947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15678658706647822516682525 5879497014992933443755947)
              ·
                refine ⟨8819245522489400165633921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5879497014992933443755947 8819245522489400165633921)
                ·
                  refine ⟨6614434141867050124225441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8819245522489400165633921 6614434141867050124225441)
                  ·
                    refine ⟨4960825606400287593169081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6614434141867050124225441 4960825606400287593169081)
                    ·
                      refine ⟨3720619204800215694876811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4960825606400287593169081 3720619204800215694876811)
                      ·
                        rfl

theorem cell23_7245880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 3, 1, 2, 2, 2].length) (baseStart_7245880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7245880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7245880 prefixEnd_7245880 := by exact prefixLift 7245880
  have htrace : WordTrace (prefixWord ++ tailWord_7245880) baseStart_7245880 baseEnd_7245880 := by
    simpa [prefixWord, tailWord_7245880, baseEnd_7245880] using wordTrace_append hprefix tailTrace_7245880
  have hstable : (prefixWord ++ tailWord_7245880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7245880).length < 2 ^ (prefixWord ++ tailWord_7245880).sum := by decide
  have hdescent : baseEnd_7245880 < baseStart_7245880 := by decide
  rcases family_descends (prefixWord ++ tailWord_7245880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7245919 : List Nat := [1, 1, 2, 3, 1, 1, 2, 4, 2, 4, 2]
def baseStart_7245919 : Nat := 118140960795 + 7245919 * 2 ^ 59
def prefixEnd_7245919 : Nat := 4983230072969 + 3 ^ 40 * 7245919 * 2
def baseEnd_7245919 : Nat := 3720639230545741042289131

theorem tailTrace_7245919 : CollatzResearch.WordTrace tailWord_7245919 prefixEnd_7245919 3720639230545741042289131 := by
  unfold tailWord_7245919
  simp only [CollatzResearch.WordTrace]
  refine ⟨264280377436280442287548811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176186918290853628191699207 264280377436280442287548811)
  ·
    refine ⟨396420566154420663431323217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264280377436280442287548811 396420566154420663431323217)
    ·
      refine ⟨297315424615815497573492413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 396420566154420663431323217 297315424615815497573492413)
      ·
        refine ⟨111493284230930811590059655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 297315424615815497573492413 111493284230930811590059655)
        ·
          refine ⟨167239926346396217385089483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111493284230930811590059655 167239926346396217385089483)
          ·
            refine ⟨250859889519594326077634225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 167239926346396217385089483 250859889519594326077634225)
            ·
              refine ⟨188144917139695744558225669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 250859889519594326077634225 188144917139695744558225669)
              ·
                refine ⟨35277171963692952104667313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 188144917139695744558225669 35277171963692952104667313)
                ·
                  refine ⟨26457878972769714078500485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35277171963692952104667313 26457878972769714078500485)
                  ·
                    refine ⟨4960852307394321389718841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26457878972769714078500485 4960852307394321389718841)
                    ·
                      refine ⟨3720639230545741042289131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4960852307394321389718841 3720639230545741042289131)
                      ·
                        rfl

theorem cell23_7245919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 4, 2, 4, 2].length) (baseStart_7245919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7245919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7245919 prefixEnd_7245919 := by exact prefixLift 7245919
  have htrace : WordTrace (prefixWord ++ tailWord_7245919) baseStart_7245919 baseEnd_7245919 := by
    simpa [prefixWord, tailWord_7245919, baseEnd_7245919] using wordTrace_append hprefix tailTrace_7245919
  have hstable : (prefixWord ++ tailWord_7245919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7245919).length < 2 ^ (prefixWord ++ tailWord_7245919).sum := by decide
  have hdescent : baseEnd_7245919 < baseStart_7245919 := by decide
  rcases family_descends (prefixWord ++ tailWord_7245919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7245956 : List Nat := [2, 3, 2, 1, 2, 1, 4, 1, 2, 2, 3]
def baseStart_7245956 : Nat := 118140960795 + 7245956 * 2 ^ 59
def prefixEnd_7245956 : Nat := 4983230072969 + 3 ^ 40 * 7245956 * 2
def baseEnd_7245956 : Nat := 3720658229329957397526461

theorem tailTrace_7245956 : CollatzResearch.WordTrace tailWord_7245956 prefixEnd_7245956 3720658229329957397526461 := by
  unfold tailWord_7245956
  simp only [CollatzResearch.WordTrace]
  refine ⟨132140863468573198803322861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176187817958097598404430481 132140863468573198803322861)
  ·
    refine ⟨49552823800714949551246073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132140863468573198803322861 49552823800714949551246073)
    ·
      refine ⟨37164617850536212163434555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49552823800714949551246073 37164617850536212163434555)
      ·
        refine ⟨55746926775804318245151833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37164617850536212163434555 55746926775804318245151833)
        ·
          refine ⟨41810195081853238683863875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55746926775804318245151833 41810195081853238683863875)
          ·
            refine ⟨62715292622779858025795813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41810195081853238683863875 62715292622779858025795813)
            ·
              refine ⟨11759117366771223379836715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 62715292622779858025795813 11759117366771223379836715)
              ·
                refine ⟨17638676050156835069755073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11759117366771223379836715 17638676050156835069755073)
                ·
                  refine ⟨13229007037617626302316305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17638676050156835069755073 13229007037617626302316305)
                  ·
                    refine ⟨9921755278213219726737229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13229007037617626302316305 9921755278213219726737229)
                    ·
                      refine ⟨3720658229329957397526461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9921755278213219726737229 3720658229329957397526461)
                      ·
                        rfl

theorem cell23_7245956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 4, 1, 2, 2, 3].length) (baseStart_7245956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7245956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7245956 prefixEnd_7245956 := by exact prefixLift 7245956
  have htrace : WordTrace (prefixWord ++ tailWord_7245956) baseStart_7245956 baseEnd_7245956 := by
    simpa [prefixWord, tailWord_7245956, baseEnd_7245956] using wordTrace_append hprefix tailTrace_7245956
  have hstable : (prefixWord ++ tailWord_7245956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7245956).length < 2 ^ (prefixWord ++ tailWord_7245956).sum := by decide
  have hdescent : baseEnd_7245956 < baseStart_7245956 := by decide
  rcases family_descends (prefixWord ++ tailWord_7245956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7245976 : List Nat := [2, 1, 2, 4, 3, 1, 2, 2, 6]
def baseStart_7245976 : Nat := 118140960795 + 7245976 * 2 ^ 59
def prefixEnd_7245976 : Nat := 4983230072969 + 3 ^ 40 * 7245976 * 2
def baseEnd_7245976 : Nat := 413407610993671924364041

theorem tailTrace_7245976 : CollatzResearch.WordTrace tailWord_7245976 prefixEnd_7245976 413407610993671924364041 := by
  unfold tailWord_7245976
  simp only [CollatzResearch.WordTrace]
  refine ⟨132141228198536970511186891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176188304264715960681582521 132141228198536970511186891)
  ·
    refine ⟨198211842297805455766780337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132141228198536970511186891 198211842297805455766780337)
    ·
      refine ⟨148658881723354091825085253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 198211842297805455766780337 148658881723354091825085253)
      ·
        refine ⟨27873540323128892217203485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 148658881723354091825085253 27873540323128892217203485)
        ·
          refine ⟨10452577621173334581451307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27873540323128892217203485 10452577621173334581451307)
          ·
            refine ⟨15678866431760001872176961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10452577621173334581451307 15678866431760001872176961)
            ·
              refine ⟨11759149823820001404132721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15678866431760001872176961 11759149823820001404132721)
              ·
                refine ⟨8819362367865001053099541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11759149823820001404132721 8819362367865001053099541)
                ·
                  refine ⟨413407610993671924364041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8819362367865001053099541 413407610993671924364041)
                  ·
                    rfl

theorem cell23_7245976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 2, 2, 6].length) (baseStart_7245976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7245976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7245976 prefixEnd_7245976 := by exact prefixLift 7245976
  have htrace : WordTrace (prefixWord ++ tailWord_7245976) baseStart_7245976 baseEnd_7245976 := by
    simpa [prefixWord, tailWord_7245976, baseEnd_7245976] using wordTrace_append hprefix tailTrace_7245976
  have hstable : (prefixWord ++ tailWord_7245976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7245976).length < 2 ^ (prefixWord ++ tailWord_7245976).sum := by decide
  have hdescent : baseEnd_7245976 < baseStart_7245976 := by decide
  rcases family_descends (prefixWord ++ tailWord_7245976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7246004 : List Nat := [2, 5, 3, 1, 2, 1, 1, 1, 2, 1, 4]
def baseStart_7246004 : Nat := 118140960795 + 7246004 * 2 ^ 59
def prefixEnd_7246004 : Nat := 4983230072969 + 3 ^ 40 * 7246004 * 2
def baseEnd_7246004 : Nat := 3720682876401373209726241

theorem tailTrace_7246004 : CollatzResearch.WordTrace tailWord_7246004 prefixEnd_7246004 3720682876401373209726241 := by
  unfold tailWord_7246004
  simp only [CollatzResearch.WordTrace]
  refine ⟨132141738820486250902196533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176188985093981667869595377 132141738820486250902196533)
  ·
    refine ⟨12388288014420586022080925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 132141738820486250902196533 12388288014420586022080925)
    ·
      refine ⟨4645608005407719758280347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12388288014420586022080925 4645608005407719758280347)
      ·
        refine ⟨6968412008111579637420521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4645608005407719758280347 6968412008111579637420521)
        ·
          refine ⟨5226309006083684728065391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6968412008111579637420521 5226309006083684728065391)
          ·
            refine ⟨7839463509125527092098087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5226309006083684728065391 7839463509125527092098087)
            ·
              refine ⟨11759195263688290638147131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7839463509125527092098087 11759195263688290638147131)
              ·
                refine ⟨17638792895532435957220697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11759195263688290638147131 17638792895532435957220697)
                ·
                  refine ⟨13229094671649326967915523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17638792895532435957220697 13229094671649326967915523)
                  ·
                    refine ⟨19843642007473990451873285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13229094671649326967915523 19843642007473990451873285)
                    ·
                      refine ⟨3720682876401373209726241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19843642007473990451873285 3720682876401373209726241)
                      ·
                        rfl

theorem cell23_7246004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 2, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 2, 1, 1, 1, 2, 1, 4].length) (baseStart_7246004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7246004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7246004 prefixEnd_7246004 := by exact prefixLift 7246004
  have htrace : WordTrace (prefixWord ++ tailWord_7246004) baseStart_7246004 baseEnd_7246004 := by
    simpa [prefixWord, tailWord_7246004, baseEnd_7246004] using wordTrace_append hprefix tailTrace_7246004
  have hstable : (prefixWord ++ tailWord_7246004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7246004).length < 2 ^ (prefixWord ++ tailWord_7246004).sum := by decide
  have hdescent : baseEnd_7246004 < baseStart_7246004 := by decide
  rcases family_descends (prefixWord ++ tailWord_7246004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7246009 : List Nat := [1, 2, 1, 4, 1, 2, 1, 3, 3, 1, 4]
def baseStart_7246009 : Nat := 118140960795 + 7246009 * 2 ^ 59
def prefixEnd_7246009 : Nat := 4983230072969 + 3 ^ 40 * 7246009 * 2
def baseEnd_7246009 : Nat := 3720685443804645690163717

theorem tailTrace_7246009 : CollatzResearch.WordTrace tailWord_7246009 prefixEnd_7246009 3720685443804645690163717 := by
  unfold tailWord_7246009
  simp only [CollatzResearch.WordTrace]
  refine ⟨264283660005954387658325081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176189106670636258438883387 264283660005954387658325081)
  ·
    refine ⟨198212745004465790743743811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 264283660005954387658325081 198212745004465790743743811)
    ·
      refine ⟨297319117506698686115615717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198212745004465790743743811 297319117506698686115615717)
      ·
        refine ⟨55747334532506003646677947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 297319117506698686115615717 55747334532506003646677947)
        ·
          refine ⟨83621001798759005470016921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55747334532506003646677947 83621001798759005470016921)
          ·
            refine ⟨62715751349069254102512691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83621001798759005470016921 62715751349069254102512691)
            ·
              refine ⟨94073627023603881153769037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62715751349069254102512691 94073627023603881153769037)
              ·
                refine ⟨35277610133851455432663389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 94073627023603881153769037 35277610133851455432663389)
                ·
                  refine ⟨13229103800194295787248771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35277610133851455432663389 13229103800194295787248771)
                  ·
                    refine ⟨19843655700291443680873157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13229103800194295787248771 19843655700291443680873157)
                    ·
                      refine ⟨3720685443804645690163717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19843655700291443680873157 3720685443804645690163717)
                      ·
                        rfl

theorem cell23_7246009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 3, 3, 1, 4].length) (baseStart_7246009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7246009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7246009 prefixEnd_7246009 := by exact prefixLift 7246009
  have htrace : WordTrace (prefixWord ++ tailWord_7246009) baseStart_7246009 baseEnd_7246009 := by
    simpa [prefixWord, tailWord_7246009, baseEnd_7246009] using wordTrace_append hprefix tailTrace_7246009
  have hstable : (prefixWord ++ tailWord_7246009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7246009).length < 2 ^ (prefixWord ++ tailWord_7246009).sum := by decide
  have hdescent : baseEnd_7246009 < baseStart_7246009 := by decide
  rcases family_descends (prefixWord ++ tailWord_7246009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7246020 : List Nat := [2, 3, 3, 1, 2, 1, 1, 5, 1, 1, 3]
def baseStart_7246020 : Nat := 118140960795 + 7246020 * 2 ^ 59
def prefixEnd_7246020 : Nat := 4983230072969 + 3 ^ 40 * 7246020 * 2
def baseEnd_7246020 : Nat := 3720691092091845147126167

theorem tailTrace_7246020 : CollatzResearch.WordTrace tailWord_7246020 prefixEnd_7246020 3720691092091845147126167 := by
  unfold tailWord_7246020
  simp only [CollatzResearch.WordTrace]
  refine ⟨132142030604457268268487757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176189374139276357691317009 132142030604457268268487757)
  ·
    refine ⟨49553261476671475600682909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132142030604457268268487757 49553261476671475600682909)
    ·
      refine ⟨18582473053751803350256091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49553261476671475600682909 18582473053751803350256091)
      ·
        refine ⟨27873709580627705025384137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18582473053751803350256091 27873709580627705025384137)
        ·
          refine ⟨20905282185470778769038103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27873709580627705025384137 20905282185470778769038103)
          ·
            refine ⟨31357923278206168153557155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20905282185470778769038103 31357923278206168153557155)
            ·
              refine ⟨47036884917309252230335733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31357923278206168153557155 47036884917309252230335733)
              ·
                refine ⟨4409707960997742396593975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 47036884917309252230335733 4409707960997742396593975)
                ·
                  refine ⟨6614561941496613594890963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4409707960997742396593975 6614561941496613594890963)
                  ·
                    refine ⟨9921842912244920392336445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6614561941496613594890963 9921842912244920392336445)
                    ·
                      refine ⟨3720691092091845147126167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9921842912244920392336445 3720691092091845147126167)
                      ·
                        rfl

theorem cell23_7246020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 1, 5, 1, 1, 3].length) (baseStart_7246020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7246020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7246020 prefixEnd_7246020 := by exact prefixLift 7246020
  have htrace : WordTrace (prefixWord ++ tailWord_7246020) baseStart_7246020 baseEnd_7246020 := by
    simpa [prefixWord, tailWord_7246020, baseEnd_7246020] using wordTrace_append hprefix tailTrace_7246020
  have hstable : (prefixWord ++ tailWord_7246020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7246020).length < 2 ^ (prefixWord ++ tailWord_7246020).sum := by decide
  have hdescent : baseEnd_7246020 < baseStart_7246020 := by decide
  rcases family_descends (prefixWord ++ tailWord_7246020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7246026 : List Nat := [3, 1, 2, 1, 3, 1, 3, 3, 1, 1, 4]
def baseStart_7246026 : Nat := 118140960795 + 7246026 * 2 ^ 59
def prefixEnd_7246026 : Nat := 4983230072969 + 3 ^ 40 * 7246026 * 2
def baseEnd_7246026 : Nat := 3720694172975772123651139

theorem tailTrace_7246026 : CollatzResearch.WordTrace tailWord_7246026 prefixEnd_7246026 3720694172975772123651139 := by
  unfold tailWord_7246026
  simp only [CollatzResearch.WordTrace]
  refine ⟨66071070011723199890423483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176189520031261866374462621 66071070011723199890423483)
  ·
    refine ⟨99106605017584799835635225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66071070011723199890423483 99106605017584799835635225)
    ·
      refine ⟨74329953763188599876726419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99106605017584799835635225 74329953763188599876726419)
      ·
        refine ⟨111494930644782899815089629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74329953763188599876726419 111494930644782899815089629)
        ·
          refine ⟨41810598991793587430658611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 111494930644782899815089629 41810598991793587430658611)
          ·
            refine ⟨62715898487690381145987917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41810598991793587430658611 62715898487690381145987917)
            ·
              refine ⟨23518461932883892929745469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62715898487690381145987917 23518461932883892929745469)
              ·
                refine ⟨8819423224831459848654551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23518461932883892929745469 8819423224831459848654551)
                ·
                  refine ⟨13229134837247189772981827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8819423224831459848654551 13229134837247189772981827)
                  ·
                    refine ⟨19843702255870784659472741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13229134837247189772981827 19843702255870784659472741)
                    ·
                      refine ⟨3720694172975772123651139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19843702255870784659472741 3720694172975772123651139)
                      ·
                        rfl

theorem cell23_7246026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 3, 3, 1, 1, 4].length) (baseStart_7246026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7246026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7246026 prefixEnd_7246026 := by exact prefixLift 7246026
  have htrace : WordTrace (prefixWord ++ tailWord_7246026) baseStart_7246026 baseEnd_7246026 := by
    simpa [prefixWord, tailWord_7246026, baseEnd_7246026] using wordTrace_append hprefix tailTrace_7246026
  have hstable : (prefixWord ++ tailWord_7246026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7246026).length < 2 ^ (prefixWord ++ tailWord_7246026).sum := by decide
  have hdescent : baseEnd_7246026 < baseStart_7246026 := by decide
  rcases family_descends (prefixWord ++ tailWord_7246026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7246056 : List Nat := [2, 1, 4, 1, 2, 2, 3, 1, 1, 2, 4]
def baseStart_7246056 : Nat := 118140960795 + 7246056 * 2 ^ 59
def prefixEnd_7246056 : Nat := 4983230072969 + 3 ^ 40 * 7246056 * 2
def baseEnd_7246056 : Nat := 3720709577395407006276001

theorem tailTrace_7246056 : CollatzResearch.WordTrace tailWord_7246056 prefixEnd_7246056 3720709577395407006276001 := by
  unfold tailWord_7246056
  simp only [CollatzResearch.WordTrace]
  refine ⟨132142687118392057342643011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176190249491189409790190681 132142687118392057342643011)
  ·
    refine ⟨198214030677588086013964517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132142687118392057342643011 198214030677588086013964517)
    ·
      refine ⟨37165130752047766127618347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 198214030677588086013964517 37165130752047766127618347)
      ·
        refine ⟨55747696128071649191427521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37165130752047766127618347 55747696128071649191427521)
        ·
          refine ⟨41810772096053736893570641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55747696128071649191427521 41810772096053736893570641)
          ·
            refine ⟨31358079072040302670177981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41810772096053736893570641 31358079072040302670177981)
            ·
              refine ⟨11759279652015113501316743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31358079072040302670177981 11759279652015113501316743)
              ·
                refine ⟨17638919478022670251975115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11759279652015113501316743 17638919478022670251975115)
                ·
                  refine ⟨26458379217034005377962673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17638919478022670251975115 26458379217034005377962673)
                  ·
                    refine ⟨19843784412775504033472005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26458379217034005377962673 19843784412775504033472005)
                    ·
                      refine ⟨3720709577395407006276001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19843784412775504033472005 3720709577395407006276001)
                      ·
                        rfl

theorem cell23_7246056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 3, 1, 1, 2, 4].length) (baseStart_7246056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7246056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7246056 prefixEnd_7246056 := by exact prefixLift 7246056
  have htrace : WordTrace (prefixWord ++ tailWord_7246056) baseStart_7246056 baseEnd_7246056 := by
    simpa [prefixWord, tailWord_7246056, baseEnd_7246056] using wordTrace_append hprefix tailTrace_7246056
  have hstable : (prefixWord ++ tailWord_7246056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7246056).length < 2 ^ (prefixWord ++ tailWord_7246056).sum := by decide
  have hdescent : baseEnd_7246056 < baseStart_7246056 := by decide
  rcases family_descends (prefixWord ++ tailWord_7246056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7246063 : List Nat := [1, 1, 2, 1, 6, 2, 2, 2, 1, 2, 3]
def baseStart_7246063 : Nat := 118140960795 + 7246063 * 2 ^ 59
def prefixEnd_7246063 : Nat := 4983230072969 + 3 ^ 40 * 7246063 * 2
def baseEnd_7246063 : Nat := 3720713171759988478888469

theorem tailTrace_7246063 : CollatzResearch.WordTrace tailWord_7246063 prefixEnd_7246063 3720713171759988478888469 := by
  unfold tailWord_7246063
  simp only [CollatzResearch.WordTrace]
  refine ⟨264285629547758754880790843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176190419698505836587193895 264285629547758754880790843)
  ·
    refine ⟨396428444321638132321186265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264285629547758754880790843 396428444321638132321186265)
    ·
      refine ⟨297321333241228599240889699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 396428444321638132321186265 297321333241228599240889699)
      ·
        refine ⟨445981999861842898861334549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 297321333241228599240889699 445981999861842898861334549)
        ·
          refine ⟨20905406243523885884125057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 445981999861842898861334549 20905406243523885884125057)
          ·
            refine ⟨15679054682642914413093793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20905406243523885884125057 15679054682642914413093793)
            ·
              refine ⟨11759291011982185809820345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15679054682642914413093793 11759291011982185809820345)
              ·
                refine ⟨8819468258986639357365259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11759291011982185809820345 8819468258986639357365259)
                ·
                  refine ⟨13229202388479959036047889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8819468258986639357365259 13229202388479959036047889)
                  ·
                    refine ⟨9921901791359969277035917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13229202388479959036047889 9921901791359969277035917)
                    ·
                      refine ⟨3720713171759988478888469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9921901791359969277035917 3720713171759988478888469)
                      ·
                        rfl

theorem cell23_7246063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 2, 2, 1, 2, 3].length) (baseStart_7246063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7246063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7246063 prefixEnd_7246063 := by exact prefixLift 7246063
  have htrace : WordTrace (prefixWord ++ tailWord_7246063) baseStart_7246063 baseEnd_7246063 := by
    simpa [prefixWord, tailWord_7246063, baseEnd_7246063] using wordTrace_append hprefix tailTrace_7246063
  have hstable : (prefixWord ++ tailWord_7246063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7246063).length < 2 ^ (prefixWord ++ tailWord_7246063).sum := by decide
  have hdescent : baseEnd_7246063 < baseStart_7246063 := by decide
  rcases family_descends (prefixWord ++ tailWord_7246063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7246066 : List Nat := [3, 2, 1, 3, 2, 1, 4, 7]
def baseStart_7246066 : Nat := 118140960795 + 7246066 * 2 ^ 59
def prefixEnd_7246066 : Nat := 4983230072969 + 3 ^ 40 * 7246066 * 2
def baseEnd_7246066 : Nat := 137804248600072295079665

theorem tailTrace_7246066 : CollatzResearch.WordTrace tailWord_7246066 prefixEnd_7246066 137804248600072295079665 := by
  unfold tailWord_7246066
  simp only [CollatzResearch.WordTrace]
  refine ⟨66071434741686971598287513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176190492644498590928766701 66071434741686971598287513)
  ·
    refine ⟨49553576056265228698715635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66071434741686971598287513 49553576056265228698715635)
    ·
      refine ⟨74330364084397843048073453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49553576056265228698715635 74330364084397843048073453)
      ·
        refine ⟨27873886531649191143027545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74330364084397843048073453 27873886531649191143027545)
        ·
          refine ⟨20905414898736893357270659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27873886531649191143027545 20905414898736893357270659)
          ·
            refine ⟨31358122348105340035905989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20905414898736893357270659 31358122348105340035905989)
            ·
              refine ⟨5879647940269751256732373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31358122348105340035905989 5879647940269751256732373)
              ·
                refine ⟨137804248600072295079665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5879647940269751256732373 137804248600072295079665)
                ·
                  rfl

theorem cell23_7246066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 4, 7].length) (baseStart_7246066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7246066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7246066 prefixEnd_7246066 := by exact prefixLift 7246066
  have htrace : WordTrace (prefixWord ++ tailWord_7246066) baseStart_7246066 baseEnd_7246066 := by
    simpa [prefixWord, tailWord_7246066, baseEnd_7246066] using wordTrace_append hprefix tailTrace_7246066
  have hstable : (prefixWord ++ tailWord_7246066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7246066).length < 2 ^ (prefixWord ++ tailWord_7246066).sum := by decide
  have hdescent : baseEnd_7246066 < baseStart_7246066 := by decide
  rcases family_descends (prefixWord ++ tailWord_7246066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7246120 : List Nat := [2, 1, 5, 1, 3, 1, 1, 1, 3, 3, 2]
def baseStart_7246120 : Nat := 118140960795 + 7246120 * 2 ^ 59
def prefixEnd_7246120 : Nat := 4983230072969 + 3 ^ 40 * 7246120 * 2
def baseEnd_7246120 : Nat := 3720742440157294755875707

theorem tailTrace_7246120 : CollatzResearch.WordTrace tailWord_7246120 prefixEnd_7246120 3720742440157294755875707 := by
  unfold tailWord_7246120
  simp only [CollatzResearch.WordTrace]
  refine ⟨132143854254276126807807907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176191805672368169077077209 132143854254276126807807907)
  ·
    refine ⟨198215781381414190211711861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132143854254276126807807907 198215781381414190211711861)
    ·
      refine ⟨18582729504507580332347987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 198215781381414190211711861 18582729504507580332347987)
      ·
        refine ⟨27874094256761370498521981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18582729504507580332347987 27874094256761370498521981)
        ·
          refine ⟨10452785346285513936945743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27874094256761370498521981 10452785346285513936945743)
          ·
            refine ⟨15679178019428270905418615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10452785346285513936945743 15679178019428270905418615)
            ·
              refine ⟨23518767029142406358127923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15679178019428270905418615 23518767029142406358127923)
              ·
                refine ⟨35278150543713609537191885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23518767029142406358127923 35278150543713609537191885)
                ·
                  refine ⟨13229306453892603576446957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35278150543713609537191885 13229306453892603576446957)
                  ·
                    refine ⟨4960989920209726341167609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13229306453892603576446957 4960989920209726341167609)
                    ·
                      refine ⟨3720742440157294755875707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4960989920209726341167609 3720742440157294755875707)
                      ·
                        rfl

theorem cell23_7246120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 1, 1, 3, 3, 2].length) (baseStart_7246120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7246120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7246120 prefixEnd_7246120 := by exact prefixLift 7246120
  have htrace : WordTrace (prefixWord ++ tailWord_7246120) baseStart_7246120 baseEnd_7246120 := by
    simpa [prefixWord, tailWord_7246120, baseEnd_7246120] using wordTrace_append hprefix tailTrace_7246120
  have hstable : (prefixWord ++ tailWord_7246120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7246120).length < 2 ^ (prefixWord ++ tailWord_7246120).sum := by decide
  have hdescent : baseEnd_7246120 < baseStart_7246120 := by decide
  rcases family_descends (prefixWord ++ tailWord_7246120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7246133 : List Nat := [1, 3, 3, 1, 2, 1, 3, 2, 1, 4, 2]
def baseStart_7246133 : Nat := 118140960795 + 7246133 * 2 ^ 59
def prefixEnd_7246133 : Nat := 4983230072969 + 3 ^ 40 * 7246133 * 2
def baseEnd_7246133 : Nat := 3720749115405803205013147

theorem tailTrace_7246133 : CollatzResearch.WordTrace tailWord_7246133 prefixEnd_7246133 3720749115405803205013147 := by
  unfold tailWord_7246133
  simp only [CollatzResearch.WordTrace]
  refine ⟨264288182657505156835839053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176192121771670104557226035 264288182657505156835839053)
  ·
    refine ⟨99108068496564433813439645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 264288182657505156835839053 99108068496564433813439645)
    ·
      refine ⟨37165525686211662680039867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99108068496564433813439645 37165525686211662680039867)
      ·
        refine ⟨55748288529317494020059801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37165525686211662680039867 55748288529317494020059801)
        ·
          refine ⟨41811216396988120515044851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55748288529317494020059801 41811216396988120515044851)
          ·
            refine ⟨62716824595482180772567277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41811216396988120515044851 62716824595482180772567277)
            ·
              refine ⟨23518809223305817789712729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62716824595482180772567277 23518809223305817789712729)
              ·
                refine ⟨17639106917479363342284547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23518809223305817789712729 17639106917479363342284547)
                ·
                  refine ⟨26458660376219045013426821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17639106917479363342284547 26458660376219045013426821)
                  ·
                    refine ⟨4960998820541070940017529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26458660376219045013426821 4960998820541070940017529)
                    ·
                      refine ⟨3720749115405803205013147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4960998820541070940017529 3720749115405803205013147)
                      ·
                        rfl

theorem cell23_7246133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 3, 2, 1, 4, 2].length) (baseStart_7246133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7246133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7246133 prefixEnd_7246133 := by exact prefixLift 7246133
  have htrace : WordTrace (prefixWord ++ tailWord_7246133) baseStart_7246133 baseEnd_7246133 := by
    simpa [prefixWord, tailWord_7246133, baseEnd_7246133] using wordTrace_append hprefix tailTrace_7246133
  have hstable : (prefixWord ++ tailWord_7246133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7246133).length < 2 ^ (prefixWord ++ tailWord_7246133).sum := by decide
  have hdescent : baseEnd_7246133 < baseStart_7246133 := by decide
  rcases family_descends (prefixWord ++ tailWord_7246133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7246137 : List Nat := [1, 2, 1, 6, 1, 2, 3, 1, 1, 3, 2]
def baseStart_7246137 : Nat := 118140960795 + 7246137 * 2 ^ 59
def prefixEnd_7246137 : Nat := 4983230072969 + 3 ^ 40 * 7246137 * 2
def baseEnd_7246137 : Nat := 3720751169328421189363129

theorem tailTrace_7246137 : CollatzResearch.WordTrace tailWord_7246137 prefixEnd_7246137 3720751169328421189363129 := by
  unfold tailWord_7246137
  simp only [CollatzResearch.WordTrace]
  refine ⟨264288328549490665518984665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176192219032993777012656443 264288328549490665518984665)
  ·
    refine ⟨198216246412117999139238499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 264288328549490665518984665 198216246412117999139238499)
    ·
      refine ⟨297324369618176998708857749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198216246412117999139238499 297324369618176998708857749)
      ·
        refine ⟨13937079825852046814477707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 297324369618176998708857749 13937079825852046814477707)
        ·
          refine ⟨20905619738778070221716561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13937079825852046814477707 20905619738778070221716561)
          ·
            refine ⟨15679214804083552666287421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20905619738778070221716561 15679214804083552666287421)
            ·
              refine ⟨5879705551531332249857783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15679214804083552666287421 5879705551531332249857783)
              ·
                refine ⟨8819558327296998374786675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5879705551531332249857783 8819558327296998374786675)
                ·
                  refine ⟨13229337490945497562180013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8819558327296998374786675 13229337490945497562180013)
                  ·
                    refine ⟨4961001559104561585817505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13229337490945497562180013 4961001559104561585817505)
                    ·
                      refine ⟨3720751169328421189363129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4961001559104561585817505 3720751169328421189363129)
                      ·
                        rfl

theorem cell23_7246137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 3, 1, 1, 3, 2].length) (baseStart_7246137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7246137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7246137 prefixEnd_7246137 := by exact prefixLift 7246137
  have htrace : WordTrace (prefixWord ++ tailWord_7246137) baseStart_7246137 baseEnd_7246137 := by
    simpa [prefixWord, tailWord_7246137, baseEnd_7246137] using wordTrace_append hprefix tailTrace_7246137
  have hstable : (prefixWord ++ tailWord_7246137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7246137).length < 2 ^ (prefixWord ++ tailWord_7246137).sum := by decide
  have hdescent : baseEnd_7246137 < baseStart_7246137 := by decide
  rcases family_descends (prefixWord ++ tailWord_7246137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7246169 : List Nat := [1, 2, 1, 2, 2, 2, 1, 4, 1, 7]
def baseStart_7246169 : Nat := 118140960795 + 7246169 * 2 ^ 59
def prefixEnd_7246169 : Nat := 4983230072969 + 3 ^ 40 * 7246169 * 2
def baseEnd_7246169 : Nat := 1240255866903121688054327

theorem tailTrace_7246169 : CollatzResearch.WordTrace tailWord_7246169 prefixEnd_7246169 1240255866903121688054327 := by
  unfold tailWord_7246169
  simp only [CollatzResearch.WordTrace]
  refine ⟨264289495685374734984149561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176192997123583156656099707 264289495685374734984149561)
  ·
    refine ⟨198217121764031051238112171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 264289495685374734984149561 198217121764031051238112171)
    ·
      refine ⟨297325682646046576857168257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198217121764031051238112171 297325682646046576857168257)
      ·
        refine ⟨222994261984534932642876193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 297325682646046576857168257 222994261984534932642876193)
        ·
          refine ⟨167245696488401199482157145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 222994261984534932642876193 167245696488401199482157145)
          ·
            refine ⟨125434272366300899611617859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 167245696488401199482157145 125434272366300899611617859)
            ·
              refine ⟨188151408549451349417426789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125434272366300899611617859 188151408549451349417426789)
              ·
                refine ⟨35278389103022128015767523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 188151408549451349417426789 35278389103022128015767523)
                ·
                  refine ⟨52917583654533192023651285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35278389103022128015767523 52917583654533192023651285)
                  ·
                    refine ⟨1240255866903121688054327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 52917583654533192023651285 1240255866903121688054327)
                    ·
                      rfl

theorem cell23_7246169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 4, 1, 7].length) (baseStart_7246169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7246169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7246169 prefixEnd_7246169 := by exact prefixLift 7246169
  have htrace : WordTrace (prefixWord ++ tailWord_7246169) baseStart_7246169 baseEnd_7246169 := by
    simpa [prefixWord, tailWord_7246169, baseEnd_7246169] using wordTrace_append hprefix tailTrace_7246169
  have hstable : (prefixWord ++ tailWord_7246169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7246169).length < 2 ^ (prefixWord ++ tailWord_7246169).sum := by decide
  have hdescent : baseEnd_7246169 < baseStart_7246169 := by decide
  rcases family_descends (prefixWord ++ tailWord_7246169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7246280 : List Nat := [2, 1, 3, 1, 3, 4, 2, 1, 6]
def baseStart_7246280 : Nat := 118140960795 + 7246280 * 2 ^ 59
def prefixEnd_7246280 : Nat := 4983230072969 + 3 ^ 40 * 7246280 * 2
def baseEnd_7246280 : Nat := 413424955229112681097219

theorem tailTrace_7246280 : CollatzResearch.WordTrace tailWord_7246280 prefixEnd_7246280 413424955229112681097219 := by
  unfold tailWord_7246280
  simp only [CollatzResearch.WordTrace]
  refine ⟨132146772093986300470720147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176195696125315067294293529 132146772093986300470720147)
  ·
    refine ⟨198220158140979450706080221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132146772093986300470720147 198220158140979450706080221)
    ·
      refine ⟨74332559302867294014780083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 198220158140979450706080221 74332559302867294014780083)
      ·
        refine ⟨111498838954300941022170125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74332559302867294014780083 111498838954300941022170125)
        ·
          refine ⟨41812064607862852883313797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 111498838954300941022170125 41812064607862852883313797)
          ·
            refine ⟨7839762113974284915621337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41812064607862852883313797 7839762113974284915621337)
            ·
              refine ⟨5879821585480713686716003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7839762113974284915621337 5879821585480713686716003)
              ·
                refine ⟨8819732378221070530074005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5879821585480713686716003 8819732378221070530074005)
                ·
                  refine ⟨413424955229112681097219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8819732378221070530074005 413424955229112681097219)
                  ·
                    rfl

theorem cell23_7246280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 4, 2, 1, 6].length) (baseStart_7246280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7246280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7246280 prefixEnd_7246280 := by exact prefixLift 7246280
  have htrace : WordTrace (prefixWord ++ tailWord_7246280) baseStart_7246280 baseEnd_7246280 := by
    simpa [prefixWord, tailWord_7246280, baseEnd_7246280] using wordTrace_append hprefix tailTrace_7246280
  have hstable : (prefixWord ++ tailWord_7246280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7246280).length < 2 ^ (prefixWord ++ tailWord_7246280).sum := by decide
  have hdescent : baseEnd_7246280 < baseStart_7246280 := by decide
  rcases family_descends (prefixWord ++ tailWord_7246280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7246283 : List Nat := [1, 1, 1, 1, 3, 3, 1, 1, 6, 3, 2]
def baseStart_7246283 : Nat := 118140960795 + 7246283 * 2 ^ 59
def prefixEnd_7246283 : Nat := 4983230072969 + 3 ^ 40 * 7246283 * 2
def baseEnd_7246283 : Nat := 3720826137503977618137457

theorem tailTrace_7246283 : CollatzResearch.WordTrace tailWord_7246283 prefixEnd_7246283 3720826137503977618137457 := by
  unfold tailWord_7246283
  simp only [CollatzResearch.WordTrace]
  refine ⟨264293653606961732453799503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176195769071307821635866335 264293653606961732453799503)
  ·
    refine ⟨396440480410442598680699255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264293653606961732453799503 396440480410442598680699255)
    ·
      refine ⟨594660720615663898021048883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 396440480410442598680699255 594660720615663898021048883)
      ·
        refine ⟨891991080923495847031573325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 594660720615663898021048883 891991080923495847031573325)
        ·
          refine ⟨334496655346310942636839997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 891991080923495847031573325 334496655346310942636839997)
          ·
            refine ⟨125436245754866603488814999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 334496655346310942636839997 125436245754866603488814999)
            ·
              refine ⟨188154368632299905233222499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125436245754866603488814999 188154368632299905233222499)
              ·
                refine ⟨282231552948449857849833749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 188154368632299905233222499 282231552948449857849833749)
                ·
                  refine ⟨13229604044458587086710957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 282231552948449857849833749 13229604044458587086710957)
                  ·
                    refine ⟨4961101516671970157516609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13229604044458587086710957 4961101516671970157516609)
                    ·
                      refine ⟨3720826137503977618137457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4961101516671970157516609 3720826137503977618137457)
                      ·
                        rfl

theorem cell23_7246283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 1, 6, 3, 2].length) (baseStart_7246283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7246283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7246283 prefixEnd_7246283 := by exact prefixLift 7246283
  have htrace : WordTrace (prefixWord ++ tailWord_7246283) baseStart_7246283 baseEnd_7246283 := by
    simpa [prefixWord, tailWord_7246283, baseEnd_7246283] using wordTrace_append hprefix tailTrace_7246283
  have hstable : (prefixWord ++ tailWord_7246283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7246283).length < 2 ^ (prefixWord ++ tailWord_7246283).sum := by decide
  have hdescent : baseEnd_7246283 < baseStart_7246283 := by decide
  rcases family_descends (prefixWord ++ tailWord_7246283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7246293 : List Nat := [1, 3, 2, 3, 1, 3, 1, 1, 3, 5]
def baseStart_7246293 : Nat := 118140960795 + 7246293 * 2 ^ 59
def prefixEnd_7246293 : Nat := 4983230072969 + 3 ^ 40 * 7246293 * 2
def baseEnd_7246293 : Nat := 1240277090770174193004137

theorem tailTrace_7246293 : CollatzResearch.WordTrace tailWord_7246293 prefixEnd_7246293 1240277090770174193004137 := by
  unfold tailWord_7246293
  simp only [CollatzResearch.WordTrace]
  refine ⟨264294018336925504161663533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176196012224617002774442355 264294018336925504161663533)
  ·
    refine ⟨99110256876347064060623825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 264294018336925504161663533 99110256876347064060623825)
    ·
      refine ⟨74332692657260298045467869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99110256876347064060623825 74332692657260298045467869)
      ·
        refine ⟨27874759746472611767050451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74332692657260298045467869 27874759746472611767050451)
        ·
          refine ⟨41812139619708917650575677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27874759746472611767050451 41812139619708917650575677)
          ·
            refine ⟨15679552357390844118965879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41812139619708917650575677 15679552357390844118965879)
            ·
              refine ⟨23519328536086266178448819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15679552357390844118965879 23519328536086266178448819)
              ·
                refine ⟨35278992804129399267673229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23519328536086266178448819 35278992804129399267673229)
                ·
                  refine ⟨13229622301548524725377461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35278992804129399267673229 13229622301548524725377461)
                  ·
                    refine ⟨1240277090770174193004137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13229622301548524725377461 1240277090770174193004137)
                    ·
                      rfl

theorem cell23_7246293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 1, 1, 3, 5].length) (baseStart_7246293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7246293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7246293 prefixEnd_7246293 := by exact prefixLift 7246293
  have htrace : WordTrace (prefixWord ++ tailWord_7246293) baseStart_7246293 baseEnd_7246293 := by
    simpa [prefixWord, tailWord_7246293, baseEnd_7246293] using wordTrace_append hprefix tailTrace_7246293
  have hstable : (prefixWord ++ tailWord_7246293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7246293).length < 2 ^ (prefixWord ++ tailWord_7246293).sum := by decide
  have hdescent : baseEnd_7246293 < baseStart_7246293 := by decide
  rcases family_descends (prefixWord ++ tailWord_7246293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7246317 : List Nat := [1, 5, 1, 3, 1, 1, 2, 2, 2, 3, 2]
def baseStart_7246317 : Nat := 118140960795 + 7246317 * 2 ^ 59
def prefixEnd_7246317 : Nat := 4983230072969 + 3 ^ 40 * 7246317 * 2
def baseEnd_7246317 : Nat := 3720843595846230485112301

theorem tailTrace_7246317 : CollatzResearch.WordTrace tailWord_7246317 prefixEnd_7246317 3720843595846230485112301 := by
  unfold tailWord_7246317
  simp only [CollatzResearch.WordTrace]
  refine ⟨264294893688838556260537205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176196595792559037507024803 264294893688838556260537205)
  ·
    refine ⟨24777646283328614649425363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 264294893688838556260537205 24777646283328614649425363)
    ·
      refine ⟨37166469424992921974138045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24777646283328614649425363 37166469424992921974138045)
      ·
        refine ⟨13937426034372345740301767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37166469424992921974138045 13937426034372345740301767)
        ·
          refine ⟨20906139051558518610452651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13937426034372345740301767 20906139051558518610452651)
          ·
            refine ⟨31359208577337777915678977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20906139051558518610452651 31359208577337777915678977)
            ·
              refine ⟨23519406433003333436759233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31359208577337777915678977 23519406433003333436759233)
              ·
                refine ⟨17639554824752500077569425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23519406433003333436759233 17639554824752500077569425)
                ·
                  refine ⟨13229666118564375058177069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17639554824752500077569425 13229666118564375058177069)
                  ·
                    refine ⟨4961124794461640646816401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13229666118564375058177069 4961124794461640646816401)
                    ·
                      refine ⟨3720843595846230485112301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4961124794461640646816401 3720843595846230485112301)
                      ·
                        rfl

theorem cell23_7246317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 2, 2, 2, 3, 2].length) (baseStart_7246317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7246317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7246317 prefixEnd_7246317 := by exact prefixLift 7246317
  have htrace : WordTrace (prefixWord ++ tailWord_7246317) baseStart_7246317 baseEnd_7246317 := by
    simpa [prefixWord, tailWord_7246317, baseEnd_7246317] using wordTrace_append hprefix tailTrace_7246317
  have hstable : (prefixWord ++ tailWord_7246317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7246317).length < 2 ^ (prefixWord ++ tailWord_7246317).sum := by decide
  have hdescent : baseEnd_7246317 < baseStart_7246317 := by decide
  rcases family_descends (prefixWord ++ tailWord_7246317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7246333 : List Nat := [1, 4, 1, 1, 1, 3, 1, 1, 5, 2, 3]
def baseStart_7246333 : Nat := 118140960795 + 7246333 * 2 ^ 59
def prefixEnd_7246333 : Nat := 4983230072969 + 3 ^ 40 * 7246333 * 2
def baseEnd_7246333 : Nat := 3720851811536702422512227

theorem tailTrace_7246333 : CollatzResearch.WordTrace tailWord_7246333 prefixEnd_7246333 3720851811536702422512227 := by
  unfold tailWord_7246333
  simp only [CollatzResearch.WordTrace]
  refine ⟨264295477256780590993119653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176196984837853727328746435 264295477256780590993119653)
  ·
    refine ⟨49555401985646360811209935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 264295477256780590993119653 49555401985646360811209935)
    ·
      refine ⟨74333102978469541216814903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49555401985646360811209935 74333102978469541216814903)
      ·
        refine ⟨111499654467704311825222355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74333102978469541216814903 111499654467704311825222355)
        ·
          refine ⟨167249481701556467737833533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111499654467704311825222355 167249481701556467737833533)
          ·
            refine ⟨62718555638083675401687575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 167249481701556467737833533 62718555638083675401687575)
            ·
              refine ⟨94077833457125513102531363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62718555638083675401687575 94077833457125513102531363)
              ·
                refine ⟨141116750185688269653797045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94077833457125513102531363 141116750185688269653797045)
                ·
                  refine ⟨13229695329908275280043473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 141116750185688269653797045 13229695329908275280043473)
                  ·
                    refine ⟨9922271497431206460032605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13229695329908275280043473 9922271497431206460032605)
                    ·
                      refine ⟨3720851811536702422512227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9922271497431206460032605 3720851811536702422512227)
                      ·
                        rfl

theorem cell23_7246333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 1, 5, 2, 3].length) (baseStart_7246333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7246333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7246333 prefixEnd_7246333 := by exact prefixLift 7246333
  have htrace : WordTrace (prefixWord ++ tailWord_7246333) baseStart_7246333 baseEnd_7246333 := by
    simpa [prefixWord, tailWord_7246333, baseEnd_7246333] using wordTrace_append hprefix tailTrace_7246333
  have hstable : (prefixWord ++ tailWord_7246333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7246333).length < 2 ^ (prefixWord ++ tailWord_7246333).sum := by decide
  have hdescent : baseEnd_7246333 < baseStart_7246333 := by decide
  rcases family_descends (prefixWord ++ tailWord_7246333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7246340 : List Nat := [2, 3, 2, 3, 1, 2, 2, 1, 1, 6]
def baseStart_7246340 : Nat := 118140960795 + 7246340 * 2 ^ 59
def prefixEnd_7246340 : Nat := 4983230072969 + 3 ^ 40 * 7246340 * 2
def baseEnd_7246340 : Nat := 1240285135300427965041565

theorem tailTrace_7246340 : CollatzResearch.WordTrace tailWord_7246340 prefixEnd_7246340 1240285135300427965041565 := by
  unfold tailWord_7246340
  simp only [CollatzResearch.WordTrace]
  refine ⟨132147866283877615594312237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176197155045170154125749649 132147866283877615594312237)
  ·
    refine ⟨49555449856454105847867089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132147866283877615594312237 49555449856454105847867089)
    ·
      refine ⟨37166587392340579385900317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49555449856454105847867089 37166587392340579385900317)
      ·
        refine ⟨13937470272127717269712619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37166587392340579385900317 13937470272127717269712619)
        ·
          refine ⟨20906205408191575904568929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13937470272127717269712619 20906205408191575904568929)
          ·
            refine ⟨15679654056143681928426697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20906205408191575904568929 15679654056143681928426697)
            ·
              refine ⟨11759740542107761446320023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15679654056143681928426697 11759740542107761446320023)
              ·
                refine ⟨17639610813161642169480035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11759740542107761446320023 17639610813161642169480035)
                ·
                  refine ⟨26459416219742463254220053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17639610813161642169480035 26459416219742463254220053)
                  ·
                    refine ⟨1240285135300427965041565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26459416219742463254220053 1240285135300427965041565)
                    ·
                      rfl

theorem cell23_7246340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 2, 1, 1, 6].length) (baseStart_7246340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7246340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7246340 prefixEnd_7246340 := by exact prefixLift 7246340
  have htrace : WordTrace (prefixWord ++ tailWord_7246340) baseStart_7246340 baseEnd_7246340 := by
    simpa [prefixWord, tailWord_7246340, baseEnd_7246340] using wordTrace_append hprefix tailTrace_7246340
  have hstable : (prefixWord ++ tailWord_7246340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7246340).length < 2 ^ (prefixWord ++ tailWord_7246340).sum := by decide
  have hdescent : baseEnd_7246340 < baseStart_7246340 := by decide
  rcases family_descends (prefixWord ++ tailWord_7246340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7246347 : List Nat := [1, 1, 1, 1, 7, 2, 1, 2, 3, 2, 2]
def baseStart_7246347 : Nat := 118140960795 + 7246347 * 2 ^ 59
def prefixEnd_7246347 : Nat := 4983230072969 + 3 ^ 40 * 7246347 * 2
def baseEnd_7246347 : Nat := 3720859000265865367737163

theorem tailTrace_7246347 : CollatzResearch.WordTrace tailWord_7246347 prefixEnd_7246347 3720859000265865367737163 := by
  unfold tailWord_7246347
  simp only [CollatzResearch.WordTrace]
  refine ⟨264295987878729871384129295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176197325252486580922752863 264295987878729871384129295)
  ·
    refine ⟨396443981818094807076193943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264295987878729871384129295 396443981818094807076193943)
    ·
      refine ⟨594665972727142210614290915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 396443981818094807076193943 594665972727142210614290915)
      ·
        refine ⟨891998959090713315921436373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 594665972727142210614290915 891998959090713315921436373)
        ·
          refine ⟨20906225603688593341908665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 891998959090713315921436373 20906225603688593341908665)
          ·
            refine ⟨15679669202766445006431499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20906225603688593341908665 15679669202766445006431499)
            ·
              refine ⟨23519503804149667509647249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15679669202766445006431499 23519503804149667509647249)
              ·
                refine ⟨17639627853112250632235437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23519503804149667509647249 17639627853112250632235437)
                ·
                  refine ⟨6614860444917093987088289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17639627853112250632235437 6614860444917093987088289)
                  ·
                    refine ⟨4961145333687820490316217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6614860444917093987088289 4961145333687820490316217)
                    ·
                      refine ⟨3720859000265865367737163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4961145333687820490316217 3720859000265865367737163)
                      ·
                        rfl

theorem cell23_7246347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 1, 2, 3, 2, 2].length) (baseStart_7246347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7246347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7246347 prefixEnd_7246347 := by exact prefixLift 7246347
  have htrace : WordTrace (prefixWord ++ tailWord_7246347) baseStart_7246347 baseEnd_7246347 := by
    simpa [prefixWord, tailWord_7246347, baseEnd_7246347] using wordTrace_append hprefix tailTrace_7246347
  have hstable : (prefixWord ++ tailWord_7246347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7246347).length < 2 ^ (prefixWord ++ tailWord_7246347).sum := by decide
  have hdescent : baseEnd_7246347 < baseStart_7246347 := by decide
  rcases family_descends (prefixWord ++ tailWord_7246347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7246350 : List Nat := [4, 1, 1, 2, 3, 1, 2, 1, 3, 2, 3]
def baseStart_7246350 : Nat := 118140960795 + 7246350 * 2 ^ 59
def prefixEnd_7246350 : Nat := 4983230072969 + 3 ^ 40 * 7246350 * 2
def baseEnd_7246350 : Nat := 3720860540707828855999649

theorem tailTrace_7246350 : CollatzResearch.WordTrace tailWord_7246350 prefixEnd_7246350 3720860540707828855999649 := by
  unfold tailWord_7246350
  simp only [CollatzResearch.WordTrace]
  refine ⟨33037012162214875362061063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 176197398198479335264325669 33037012162214875362061063)
  ·
    refine ⟨49555518243322313043091595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33037012162214875362061063 49555518243322313043091595)
    ·
      refine ⟨74333277364983469564637393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49555518243322313043091595 74333277364983469564637393)
      ·
        refine ⟨55749958023737602173478045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74333277364983469564637393 55749958023737602173478045)
        ·
          refine ⟨20906234258901600815054267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55749958023737602173478045 20906234258901600815054267)
          ·
            refine ⟨31359351388352401222581401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20906234258901600815054267 31359351388352401222581401)
            ·
              refine ⟨23519513541264300916936051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31359351388352401222581401 23519513541264300916936051)
              ·
                refine ⟨35279270311896451375404077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23519513541264300916936051 35279270311896451375404077)
                ·
                  refine ⟨13229726366961169265776529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35279270311896451375404077 13229726366961169265776529)
                  ·
                    refine ⟨9922294775220876949332397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13229726366961169265776529 9922294775220876949332397)
                    ·
                      refine ⟨3720860540707828855999649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9922294775220876949332397 3720860540707828855999649)
                      ·
                        rfl

theorem cell23_7246350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 2, 1, 3, 2, 3].length) (baseStart_7246350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7246350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7246350 prefixEnd_7246350 := by exact prefixLift 7246350
  have htrace : WordTrace (prefixWord ++ tailWord_7246350) baseStart_7246350 baseEnd_7246350 := by
    simpa [prefixWord, tailWord_7246350, baseEnd_7246350] using wordTrace_append hprefix tailTrace_7246350
  have hstable : (prefixWord ++ tailWord_7246350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7246350).length < 2 ^ (prefixWord ++ tailWord_7246350).sum := by decide
  have hdescent : baseEnd_7246350 < baseStart_7246350 := by decide
  rcases family_descends (prefixWord ++ tailWord_7246350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7246364 : List Nat := [2, 2, 3, 1, 2, 2, 1, 5, 1, 2, 2]
def baseStart_7246364 : Nat := 118140960795 + 7246364 * 2 ^ 59
def prefixEnd_7246364 : Nat := 4983230072969 + 3 ^ 40 * 7246364 * 2
def baseEnd_7246364 : Nat := 3720867729436991801224585

theorem tailTrace_7246364 : CollatzResearch.WordTrace tailWord_7246364 prefixEnd_7246364 3720867729436991801224585 := by
  unfold tailWord_7246364
  simp only [CollatzResearch.WordTrace]
  refine ⟨132148303959834141643749073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176197738613112188858332097 132148303959834141643749073)
  ·
    refine ⟨99111227969875606232811805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132148303959834141643749073 99111227969875606232811805)
    ·
      refine ⟨37166710488703352337304427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99111227969875606232811805 37166710488703352337304427)
      ·
        refine ⟨55750065733055028505956641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37166710488703352337304427 55750065733055028505956641)
        ·
          refine ⟨41812549299791271379467481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55750065733055028505956641 41812549299791271379467481)
          ·
            refine ⟨31359411974843453534600611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41812549299791271379467481 31359411974843453534600611)
            ·
              refine ⟨47039117962265180301900917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31359411974843453534600611 47039117962265180301900917)
              ·
                refine ⟨4409917308962360653303211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 47039117962265180301900917 4409917308962360653303211)
                ·
                  refine ⟨6614875963443540979954817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4409917308962360653303211 6614875963443540979954817)
                  ·
                    refine ⟨4961156972582655734966113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6614875963443540979954817 4961156972582655734966113)
                    ·
                      refine ⟨3720867729436991801224585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4961156972582655734966113 3720867729436991801224585)
                      ·
                        rfl

theorem cell23_7246364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 1, 5, 1, 2, 2].length) (baseStart_7246364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7246364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7246364 prefixEnd_7246364 := by exact prefixLift 7246364
  have htrace : WordTrace (prefixWord ++ tailWord_7246364) baseStart_7246364 baseEnd_7246364 := by
    simpa [prefixWord, tailWord_7246364, baseEnd_7246364] using wordTrace_append hprefix tailTrace_7246364
  have hstable : (prefixWord ++ tailWord_7246364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7246364).length < 2 ^ (prefixWord ++ tailWord_7246364).sum := by decide
  have hdescent : baseEnd_7246364 < baseStart_7246364 := by decide
  rcases family_descends (prefixWord ++ tailWord_7246364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7246397 : List Nat := [1, 4, 1, 3, 2, 3, 1, 1, 1, 3, 3]
def baseStart_7246397 : Nat := 118140960795 + 7246397 * 2 ^ 59
def prefixEnd_7246397 : Nat := 4983230072969 + 3 ^ 40 * 7246397 * 2
def baseEnd_7246397 : Nat := 3720884674298590172111933

theorem tailTrace_7246397 : CollatzResearch.WordTrace tailWord_7246397 prefixEnd_7246397 3720884674298590172111933 := by
  unfold tailWord_7246397
  simp only [CollatzResearch.WordTrace]
  refine ⟨264297811528548729923449445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176198541019032486615632963 264297811528548729923449445)
  ·
    refine ⟨49555839661602886860646771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 264297811528548729923449445 49555839661602886860646771)
    ·
      refine ⟨74333759492404330290970157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49555839661602886860646771 74333759492404330290970157)
      ·
        refine ⟨27875159809651623859113809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74333759492404330290970157 27875159809651623859113809)
        ·
          refine ⟨20906369857238717894335357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27875159809651623859113809 20906369857238717894335357)
          ·
            refine ⟨7839888696464519210375759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20906369857238717894335357 7839888696464519210375759)
            ·
              refine ⟨11759833044696778815563639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7839888696464519210375759 11759833044696778815563639)
              ·
                refine ⟨17639749567045168223345459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11759833044696778815563639 17639749567045168223345459)
                ·
                  refine ⟨26459624350567752335018189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17639749567045168223345459 26459624350567752335018189)
                  ·
                    refine ⟨9922359131462907125631821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26459624350567752335018189 9922359131462907125631821)
                    ·
                      refine ⟨3720884674298590172111933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9922359131462907125631821 3720884674298590172111933)
                      ·
                        rfl

theorem cell23_7246397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 3, 1, 1, 1, 3, 3].length) (baseStart_7246397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7246397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7246397 prefixEnd_7246397 := by exact prefixLift 7246397
  have htrace : WordTrace (prefixWord ++ tailWord_7246397) baseStart_7246397 baseEnd_7246397 := by
    simpa [prefixWord, tailWord_7246397, baseEnd_7246397] using wordTrace_append hprefix tailTrace_7246397
  have hstable : (prefixWord ++ tailWord_7246397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7246397).length < 2 ^ (prefixWord ++ tailWord_7246397).sum := by decide
  have hdescent : baseEnd_7246397 < baseStart_7246397 := by decide
  rcases family_descends (prefixWord ++ tailWord_7246397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7246407 : List Nat := [1, 1, 4, 1, 4, 1, 1, 4, 1, 3, 2]
def baseStart_7246407 : Nat := 118140960795 + 7246407 * 2 ^ 59
def prefixEnd_7246407 : Nat := 4983230072969 + 3 ^ 40 * 7246407 * 2
def baseEnd_7246407 : Nat := 3720889809105135132986887

theorem tailTrace_7246407 : CollatzResearch.WordTrace tailWord_7246407 prefixEnd_7246407 3720889809105135132986887 := by
  unfold tailWord_7246407
  simp only [CollatzResearch.WordTrace]
  refine ⟨264298176258512501631313475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176198784172341667754208983 264298176258512501631313475)
  ·
    refine ⟨396447264387768752446970213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264298176258512501631313475 396447264387768752446970213)
    ·
      refine ⟨74333862072706641083806915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 396447264387768752446970213 74333862072706641083806915)
      ·
        refine ⟨111500793109059961625710373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74333862072706641083806915 111500793109059961625710373)
        ·
          refine ⟨20906398707948742804820695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 111500793109059961625710373 20906398707948742804820695)
          ·
            refine ⟨31359598061923114207231043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20906398707948742804820695 31359598061923114207231043)
            ·
              refine ⟨47039397092884671310846565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31359598061923114207231043 47039397092884671310846565)
              ·
                refine ⟨8819886954915875870783731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47039397092884671310846565 8819886954915875870783731)
                ·
                  refine ⟨13229830432373813806175597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8819886954915875870783731 13229830432373813806175597)
                  ·
                    refine ⟨4961186412140180177315849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13229830432373813806175597 4961186412140180177315849)
                    ·
                      refine ⟨3720889809105135132986887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4961186412140180177315849 3720889809105135132986887)
                      ·
                        rfl

theorem cell23_7246407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 1, 4, 1, 3, 2].length) (baseStart_7246407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7246407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7246407 prefixEnd_7246407 := by exact prefixLift 7246407
  have htrace : WordTrace (prefixWord ++ tailWord_7246407) baseStart_7246407 baseEnd_7246407 := by
    simpa [prefixWord, tailWord_7246407, baseEnd_7246407] using wordTrace_append hprefix tailTrace_7246407
  have hstable : (prefixWord ++ tailWord_7246407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7246407).length < 2 ^ (prefixWord ++ tailWord_7246407).sum := by decide
  have hdescent : baseEnd_7246407 < baseStart_7246407 := by decide
  rcases family_descends (prefixWord ++ tailWord_7246407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7246423 : List Nat := [1, 1, 3, 2, 2, 2, 3, 1, 2, 1, 5]
def baseStart_7246423 : Nat := 118140960795 + 7246423 * 2 ^ 59
def prefixEnd_7246423 : Nat := 4983230072969 + 3 ^ 40 * 7246423 * 2
def baseEnd_7246423 : Nat := 3720898024795607070386813

theorem tailTrace_7246423 : CollatzResearch.WordTrace tailWord_7246423 prefixEnd_7246423 3720898024795607070386813 := by
  unfold tailWord_7246423
  simp only [CollatzResearch.WordTrace]
  refine ⟨264298759826454536363895923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176199173217636357575930615 264298759826454536363895923)
  ·
    refine ⟨396448139739681804545843885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264298759826454536363895923 396448139739681804545843885)
    ·
      refine ⟨148668052402380676704691457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 396448139739681804545843885 148668052402380676704691457)
      ·
        refine ⟨111501039301785507528518593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148668052402380676704691457 111501039301785507528518593)
        ·
          refine ⟨83625779476339130646388945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111501039301785507528518593 83625779476339130646388945)
          ·
            refine ⟨62719334607254347984791709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83625779476339130646388945 62719334607254347984791709)
            ·
              refine ⟨23519750477720380494296891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62719334607254347984791709 23519750477720380494296891)
              ·
                refine ⟨35279625716580570741445337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23519750477720380494296891 35279625716580570741445337)
                ·
                  refine ⟨26459719287435428056084003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35279625716580570741445337 26459719287435428056084003)
                  ·
                    refine ⟨39689578931153142084126005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26459719287435428056084003 39689578931153142084126005)
                    ·
                      refine ⟨3720898024795607070386813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39689578931153142084126005 3720898024795607070386813)
                      ·
                        rfl

theorem cell23_7246423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 3, 1, 2, 1, 5].length) (baseStart_7246423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7246423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7246423 prefixEnd_7246423 := by exact prefixLift 7246423
  have htrace : WordTrace (prefixWord ++ tailWord_7246423) baseStart_7246423 baseEnd_7246423 := by
    simpa [prefixWord, tailWord_7246423, baseEnd_7246423] using wordTrace_append hprefix tailTrace_7246423
  have hstable : (prefixWord ++ tailWord_7246423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7246423).length < 2 ^ (prefixWord ++ tailWord_7246423).sum := by decide
  have hdescent : baseEnd_7246423 < baseStart_7246423 := by decide
  rcases family_descends (prefixWord ++ tailWord_7246423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7246527 : List Nat := [1, 1, 2, 2, 2, 6, 1, 1, 2, 1, 4]
def baseStart_7246527 : Nat := 118140960795 + 7246527 * 2 ^ 59
def prefixEnd_7246527 : Nat := 4983230072969 + 3 ^ 40 * 7246527 * 2
def baseEnd_7246527 : Nat := 3720951426783674663486335

theorem tailTrace_7246527 : CollatzResearch.WordTrace tailWord_7246527 prefixEnd_7246527 3720951426783674663486335 := by
  unfold tailWord_7246527
  simp only [CollatzResearch.WordTrace]
  refine ⟨264302553018077762125681835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176201702012051841417121223 264302553018077762125681835)
  ·
    refine ⟨396453829527116643188522753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264302553018077762125681835 396453829527116643188522753)
    ·
      refine ⟨297340372145337482391392065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 396453829527116643188522753 297340372145337482391392065)
      ·
        refine ⟨223005279109003111793544049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 297340372145337482391392065 223005279109003111793544049)
        ·
          refine ⟨167253959331752333845158037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 223005279109003111793544049 167253959331752333845158037)
          ·
            refine ⟨7840029343675890648991783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 167253959331752333845158037 7840029343675890648991783)
            ·
              refine ⟨11760044015513835973487675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7840029343675890648991783 11760044015513835973487675)
              ·
                refine ⟨17640066023270753960231513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11760044015513835973487675 17640066023270753960231513)
                ·
                  refine ⟨13230049517453065470173635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17640066023270753960231513 13230049517453065470173635)
                  ·
                    refine ⟨19845074276179598205260453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13230049517453065470173635 19845074276179598205260453)
                    ·
                      refine ⟨3720951426783674663486335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19845074276179598205260453 3720951426783674663486335)
                      ·
                        rfl

theorem cell23_7246527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 6, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 6, 1, 1, 2, 1, 4].length) (baseStart_7246527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7246527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7246527 prefixEnd_7246527 := by exact prefixLift 7246527
  have htrace : WordTrace (prefixWord ++ tailWord_7246527) baseStart_7246527 baseEnd_7246527 := by
    simpa [prefixWord, tailWord_7246527, baseEnd_7246527] using wordTrace_append hprefix tailTrace_7246527
  have hstable : (prefixWord ++ tailWord_7246527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7246527).length < 2 ^ (prefixWord ++ tailWord_7246527).sum := by decide
  have hdescent : baseEnd_7246527 < baseStart_7246527 := by decide
  rcases family_descends (prefixWord ++ tailWord_7246527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7246540 : List Nat := [2, 2, 1, 5, 1, 1, 1, 1, 2, 1, 6]
def baseStart_7246540 : Nat := 118140960795 + 7246540 * 2 ^ 59
def prefixEnd_7246540 : Nat := 4983230072969 + 3 ^ 40 * 7246540 * 2
def baseEnd_7246540 : Nat := 3720958102032183112623775

theorem tailTrace_7246540 : CollatzResearch.WordTrace tailWord_7246540 prefixEnd_7246540 3720958102032183112623775 := by
  unfold tailWord_7246540
  simp only [CollatzResearch.WordTrace]
  refine ⟨132151513583515332672952537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176202018111353776897270049 132151513583515332672952537)
  ·
    refine ⟨99113635187636499504714403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132151513583515332672952537 99113635187636499504714403)
    ·
      refine ⟨148670452781454749257071605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99113635187636499504714403 148670452781454749257071605)
      ·
        refine ⟨13937854948261382742850463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 148670452781454749257071605 13937854948261382742850463)
        ·
          refine ⟨20906782422392074114275695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13937854948261382742850463 20906782422392074114275695)
          ·
            refine ⟨31360173633588111171413543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20906782422392074114275695 31360173633588111171413543)
            ·
              refine ⟨47040260450382166757120315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31360173633588111171413543 47040260450382166757120315)
              ·
                refine ⟨70560390675573250135680473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47040260450382166757120315 70560390675573250135680473)
                ·
                  refine ⟨52920293006679937601760355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 70560390675573250135680473 52920293006679937601760355)
                  ·
                    refine ⟨79380439510019906402640533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 52920293006679937601760355 79380439510019906402640533)
                    ·
                      refine ⟨3720958102032183112623775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 79380439510019906402640533 3720958102032183112623775)
                      ·
                        rfl

theorem cell23_7246540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 1, 1, 2, 1, 6].length) (baseStart_7246540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7246540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7246540 prefixEnd_7246540 := by exact prefixLift 7246540
  have htrace : WordTrace (prefixWord ++ tailWord_7246540) baseStart_7246540 baseEnd_7246540 := by
    simpa [prefixWord, tailWord_7246540, baseEnd_7246540] using wordTrace_append hprefix tailTrace_7246540
  have hstable : (prefixWord ++ tailWord_7246540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7246540).length < 2 ^ (prefixWord ++ tailWord_7246540).sum := by decide
  have hdescent : baseEnd_7246540 < baseStart_7246540 := by decide
  rcases family_descends (prefixWord ++ tailWord_7246540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7246553 : List Nat := [1, 2, 1, 2, 3, 2, 1, 1, 1, 1, 8]
def baseStart_7246553 : Nat := 118140960795 + 7246553 * 2 ^ 59
def prefixEnd_7246553 : Nat := 4983230072969 + 3 ^ 40 * 7246553 * 2
def baseEnd_7246553 : Nat := 3720964777280691561761215

theorem tailTrace_7246553 : CollatzResearch.WordTrace tailWord_7246553 prefixEnd_7246553 3720964777280691561761215 := by
  unfold tailWord_7246553
  simp only [CollatzResearch.WordTrace]
  refine ⟨264303501315983568566128313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176202334210655712377418875 264303501315983568566128313)
  ·
    refine ⟨198227625986987676424596235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 264303501315983568566128313 198227625986987676424596235)
    ·
      refine ⟨297341438980481514636894353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198227625986987676424596235 297341438980481514636894353)
      ·
        refine ⟨223006079235361135977670765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 297341438980481514636894353 223006079235361135977670765)
        ·
          refine ⟨83627279713260425991626537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 223006079235361135977670765 83627279713260425991626537)
          ·
            refine ⟨62720459784945319493719903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83627279713260425991626537 62720459784945319493719903)
            ·
              refine ⟨94080689677417979240579855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62720459784945319493719903 94080689677417979240579855)
              ·
                refine ⟨141121034516126968860869783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94080689677417979240579855 141121034516126968860869783)
                ·
                  refine ⟨211681551774190453291304675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 141121034516126968860869783 211681551774190453291304675)
                  ·
                    refine ⟨317522327661285679936957013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 211681551774190453291304675 317522327661285679936957013)
                    ·
                      refine ⟨3720964777280691561761215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 317522327661285679936957013 3720964777280691561761215)
                      ·
                        rfl

theorem cell23_7246553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 1, 1, 1, 8].length) (baseStart_7246553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7246553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7246553 prefixEnd_7246553 := by exact prefixLift 7246553
  have htrace : WordTrace (prefixWord ++ tailWord_7246553) baseStart_7246553 baseEnd_7246553 := by
    simpa [prefixWord, tailWord_7246553, baseEnd_7246553] using wordTrace_append hprefix tailTrace_7246553
  have hstable : (prefixWord ++ tailWord_7246553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7246553).length < 2 ^ (prefixWord ++ tailWord_7246553).sum := by decide
  have hdescent : baseEnd_7246553 < baseStart_7246553 := by decide
  rcases family_descends (prefixWord ++ tailWord_7246553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7246577 : List Nat := [1, 2, 2, 2, 2, 2, 1, 4, 3, 1, 3]
def baseStart_7246577 : Nat := 118140960795 + 7246577 * 2 ^ 59
def prefixEnd_7246577 : Nat := 4983230072969 + 3 ^ 40 * 7246577 * 2
def baseEnd_7246577 : Nat := 3720977100816399467861105

theorem tailTrace_7246577 : CollatzResearch.WordTrace tailWord_7246577 prefixEnd_7246577 3720977100816399467861105 := by
  unfold tailWord_7246577
  simp only [CollatzResearch.WordTrace]
  refine ⟨264304376667896620665001985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176202917778597747110001323 264304376667896620665001985)
  ·
    refine ⟨198228282500922465498751489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 264304376667896620665001985 198228282500922465498751489)
    ·
      refine ⟨148671211875691849124063617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 198228282500922465498751489 148671211875691849124063617)
      ·
        refine ⟨111503408906768886843047713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148671211875691849124063617 111503408906768886843047713)
        ·
          refine ⟨83627556680076665132285785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111503408906768886843047713 83627556680076665132285785)
          ·
            refine ⟨62720667510057498849214339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83627556680076665132285785 62720667510057498849214339)
            ·
              refine ⟨94081001265086248273821509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62720667510057498849214339 94081001265086248273821509)
              ·
                refine ⟨17640187737203671551341533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 94081001265086248273821509 17640187737203671551341533)
                ·
                  refine ⟨6615070401451376831753075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17640187737203671551341533 6615070401451376831753075)
                  ·
                    refine ⟨9922605602177065247629613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6615070401451376831753075 9922605602177065247629613)
                    ·
                      refine ⟨3720977100816399467861105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9922605602177065247629613 3720977100816399467861105)
                      ·
                        rfl

theorem cell23_7246577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 4, 3, 1, 3].length) (baseStart_7246577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7246577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7246577 prefixEnd_7246577 := by exact prefixLift 7246577
  have htrace : WordTrace (prefixWord ++ tailWord_7246577) baseStart_7246577 baseEnd_7246577 := by
    simpa [prefixWord, tailWord_7246577, baseEnd_7246577] using wordTrace_append hprefix tailTrace_7246577
  have hstable : (prefixWord ++ tailWord_7246577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7246577).length < 2 ^ (prefixWord ++ tailWord_7246577).sum := by decide
  have hdescent : baseEnd_7246577 < baseStart_7246577 := by decide
  rcases family_descends (prefixWord ++ tailWord_7246577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7246611 : List Nat := [1, 1, 1, 2, 1, 3, 7, 2, 1, 1, 3]
def baseStart_7246611 : Nat := 118140960795 + 7246611 * 2 ^ 59
def prefixEnd_7246611 : Nat := 4983230072969 + 3 ^ 40 * 7246611 * 2
def baseEnd_7246611 : Nat := 3720994559158652334835949

theorem tailTrace_7246611 : CollatzResearch.WordTrace tailWord_7246611 prefixEnd_7246611 3720994559158652334835949 := by
  unfold tailWord_7246611
  simp only [CollatzResearch.WordTrace]
  refine ⟨264305616749773444471739687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176203744499848962981159791 264305616749773444471739687)
  ·
    refine ⟨396458425124660166707609531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264305616749773444471739687 396458425124660166707609531)
    ·
      refine ⟨594687637686990250061414297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 396458425124660166707609531 594687637686990250061414297)
      ·
        refine ⟨446015728265242687546060723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 594687637686990250061414297 446015728265242687546060723)
        ·
          refine ⟨669023592397864031319091085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 446015728265242687546060723 669023592397864031319091085)
          ·
            refine ⟨250883847149199011744659157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 669023592397864031319091085 250883847149199011744659157)
            ·
              refine ⟨5880090167559351837765449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 250883847149199011744659157 5880090167559351837765449)
              ·
                refine ⟨4410067625669513878324087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5880090167559351837765449 4410067625669513878324087)
                ·
                  refine ⟨6615101438504270817486131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4410067625669513878324087 6615101438504270817486131)
                  ·
                    refine ⟨9922652157756406226229197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6615101438504270817486131 9922652157756406226229197)
                    ·
                      refine ⟨3720994559158652334835949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9922652157756406226229197 3720994559158652334835949)
                      ·
                        rfl

theorem cell23_7246611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 7, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 7, 2, 1, 1, 3].length) (baseStart_7246611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7246611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7246611 prefixEnd_7246611 := by exact prefixLift 7246611
  have htrace : WordTrace (prefixWord ++ tailWord_7246611) baseStart_7246611 baseEnd_7246611 := by
    simpa [prefixWord, tailWord_7246611, baseEnd_7246611] using wordTrace_append hprefix tailTrace_7246611
  have hstable : (prefixWord ++ tailWord_7246611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7246611).length < 2 ^ (prefixWord ++ tailWord_7246611).sum := by decide
  have hdescent : baseEnd_7246611 < baseStart_7246611 := by decide
  rcases family_descends (prefixWord ++ tailWord_7246611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7246644 : List Nat := [2, 5, 1, 1, 3, 1, 1, 2, 1, 6]
def baseStart_7246644 : Nat := 118140960795 + 7246644 * 2 ^ 59
def prefixEnd_7246644 : Nat := 4983230072969 + 3 ^ 40 * 7246644 * 2
def baseEnd_7246644 : Nat := 1240337168006750235241099

theorem tailTrace_7246644 : CollatzResearch.WordTrace tailWord_7246644 prefixEnd_7246644 1240337168006750235241099 := by
  unfold tailWord_7246644
  simp only [CollatzResearch.WordTrace]
  refine ⟨132153410179326945553845493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176204546905769260738460657 132153410179326945553845493)
  ·
    refine ⟨12389382204311901145673015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 132153410179326945553845493 12389382204311901145673015)
    ·
      refine ⟨18584073306467851718509523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12389382204311901145673015 18584073306467851718509523)
      ·
        refine ⟨27876109959701777577764285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18584073306467851718509523 27876109959701777577764285)
        ·
          refine ⟨10453541234888166591661607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27876109959701777577764285 10453541234888166591661607)
          ·
            refine ⟨15680311852332249887492411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10453541234888166591661607 15680311852332249887492411)
            ·
              refine ⟨23520467778498374831238617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15680311852332249887492411 23520467778498374831238617)
              ·
                refine ⟨17640350833873781123428963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23520467778498374831238617 17640350833873781123428963)
                ·
                  refine ⟨26460526250810671685143445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17640350833873781123428963 26460526250810671685143445)
                  ·
                    refine ⟨1240337168006750235241099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26460526250810671685143445 1240337168006750235241099)
                    ·
                      rfl

theorem cell23_7246644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 1, 2, 1, 6].length) (baseStart_7246644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7246644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7246644 prefixEnd_7246644 := by exact prefixLift 7246644
  have htrace : WordTrace (prefixWord ++ tailWord_7246644) baseStart_7246644 baseEnd_7246644 := by
    simpa [prefixWord, tailWord_7246644, baseEnd_7246644] using wordTrace_append hprefix tailTrace_7246644
  have hstable : (prefixWord ++ tailWord_7246644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7246644).length < 2 ^ (prefixWord ++ tailWord_7246644).sum := by decide
  have hdescent : baseEnd_7246644 < baseStart_7246644 := by decide
  rcases family_descends (prefixWord ++ tailWord_7246644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7246657 : List Nat := [1, 2, 5, 3, 1, 11]
def baseStart_7246657 : Nat := 118140960795 + 7246657 * 2 ^ 59
def prefixEnd_7246657 : Nat := 4983230072969 + 3 ^ 40 * 7246657 * 2
def baseEnd_7246657 : Nat := 15312832013451683764859

theorem tailTrace_7246657 : CollatzResearch.WordTrace tailWord_7246657 prefixEnd_7246657 15312832013451683764859 := by
  unfold tailWord_7246657
  simp only [CollatzResearch.WordTrace]
  refine ⟨264307294507606794327914225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176204863005071196218609483 264307294507606794327914225)
  ·
    refine ⟨198230470880705095745935669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 264307294507606794327914225 198230470880705095745935669)
    ·
      refine ⟨18584106645066102726181469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 198230470880705095745935669 18584106645066102726181469)
      ·
        refine ⟨6969039991899788522318051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18584106645066102726181469 6969039991899788522318051)
        ·
          refine ⟨10453559987849682783477077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6969039991899788522318051 10453559987849682783477077)
          ·
            refine ⟨15312832013451683764859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 10453559987849682783477077 15312832013451683764859)
            ·
              rfl

theorem cell23_7246657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 11].length) (baseStart_7246657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7246657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7246657 prefixEnd_7246657 := by exact prefixLift 7246657
  have htrace : WordTrace (prefixWord ++ tailWord_7246657) baseStart_7246657 baseEnd_7246657 := by
    simpa [prefixWord, tailWord_7246657, baseEnd_7246657] using wordTrace_append hprefix tailTrace_7246657
  have hstable : (prefixWord ++ tailWord_7246657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7246657).length < 2 ^ (prefixWord ++ tailWord_7246657).sum := by decide
  have hdescent : baseEnd_7246657 < baseStart_7246657 := by decide
  rcases family_descends (prefixWord ++ tailWord_7246657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7246668 : List Nat := [2, 2, 1, 3, 3, 2, 1, 4, 1, 2, 2]
def baseStart_7246668 : Nat := 118140960795 + 7246668 * 2 ^ 59
def prefixEnd_7246668 : Nat := 4983230072969 + 3 ^ 40 * 7246668 * 2
def baseEnd_7246668 : Nat := 3721023827555958611823187

theorem tailTrace_7246668 : CollatzResearch.WordTrace tailWord_7246668 prefixEnd_7246668 3721023827555958611823187 := by
  unfold tailWord_7246668
  simp only [CollatzResearch.WordTrace]
  refine ⟨132153847855283471603282329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176205130473711295471043105 132153847855283471603282329)
  ·
    refine ⟨99115385891462603702461747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132153847855283471603282329 99115385891462603702461747)
    ·
      refine ⟨148673078837193905553692621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99115385891462603702461747 148673078837193905553692621)
      ·
        refine ⟨55752404563947714582634733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 148673078837193905553692621 55752404563947714582634733)
        ·
          refine ⟨20907151711480392968488025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55752404563947714582634733 20907151711480392968488025)
          ·
            refine ⟨15680363783610294726366019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20907151711480392968488025 15680363783610294726366019)
            ·
              refine ⟨23520545675415442089549029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15680363783610294726366019 23520545675415442089549029)
              ·
                refine ⟨4410102314140395391790443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23520545675415442089549029 4410102314140395391790443)
                ·
                  refine ⟨6615153471210593087685665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4410102314140395391790443 6615153471210593087685665)
                  ·
                    refine ⟨4961365103407944815764249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6615153471210593087685665 4961365103407944815764249)
                    ·
                      refine ⟨3721023827555958611823187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4961365103407944815764249 3721023827555958611823187)
                      ·
                        rfl

theorem cell23_7246668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 1, 4, 1, 2, 2].length) (baseStart_7246668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7246668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7246668 prefixEnd_7246668 := by exact prefixLift 7246668
  have htrace : WordTrace (prefixWord ++ tailWord_7246668) baseStart_7246668 baseEnd_7246668 := by
    simpa [prefixWord, tailWord_7246668, baseEnd_7246668] using wordTrace_append hprefix tailTrace_7246668
  have hstable : (prefixWord ++ tailWord_7246668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7246668).length < 2 ^ (prefixWord ++ tailWord_7246668).sum := by decide
  have hdescent : baseEnd_7246668 < baseStart_7246668 := by decide
  rcases family_descends (prefixWord ++ tailWord_7246668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7246684 : List Nat := [2, 2, 4, 2, 1, 1, 1, 3, 1, 3, 3]
def baseStart_7246684 : Nat := 118140960795 + 7246684 * 2 ^ 59
def prefixEnd_7246684 : Nat := 4983230072969 + 3 ^ 40 * 7246684 * 2
def baseEnd_7246684 : Nat := 3721032043246430549223113

theorem tailTrace_7246684 : CollatzResearch.WordTrace tailWord_7246684 prefixEnd_7246684 3721032043246430549223113 := by
  unfold tailWord_7246684
  simp only [CollatzResearch.WordTrace]
  refine ⟨132154139639254488969573553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176205519519005985292764737 132154139639254488969573553)
  ·
    refine ⟨99115604729440866727180165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132154139639254488969573553 99115604729440866727180165)
    ·
      refine ⟨18584175886770162511346281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 99115604729440866727180165 18584175886770162511346281)
      ·
        refine ⟨13938131915077621883509711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18584175886770162511346281 13938131915077621883509711)
        ·
          refine ⟨20907197872616432825264567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13938131915077621883509711 20907197872616432825264567)
          ·
            refine ⟨31360796808924649237896851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20907197872616432825264567 31360796808924649237896851)
            ·
              refine ⟨47041195213386973856845277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31360796808924649237896851 47041195213386973856845277)
              ·
                refine ⟨17640448205020115196316979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47041195213386973856845277 17640448205020115196316979)
                ·
                  refine ⟨26460672307530172794475469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17640448205020115196316979 26460672307530172794475469)
                  ·
                    refine ⟨9922752115323814797928301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26460672307530172794475469 9922752115323814797928301)
                    ·
                      refine ⟨3721032043246430549223113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9922752115323814797928301 3721032043246430549223113)
                      ·
                        rfl

theorem cell23_7246684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 1, 3, 1, 3, 3].length) (baseStart_7246684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7246684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7246684 prefixEnd_7246684 := by exact prefixLift 7246684
  have htrace : WordTrace (prefixWord ++ tailWord_7246684) baseStart_7246684 baseEnd_7246684 := by
    simpa [prefixWord, tailWord_7246684, baseEnd_7246684] using wordTrace_append hprefix tailTrace_7246684
  have hstable : (prefixWord ++ tailWord_7246684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7246684).length < 2 ^ (prefixWord ++ tailWord_7246684).sum := by decide
  have hdescent : baseEnd_7246684 < baseStart_7246684 := by decide
  rcases family_descends (prefixWord ++ tailWord_7246684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7246700 : List Nat := [2, 2, 1, 1, 4, 1, 1, 2, 1, 8]
def baseStart_7246700 : Nat := 118140960795 + 7246700 * 2 ^ 59
def prefixEnd_7246700 : Nat := 4983230072969 + 3 ^ 40 * 7246700 * 2
def baseEnd_7246700 : Nat := 1240346752978967495541013

theorem tailTrace_7246700 : CollatzResearch.WordTrace tailWord_7246700 prefixEnd_7246700 1240346752978967495541013 := by
  unfold tailWord_7246700
  simp only [CollatzResearch.WordTrace]
  refine ⟨132154431423225506335864777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176205908564300675114486369 132154431423225506335864777)
  ·
    refine ⟨99115823567419129751898583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132154431423225506335864777 99115823567419129751898583)
    ·
      refine ⟨148673735351128694627847875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99115823567419129751898583 148673735351128694627847875)
      ·
        refine ⟨223010603026693041941771813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148673735351128694627847875 223010603026693041941771813)
        ·
          refine ⟨41814488067504945364082215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 223010603026693041941771813 41814488067504945364082215)
          ·
            refine ⟨62721732101257418046123323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41814488067504945364082215 62721732101257418046123323)
            ·
              refine ⟨94082598151886127069184985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62721732101257418046123323 94082598151886127069184985)
              ·
                refine ⟨70561948613914595301888739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 94082598151886127069184985 70561948613914595301888739)
                ·
                  refine ⟨105842922920871892952833109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70561948613914595301888739 105842922920871892952833109)
                  ·
                    refine ⟨1240346752978967495541013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 105842922920871892952833109 1240346752978967495541013)
                    ·
                      rfl

theorem cell23_7246700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 8].length) (baseStart_7246700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7246700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7246700 prefixEnd_7246700 := by exact prefixLift 7246700
  have htrace : WordTrace (prefixWord ++ tailWord_7246700) baseStart_7246700 baseEnd_7246700 := by
    simpa [prefixWord, tailWord_7246700, baseEnd_7246700] using wordTrace_append hprefix tailTrace_7246700
  have hstable : (prefixWord ++ tailWord_7246700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7246700).length < 2 ^ (prefixWord ++ tailWord_7246700).sum := by decide
  have hdescent : baseEnd_7246700 < baseStart_7246700 := by decide
  rcases family_descends (prefixWord ++ tailWord_7246700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7246718 : List Nat := [4, 2, 3, 1, 2, 1, 1, 1, 4, 1, 3]
def baseStart_7246718 : Nat := 118140960795 + 7246718 * 2 ^ 59
def prefixEnd_7246718 : Nat := 4983230072969 + 3 ^ 40 * 7246718 * 2
def baseEnd_7246718 : Nat := 3721049501588683416197957

theorem tailTrace_7246718 : CollatzResearch.WordTrace tailWord_7246718 prefixEnd_7246718 3721049501588683416197957 := by
  unfold tailWord_7246718
  simp only [CollatzResearch.WordTrace]
  refine ⟨33038689920048225218235601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 176206346240257201163923205 33038689920048225218235601)
  ·
    refine ⟨24779017440036168913676701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33038689920048225218235601 24779017440036168913676701)
    ·
      refine ⟨9292131540013563342628763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24779017440036168913676701 9292131540013563342628763)
      ·
        refine ⟨13938197310020345013943145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9292131540013563342628763 13938197310020345013943145)
        ·
          refine ⟨10453647982515258760457359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13938197310020345013943145 10453647982515258760457359)
          ·
            refine ⟨15680471973772888140686039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10453647982515258760457359 15680471973772888140686039)
            ·
              refine ⟨23520707960659332211029059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15680471973772888140686039 23520707960659332211029059)
              ·
                refine ⟨35281061940988998316543589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23520707960659332211029059 35281061940988998316543589)
                ·
                  refine ⟨6615199113935437184351923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35281061940988998316543589 6615199113935437184351923)
                  ·
                    refine ⟨9922798670903155776527885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6615199113935437184351923 9922798670903155776527885)
                    ·
                      refine ⟨3721049501588683416197957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9922798670903155776527885 3721049501588683416197957)
                      ·
                        rfl

theorem cell23_7246718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 1, 1, 4, 1, 3].length) (baseStart_7246718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7246718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7246718 prefixEnd_7246718 := by exact prefixLift 7246718
  have htrace : WordTrace (prefixWord ++ tailWord_7246718) baseStart_7246718 baseEnd_7246718 := by
    simpa [prefixWord, tailWord_7246718, baseEnd_7246718] using wordTrace_append hprefix tailTrace_7246718
  have hstable : (prefixWord ++ tailWord_7246718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7246718).length < 2 ^ (prefixWord ++ tailWord_7246718).sum := by decide
  have hdescent : baseEnd_7246718 < baseStart_7246718 := by decide
  rcases family_descends (prefixWord ++ tailWord_7246718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7246741 : List Nat := [1, 3, 2, 1, 1, 6, 1, 1, 1, 4, 2]
def baseStart_7246741 : Nat := 118140960795 + 7246741 * 2 ^ 59
def prefixEnd_7246741 : Nat := 4983230072969 + 3 ^ 40 * 7246741 * 2
def baseEnd_7246741 : Nat := 3721061311643736826210351

theorem tailTrace_7246741 : CollatzResearch.WordTrace tailWord_7246741 prefixEnd_7246741 3721061311643736826210351 := by
  unfold tailWord_7246741
  simp only [CollatzResearch.WordTrace]
  refine ⟨264310358239302476673972077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176206905492868317782648051 264310358239302476673972077)
  ·
    refine ⟨99116384339738428752739529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 264310358239302476673972077 99116384339738428752739529)
    ·
      refine ⟨74337288254803821564554647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99116384339738428752739529 74337288254803821564554647)
      ·
        refine ⟨111505932382205732346831971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74337288254803821564554647 111505932382205732346831971)
        ·
          refine ⟨167258898573308598520247957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111505932382205732346831971 167258898573308598520247957)
          ·
            refine ⟨7840260870623840555636623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 167258898573308598520247957 7840260870623840555636623)
            ·
              refine ⟨11760391305935760833454935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7840260870623840555636623 11760391305935760833454935)
              ·
                refine ⟨17640586958903641250182403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11760391305935760833454935 17640586958903641250182403)
                ·
                  refine ⟨26460880438355461875273605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17640586958903641250182403 26460880438355461875273605)
                  ·
                    refine ⟨4961415082191649101613801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26460880438355461875273605 4961415082191649101613801)
                    ·
                      refine ⟨3721061311643736826210351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4961415082191649101613801 3721061311643736826210351)
                      ·
                        rfl

theorem cell23_7246741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 6, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 6, 1, 1, 1, 4, 2].length) (baseStart_7246741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7246741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7246741 prefixEnd_7246741 := by exact prefixLift 7246741
  have htrace : WordTrace (prefixWord ++ tailWord_7246741) baseStart_7246741 baseEnd_7246741 := by
    simpa [prefixWord, tailWord_7246741, baseEnd_7246741] using wordTrace_append hprefix tailTrace_7246741
  have hstable : (prefixWord ++ tailWord_7246741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7246741).length < 2 ^ (prefixWord ++ tailWord_7246741).sum := by decide
  have hdescent : baseEnd_7246741 < baseStart_7246741 := by decide
  rcases family_descends (prefixWord ++ tailWord_7246741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7246777 : List Nat := [1, 2, 1, 4, 2, 2, 1, 1, 4, 5]
def baseStart_7246777 : Nat := 118140960795 + 7246777 * 2 ^ 59
def prefixEnd_7246777 : Nat := 4983230072969 + 3 ^ 40 * 7246777 * 2
def baseEnd_7246777 : Nat := 1240359932315766228453395

theorem tailTrace_7246777 : CollatzResearch.WordTrace tailWord_7246777 prefixEnd_7246777 1240359932315766228453395 := by
  unfold tailWord_7246777
  simp only [CollatzResearch.WordTrace]
  refine ⟨264311671267172054822282585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176207780844781369881521723 264311671267172054822282585)
  ·
    refine ⟨198233753450379041116711939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 264311671267172054822282585 198233753450379041116711939)
    ·
      refine ⟨297350630175568561675067909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198233753450379041116711939 297350630175568561675067909)
      ·
        refine ⟨55753243157919105314075233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 297350630175568561675067909 55753243157919105314075233)
        ·
          refine ⟨41814932368439328985556425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55753243157919105314075233 41814932368439328985556425)
          ·
            refine ⟨31361199276329496739167319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41814932368439328985556425 31361199276329496739167319)
            ·
              refine ⟨47041798914494245108750979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31361199276329496739167319 47041798914494245108750979)
              ·
                refine ⟨70562698371741367663126469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47041798914494245108750979 70562698371741367663126469)
                ·
                  refine ⟨13230505944701506436836213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 70562698371741367663126469 13230505944701506436836213)
                  ·
                    refine ⟨1240359932315766228453395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13230505944701506436836213 1240359932315766228453395)
                    ·
                      rfl

theorem cell23_7246777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 1, 1, 4, 5].length) (baseStart_7246777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7246777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7246777 prefixEnd_7246777 := by exact prefixLift 7246777
  have htrace : WordTrace (prefixWord ++ tailWord_7246777) baseStart_7246777 baseEnd_7246777 := by
    simpa [prefixWord, tailWord_7246777, baseEnd_7246777] using wordTrace_append hprefix tailTrace_7246777
  have hstable : (prefixWord ++ tailWord_7246777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7246777).length < 2 ^ (prefixWord ++ tailWord_7246777).sum := by decide
  have hdescent : baseEnd_7246777 < baseStart_7246777 := by decide
  rcases family_descends (prefixWord ++ tailWord_7246777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7246781 : List Nat := [1, 4, 1, 2, 5, 1, 1, 1, 7]
def baseStart_7246781 : Nat := 118140960795 + 7246781 * 2 ^ 59
def prefixEnd_7246781 : Nat := 4983230072969 + 3 ^ 40 * 7246781 * 2
def baseEnd_7246781 : Nat := 413453538985546296634463

theorem tailTrace_7246781 : CollatzResearch.WordTrace tailWord_7246781 prefixEnd_7246781 413453538985546296634463 := by
  unfold tailWord_7246781
  simp only [CollatzResearch.WordTrace]
  refine ⟨264311817159157563505428197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176207878106105042336952131 264311817159157563505428197)
  ·
    refine ⟨49558465717342043157267787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 264311817159157563505428197 49558465717342043157267787)
    ·
      refine ⟨74337698576013064735901681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49558465717342043157267787 74337698576013064735901681)
      ·
        refine ⟨55753273932009798551926261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74337698576013064735901681 55753273932009798551926261)
        ·
          refine ⟨5226869431125918614243087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 55753273932009798551926261 5226869431125918614243087)
          ·
            refine ⟨7840304146688877921364631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5226869431125918614243087 7840304146688877921364631)
            ·
              refine ⟨11760456220033316882046947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7840304146688877921364631 11760456220033316882046947)
              ·
                refine ⟨17640684330049975323070421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11760456220033316882046947 17640684330049975323070421)
                ·
                  refine ⟨413453538985546296634463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17640684330049975323070421 413453538985546296634463)
                  ·
                    rfl

theorem cell23_7246781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 5, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 5, 1, 1, 1, 7].length) (baseStart_7246781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7246781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7246781 prefixEnd_7246781 := by exact prefixLift 7246781
  have htrace : WordTrace (prefixWord ++ tailWord_7246781) baseStart_7246781 baseEnd_7246781 := by
    simpa [prefixWord, tailWord_7246781, baseEnd_7246781] using wordTrace_append hprefix tailTrace_7246781
  have hstable : (prefixWord ++ tailWord_7246781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7246781).length < 2 ^ (prefixWord ++ tailWord_7246781).sum := by decide
  have hdescent : baseEnd_7246781 < baseStart_7246781 := by decide
  rcases family_descends (prefixWord ++ tailWord_7246781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7246792 : List Nat := [2, 1, 3, 1, 6, 1, 2, 1, 2, 2, 2]
def baseStart_7246792 : Nat := 118140960795 + 7246792 * 2 ^ 59
def prefixEnd_7246792 : Nat := 4983230072969 + 3 ^ 40 * 7246792 * 2
def baseEnd_7246792 : Nat := 3721087499157116126672617

theorem tailTrace_7246792 : CollatzResearch.WordTrace tailWord_7246792 prefixEnd_7246792 3721087499157116126672617 := by
  unfold tailWord_7246792
  simp only [CollatzResearch.WordTrace]
  refine ⟨132156109181058856192039315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176208145574745141589385753 132156109181058856192039315)
  ·
    refine ⟨198234163771588284288058973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132156109181058856192039315 198234163771588284288058973)
    ·
      refine ⟨74337811414345606608022115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 198234163771588284288058973 74337811414345606608022115)
      ·
        refine ⟨111506717121518409912033173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74337811414345606608022115 111506717121518409912033173)
        ·
          refine ⟨5226877365071175464626555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 111506717121518409912033173 5226877365071175464626555)
          ·
            refine ⟨7840316047606763196939833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5226877365071175464626555 7840316047606763196939833)
            ·
              refine ⟨5880237035705072397704875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7840316047606763196939833 5880237035705072397704875)
              ·
                refine ⟨8820355553557608596557313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5880237035705072397704875 8820355553557608596557313)
                ·
                  refine ⟨6615266665168206447417985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8820355553557608596557313 6615266665168206447417985)
                  ·
                    refine ⟨4961449998876154835563489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6615266665168206447417985 4961449998876154835563489)
                    ·
                      refine ⟨3721087499157116126672617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4961449998876154835563489 3721087499157116126672617)
                      ·
                        rfl

theorem cell23_7246792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 6, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 6, 1, 2, 1, 2, 2, 2].length) (baseStart_7246792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7246792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7246792 prefixEnd_7246792 := by exact prefixLift 7246792
  have htrace : WordTrace (prefixWord ++ tailWord_7246792) baseStart_7246792 baseEnd_7246792 := by
    simpa [prefixWord, tailWord_7246792, baseEnd_7246792] using wordTrace_append hprefix tailTrace_7246792
  have hstable : (prefixWord ++ tailWord_7246792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7246792).length < 2 ^ (prefixWord ++ tailWord_7246792).sum := by decide
  have hdescent : baseEnd_7246792 < baseStart_7246792 := by decide
  rcases family_descends (prefixWord ++ tailWord_7246792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7246841 : List Nat := [1, 2, 1, 3, 1, 3, 3, 4, 1, 4]
def baseStart_7246841 : Nat := 118140960795 + 7246841 * 2 ^ 59
def prefixEnd_7246841 : Nat := 4983230072969 + 3 ^ 40 * 7246841 * 2
def baseEnd_7246841 : Nat := 1240370886569728811653297

theorem tailTrace_7246841 : CollatzResearch.WordTrace tailWord_7246841 prefixEnd_7246841 1240370886569728811653297 := by
  unfold tailWord_7246841
  simp only [CollatzResearch.WordTrace]
  refine ⟨264314005538940193752612377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176209337025960129168408251 264314005538940193752612377)
  ·
    refine ⟨198235504154205145314459283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 264314005538940193752612377 198235504154205145314459283)
    ·
      refine ⟨297353256231307717971688925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198235504154205145314459283 297353256231307717971688925)
      ·
        refine ⟨111507471086740394239383347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 297353256231307717971688925 111507471086740394239383347)
        ·
          refine ⟨167261206630110591359075021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111507471086740394239383347 167261206630110591359075021)
          ·
            refine ⟨62722952486291471759653133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 167261206630110591359075021 62722952486291471759653133)
            ·
              refine ⟨23521107182359301909869925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62722952486291471759653133 23521107182359301909869925)
              ·
                refine ⟨4410207596692369108100611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23521107182359301909869925 4410207596692369108100611)
                ·
                  refine ⟨6615311395038553662150917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4410207596692369108100611 6615311395038553662150917)
                  ·
                    refine ⟨1240370886569728811653297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6615311395038553662150917 1240370886569728811653297)
                    ·
                      rfl

theorem cell23_7246841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 3, 4, 1, 4].length) (baseStart_7246841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7246841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7246841 prefixEnd_7246841 := by exact prefixLift 7246841
  have htrace : WordTrace (prefixWord ++ tailWord_7246841) baseStart_7246841 baseEnd_7246841 := by
    simpa [prefixWord, tailWord_7246841, baseEnd_7246841] using wordTrace_append hprefix tailTrace_7246841
  have hstable : (prefixWord ++ tailWord_7246841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7246841).length < 2 ^ (prefixWord ++ tailWord_7246841).sum := by decide
  have hdescent : baseEnd_7246841 < baseStart_7246841 := by decide
  rcases family_descends (prefixWord ++ tailWord_7246841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7246847 : List Nat := [1, 1, 2, 2, 1, 2, 1, 1, 4, 5, 3]
def baseStart_7246847 : Nat := 118140960795 + 7246847 * 2 ^ 59
def prefixEnd_7246847 : Nat := 4983230072969 + 3 ^ 40 * 7246847 * 2
def baseEnd_7246847 : Nat := 3721115740593113411484863

theorem tailTrace_7246847 : CollatzResearch.WordTrace tailWord_7246847 prefixEnd_7246847 3721115740593113411484863 := by
  unfold tailWord_7246847
  simp only [CollatzResearch.WordTrace]
  refine ⟨264314224376918456777330795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176209482917945637851553863 264314224376918456777330795)
  ·
    refine ⟨396471336565377685165996193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264314224376918456777330795 396471336565377685165996193)
    ·
      refine ⟨297353502424033263874497145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 396471336565377685165996193 297353502424033263874497145)
      ·
        refine ⟨223015126818024947905872859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 297353502424033263874497145 223015126818024947905872859)
        ·
          refine ⟨334522690227037421858809289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 223015126818024947905872859 334522690227037421858809289)
          ·
            refine ⟨250892017670278066394106967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 334522690227037421858809289 250892017670278066394106967)
            ·
              refine ⟨376338026505417099591160451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 250892017670278066394106967 376338026505417099591160451)
              ·
                refine ⟨564507039758125649386740677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 376338026505417099591160451 564507039758125649386740677)
                ·
                  refine ⟨105845069954648559260013877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 564507039758125649386740677 105845069954648559260013877)
                  ·
                    refine ⟨9922975308248302430626301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 105845069954648559260013877 9922975308248302430626301)
                    ·
                      refine ⟨3721115740593113411484863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9922975308248302430626301 3721115740593113411484863)
                      ·
                        rfl

theorem cell23_7246847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 4, 5, 3].length) (baseStart_7246847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7246847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7246847 prefixEnd_7246847 := by exact prefixLift 7246847
  have htrace : WordTrace (prefixWord ++ tailWord_7246847) baseStart_7246847 baseEnd_7246847 := by
    simpa [prefixWord, tailWord_7246847, baseEnd_7246847] using wordTrace_append hprefix tailTrace_7246847
  have hstable : (prefixWord ++ tailWord_7246847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7246847).length < 2 ^ (prefixWord ++ tailWord_7246847).sum := by decide
  have hdescent : baseEnd_7246847 < baseStart_7246847 := by decide
  rcases family_descends (prefixWord ++ tailWord_7246847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7246898 : List Nat := [3, 2, 1, 1, 2, 2, 1, 6, 1, 1, 3]
def baseStart_7246898 : Nat := 118140960795 + 7246898 * 2 ^ 59
def prefixEnd_7246898 : Nat := 4983230072969 + 3 ^ 40 * 7246898 * 2
def baseEnd_7246898 : Nat := 3721141928106492711947129

theorem tailTrace_7246898 : CollatzResearch.WordTrace tailWord_7246898 prefixEnd_7246898 3721141928106492711947129 := by
  unfold tailWord_7246898
  simp only [CollatzResearch.WordTrace]
  refine ⟨66079021124933423121859337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176210722999822461658291565 66079021124933423121859337)
  ·
    refine ⟨49559265843700067341394503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66079021124933423121859337 49559265843700067341394503)
    ·
      refine ⟨74338898765550101012091755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49559265843700067341394503 74338898765550101012091755)
      ·
        refine ⟨111508348148325151518137633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74338898765550101012091755 111508348148325151518137633)
        ·
          refine ⟨83631261111243863638603225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111508348148325151518137633 83631261111243863638603225)
          ·
            refine ⟨62723445833432897728952419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83631261111243863638603225 62723445833432897728952419)
            ·
              refine ⟨94085168750149346593428629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62723445833432897728952419 94085168750149346593428629)
              ·
                refine ⟨4410242285163250621566967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 94085168750149346593428629 4410242285163250621566967)
                ·
                  refine ⟨6615363427744875932350451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4410242285163250621566967 6615363427744875932350451)
                  ·
                    refine ⟨9923045141617313898525677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6615363427744875932350451 9923045141617313898525677)
                    ·
                      refine ⟨3721141928106492711947129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9923045141617313898525677 3721141928106492711947129)
                      ·
                        rfl

theorem cell23_7246898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 6, 1, 1, 3].length) (baseStart_7246898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7246898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7246898 prefixEnd_7246898 := by exact prefixLift 7246898
  have htrace : WordTrace (prefixWord ++ tailWord_7246898) baseStart_7246898 baseEnd_7246898 := by
    simpa [prefixWord, tailWord_7246898, baseEnd_7246898] using wordTrace_append hprefix tailTrace_7246898
  have hstable : (prefixWord ++ tailWord_7246898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7246898).length < 2 ^ (prefixWord ++ tailWord_7246898).sum := by decide
  have hdescent : baseEnd_7246898 < baseStart_7246898 := by decide
  rcases family_descends (prefixWord ++ tailWord_7246898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7246918 : List Nat := [6, 1, 1, 1, 1, 2, 1, 4, 1, 5]
def baseStart_7246918 : Nat := 118140960795 + 7246918 * 2 ^ 59
def prefixEnd_7246918 : Nat := 4983230072969 + 3 ^ 40 * 7246918 * 2
def baseEnd_7246918 : Nat := 1240384065906527544565679

theorem tailTrace_7246918 : CollatzResearch.WordTrace tailWord_7246918 prefixEnd_7246918 1240384065906527544565679 := by
  unfold tailWord_7246918
  simp only [CollatzResearch.WordTrace]
  refine ⟨8259900436239413621973919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 176211209306440823935443605 8259900436239413621973919)
  ·
    refine ⟨12389850654359120432960879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8259900436239413621973919 12389850654359120432960879)
    ·
      refine ⟨18584775981538680649441319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12389850654359120432960879 18584775981538680649441319)
      ·
        refine ⟨27877163972308020974161979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18584775981538680649441319 27877163972308020974161979)
        ·
          refine ⟨41815745958462031461242969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27877163972308020974161979 41815745958462031461242969)
          ·
            refine ⟨31361809468846523595932227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41815745958462031461242969 31361809468846523595932227)
            ·
              refine ⟨47042714203269785393898341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31361809468846523595932227 47042714203269785393898341)
              ·
                refine ⟨8820508913113084761355939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47042714203269785393898341 8820508913113084761355939)
                ·
                  refine ⟨13230763369669627142033909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8820508913113084761355939 13230763369669627142033909)
                  ·
                    refine ⟨1240384065906527544565679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13230763369669627142033909 1240384065906527544565679)
                    ·
                      rfl

theorem cell23_7246918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 1, 4, 1, 5].length) (baseStart_7246918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7246918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7246918 prefixEnd_7246918 := by exact prefixLift 7246918
  have htrace : WordTrace (prefixWord ++ tailWord_7246918) baseStart_7246918 baseEnd_7246918 := by
    simpa [prefixWord, tailWord_7246918, baseEnd_7246918] using wordTrace_append hprefix tailTrace_7246918
  have hstable : (prefixWord ++ tailWord_7246918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7246918).length < 2 ^ (prefixWord ++ tailWord_7246918).sum := by decide
  have hdescent : baseEnd_7246918 < baseStart_7246918 := by decide
  rcases family_descends (prefixWord ++ tailWord_7246918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7246921 : List Nat := [1, 2, 1, 1, 2, 2, 2, 3, 5, 2, 2]
def baseStart_7246921 : Nat := 118140960795 + 7246921 * 2 ^ 59
def prefixEnd_7246921 : Nat := 4983230072969 + 3 ^ 40 * 7246921 * 2
def baseEnd_7246921 : Nat := 3721153738161546121959523

theorem tailTrace_7246921 : CollatzResearch.WordTrace tailWord_7246921 prefixEnd_7246921 3721153738161546121959523 := by
  unfold tailWord_7246921
  simp only [CollatzResearch.WordTrace]
  refine ⟨264316923378650367415524617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176211282252433578277016411 264316923378650367415524617)
  ·
    refine ⟨198237692533987775561643463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 264316923378650367415524617 198237692533987775561643463)
    ·
      refine ⟨297356538800981663342465195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198237692533987775561643463 297356538800981663342465195)
      ·
        refine ⟨446034808201472495013697793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 297356538800981663342465195 446034808201472495013697793)
        ·
          refine ⟨334526106151104371260273345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 446034808201472495013697793 334526106151104371260273345)
          ·
            refine ⟨250894579613328278445205009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 334526106151104371260273345 250894579613328278445205009)
            ·
              refine ⟨188170934709996208833903757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 250894579613328278445205009 188170934709996208833903757)
              ·
                refine ⟨70564100516248578312713909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 188170934709996208833903757 70564100516248578312713909)
                ·
                  refine ⟨6615384423398304216816929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 70564100516248578312713909 6615384423398304216816929)
                  ·
                    refine ⟨4961538317548728162612697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6615384423398304216816929 4961538317548728162612697)
                    ·
                      refine ⟨3721153738161546121959523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4961538317548728162612697 3721153738161546121959523)
                      ·
                        rfl

theorem cell23_7246921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 3, 5, 2, 2].length) (baseStart_7246921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7246921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7246921 prefixEnd_7246921 := by exact prefixLift 7246921
  have htrace : WordTrace (prefixWord ++ tailWord_7246921) baseStart_7246921 baseEnd_7246921 := by
    simpa [prefixWord, tailWord_7246921, baseEnd_7246921] using wordTrace_append hprefix tailTrace_7246921
  have hstable : (prefixWord ++ tailWord_7246921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7246921).length < 2 ^ (prefixWord ++ tailWord_7246921).sum := by decide
  have hdescent : baseEnd_7246921 < baseStart_7246921 := by decide
  rcases family_descends (prefixWord ++ tailWord_7246921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7246942 : List Nat := [4, 4, 1, 1, 1, 2, 1, 2, 2, 3, 2]
def baseStart_7246942 : Nat := 118140960795 + 7246942 * 2 ^ 59
def prefixEnd_7246942 : Nat := 4983230072969 + 3 ^ 40 * 7246942 * 2
def baseEnd_7246942 : Nat := 3721164521255290539796927

theorem tailTrace_7246942 : CollatzResearch.WordTrace tailWord_7246942 prefixEnd_7246942 3721164521255290539796927 := by
  unfold tailWord_7246942
  simp only [CollatzResearch.WordTrace]
  refine ⟨33039711163946786000254885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 176211792874382858668026053 33039711163946786000254885)
  ·
    refine ⟨6194945843240022375047791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33039711163946786000254885 6194945843240022375047791)
    ·
      refine ⟨9292418764860033562571687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6194945843240022375047791 9292418764860033562571687)
      ·
        refine ⟨13938628147290050343857531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9292418764860033562571687 13938628147290050343857531)
        ·
          refine ⟨20907942220935075515786297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13938628147290050343857531 20907942220935075515786297)
          ·
            refine ⟨15680956665701306636839723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20907942220935075515786297 15680956665701306636839723)
            ·
              refine ⟨23521434998551959955259585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15680956665701306636839723 23521434998551959955259585)
              ·
                refine ⟨17641076248913969966444689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23521434998551959955259585 17641076248913969966444689)
                ·
                  refine ⟨13230807186685477474833517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17641076248913969966444689 13230807186685477474833517)
                  ·
                    refine ⟨4961552695007054053062569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13230807186685477474833517 4961552695007054053062569)
                    ·
                      refine ⟨3721164521255290539796927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4961552695007054053062569 3721164521255290539796927)
                      ·
                        rfl

theorem cell23_7246942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 1, 2, 2, 3, 2].length) (baseStart_7246942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7246942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7246942 prefixEnd_7246942 := by exact prefixLift 7246942
  have htrace : WordTrace (prefixWord ++ tailWord_7246942) baseStart_7246942 baseEnd_7246942 := by
    simpa [prefixWord, tailWord_7246942, baseEnd_7246942] using wordTrace_append hprefix tailTrace_7246942
  have hstable : (prefixWord ++ tailWord_7246942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7246942).length < 2 ^ (prefixWord ++ tailWord_7246942).sum := by decide
  have hdescent : baseEnd_7246942 < baseStart_7246942 := by decide
  rcases family_descends (prefixWord ++ tailWord_7246942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7246965 : List Nat := [1, 3, 4, 3, 1, 1, 1, 3, 2, 4]
def baseStart_7246965 : Nat := 118140960795 + 7246965 * 2 ^ 59
def prefixEnd_7246965 : Nat := 4983230072969 + 3 ^ 40 * 7246965 * 2
def baseEnd_7246965 : Nat := 1240392110436781316603107

theorem tailTrace_7246965 : CollatzResearch.WordTrace tailWord_7246965 prefixEnd_7246965 1240392110436781316603107 := by
  unfold tailWord_7246965
  simp only [CollatzResearch.WordTrace]
  refine ⟨264318528190490962930126349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176212352126993975286750899 264318528190490962930126349)
  ·
    refine ⟨99119448071434111098797381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 264318528190490962930126349 99119448071434111098797381)
    ·
      refine ⟨18584896513393895831024509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 99119448071434111098797381 18584896513393895831024509)
      ·
        refine ⟨6969336192522710936634191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18584896513393895831024509 6969336192522710936634191)
        ·
          refine ⟨10454004288784066404951287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6969336192522710936634191 10454004288784066404951287)
          ·
            refine ⟨15681006433176099607426931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10454004288784066404951287 15681006433176099607426931)
            ·
              refine ⟨23521509649764149411140397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15681006433176099607426931 23521509649764149411140397)
              ·
                refine ⟨8820566118661556029177649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23521509649764149411140397 8820566118661556029177649)
                ·
                  refine ⟨6615424588996167021883237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8820566118661556029177649 6615424588996167021883237)
                  ·
                    refine ⟨1240392110436781316603107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6615424588996167021883237 1240392110436781316603107)
                    ·
                      rfl

theorem cell23_7246965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 1, 3, 2, 4].length) (baseStart_7246965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7246965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7246965 prefixEnd_7246965 := by exact prefixLift 7246965
  have htrace : WordTrace (prefixWord ++ tailWord_7246965) baseStart_7246965 baseEnd_7246965 := by
    simpa [prefixWord, tailWord_7246965, baseEnd_7246965] using wordTrace_append hprefix tailTrace_7246965
  have hstable : (prefixWord ++ tailWord_7246965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7246965).length < 2 ^ (prefixWord ++ tailWord_7246965).sum := by decide
  have hdescent : baseEnd_7246965 < baseStart_7246965 := by decide
  rcases family_descends (prefixWord ++ tailWord_7246965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7247006 : List Nat := [4, 3, 1, 1, 2, 3, 2, 2, 1, 2, 2]
def baseStart_7247006 : Nat := 118140960795 + 7247006 * 2 ^ 59
def prefixEnd_7247006 : Nat := 4983230072969 + 3 ^ 40 * 7247006 * 2
def baseEnd_7247006 : Nat := 3721197384017178289396633

theorem tailTrace_7247006 : CollatzResearch.WordTrace tailWord_7247006 prefixEnd_7247006 3721197384017178289396633 := by
  unfold tailWord_7247006
  simp only [CollatzResearch.WordTrace]
  refine ⟨33040002947917803366546109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 176213349055561617954912581 33040002947917803366546109)
  ·
    refine ⟨12390001105469176262454791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33040002947917803366546109 12390001105469176262454791)
    ·
      refine ⟨18585001658203764393682187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12390001105469176262454791 18585001658203764393682187)
      ·
        refine ⟨27877502487305646590523281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18585001658203764393682187 27877502487305646590523281)
        ·
          refine ⟨20908126865479234942892461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27877502487305646590523281 20908126865479234942892461)
          ·
            refine ⟨7840547574554713103584673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20908126865479234942892461 7840547574554713103584673)
            ·
              refine ⟨5880410680916034827688505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7840547574554713103584673 5880410680916034827688505)
              ·
                refine ⟨4410308010687026120766379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5880410680916034827688505 4410308010687026120766379)
                ·
                  refine ⟨6615462016030539181149569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4410308010687026120766379 6615462016030539181149569)
                  ·
                    refine ⟨4961596512022904385862177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6615462016030539181149569 4961596512022904385862177)
                    ·
                      refine ⟨3721197384017178289396633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4961596512022904385862177 3721197384017178289396633)
                      ·
                        rfl

theorem cell23_7247006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 3, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 3, 2, 2, 1, 2, 2].length) (baseStart_7247006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7247006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7247006 prefixEnd_7247006 := by exact prefixLift 7247006
  have htrace : WordTrace (prefixWord ++ tailWord_7247006) baseStart_7247006 baseEnd_7247006 := by
    simpa [prefixWord, tailWord_7247006, baseEnd_7247006] using wordTrace_append hprefix tailTrace_7247006
  have hstable : (prefixWord ++ tailWord_7247006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7247006).length < 2 ^ (prefixWord ++ tailWord_7247006).sum := by decide
  have hdescent : baseEnd_7247006 < baseStart_7247006 := by decide
  rcases family_descends (prefixWord ++ tailWord_7247006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7247024 : List Nat := [2, 1, 1, 1, 2, 1, 2, 5, 2, 2, 4]
def baseStart_7247024 : Nat := 118140960795 + 7247024 * 2 ^ 59
def prefixEnd_7247024 : Nat := 4983230072969 + 3 ^ 40 * 7247024 * 2
def baseEnd_7247024 : Nat := 3721206626668959218971549

theorem tailTrace_7247024 : CollatzResearch.WordTrace tailWord_7247024 prefixEnd_7247024 3721206626668959218971549 := by
  unfold tailWord_7247024
  simp only [CollatzResearch.WordTrace]
  refine ⟨132160340048638608003262063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176213786731518144004349417 132160340048638608003262063)
  ·
    refine ⟨198240510072957912004893095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132160340048638608003262063 198240510072957912004893095)
    ·
      refine ⟨297360765109436868007339643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198240510072957912004893095 297360765109436868007339643)
      ·
        refine ⟨446041147664155302011009465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 297360765109436868007339643 446041147664155302011009465)
        ·
          refine ⟨334530860748116476508257099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 446041147664155302011009465 334530860748116476508257099)
          ·
            refine ⟨501796291122174714762385649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 334530860748116476508257099 501796291122174714762385649)
            ·
              refine ⟨376347218341631036071789237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 501796291122174714762385649 376347218341631036071789237)
              ·
                refine ⟨35282551719527909631730241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 376347218341631036071789237 35282551719527909631730241)
                ·
                  refine ⟨26461913789645932223797681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35282551719527909631730241 26461913789645932223797681)
                  ·
                    refine ⟨19846435342234449167848261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26461913789645932223797681 19846435342234449167848261)
                    ·
                      refine ⟨3721206626668959218971549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19846435342234449167848261 3721206626668959218971549)
                      ·
                        rfl

theorem cell23_7247024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 5, 2, 2, 4].length) (baseStart_7247024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7247024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7247024 prefixEnd_7247024 := by exact prefixLift 7247024
  have htrace : WordTrace (prefixWord ++ tailWord_7247024) baseStart_7247024 baseEnd_7247024 := by
    simpa [prefixWord, tailWord_7247024, baseEnd_7247024] using wordTrace_append hprefix tailTrace_7247024
  have hstable : (prefixWord ++ tailWord_7247024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7247024).length < 2 ^ (prefixWord ++ tailWord_7247024).sum := by decide
  have hdescent : baseEnd_7247024 < baseStart_7247024 := by decide
  rcases family_descends (prefixWord ++ tailWord_7247024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7247071 : List Nat := [1, 1, 2, 3, 2, 1, 2, 1, 1, 7, 2]
def baseStart_7247071 : Nat := 118140960795 + 7247071 * 2 ^ 59
def prefixEnd_7247071 : Nat := 4983230072969 + 3 ^ 40 * 7247071 * 2
def baseEnd_7247071 : Nat := 3721230760259720535083833

theorem tailTrace_7247071 : CollatzResearch.WordTrace tailWord_7247071 prefixEnd_7247071 3721230760259720535083833 := by
  unfold tailWord_7247071
  simp only [CollatzResearch.WordTrace]
  refine ⟨264322394328106943033485067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176214929552071295355656711 264322394328106943033485067)
  ·
    refine ⟨396483591492160414550227601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264322394328106943033485067 396483591492160414550227601)
    ·
      refine ⟨297362693619120310912670701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 396483591492160414550227601 297362693619120310912670701)
      ·
        refine ⟨111511010107170116592251513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 297362693619120310912670701 111511010107170116592251513)
        ·
          refine ⟨83633257580377587444188635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111511010107170116592251513 83633257580377587444188635)
          ·
            refine ⟨125449886370566381166282953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83633257580377587444188635 125449886370566381166282953)
            ·
              refine ⟨94087414777924785874712215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 125449886370566381166282953 94087414777924785874712215)
              ·
                refine ⟨141131122166887178812068323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94087414777924785874712215 141131122166887178812068323)
                ·
                  refine ⟨211696683250330768218102485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 141131122166887178812068323 211696683250330768218102485)
                  ·
                    refine ⟨4961641013679627380111777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 211696683250330768218102485 4961641013679627380111777)
                    ·
                      refine ⟨3721230760259720535083833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4961641013679627380111777 3721230760259720535083833)
                      ·
                        rfl

theorem cell23_7247071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 1, 1, 7, 2].length) (baseStart_7247071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7247071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7247071 prefixEnd_7247071 := by exact prefixLift 7247071
  have htrace : WordTrace (prefixWord ++ tailWord_7247071) baseStart_7247071 baseEnd_7247071 := by
    simpa [prefixWord, tailWord_7247071, baseEnd_7247071] using wordTrace_append hprefix tailTrace_7247071
  have hstable : (prefixWord ++ tailWord_7247071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7247071).length < 2 ^ (prefixWord ++ tailWord_7247071).sum := by decide
  have hdescent : baseEnd_7247071 < baseStart_7247071 := by decide
  rcases family_descends (prefixWord ++ tailWord_7247071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7247079 : List Nat := [1, 1, 5, 3, 2, 1, 3, 1, 2, 2, 2]
def baseStart_7247079 : Nat := 118140960795 + 7247079 * 2 ^ 59
def prefixEnd_7247079 : Nat := 4983230072969 + 3 ^ 40 * 7247079 * 2
def baseEnd_7247079 : Nat := 3721234868104956503783797

theorem tailTrace_7247079 : CollatzResearch.WordTrace tailWord_7247079 prefixEnd_7247079 3721234868104956503783797 := by
  unfold tailWord_7247079
  simp only [CollatzResearch.WordTrace]
  refine ⟨264322686112077960399776291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176215124074718640266517527 264322686112077960399776291)
  ·
    refine ⟨396484029168116940599664437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264322686112077960399776291 396484029168116940599664437)
    ·
      refine ⟨37170377734510963181218541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 396484029168116940599664437 37170377734510963181218541)
      ·
        refine ⟨13938891650441611192956953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37170377734510963181218541 13938891650441611192956953)
        ·
          refine ⟨10454168737831208394717715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13938891650441611192956953 10454168737831208394717715)
          ·
            refine ⟨15681253106746812592076573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10454168737831208394717715 15681253106746812592076573)
            ·
              refine ⟨5880469915030054722028715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15681253106746812592076573 5880469915030054722028715)
              ·
                refine ⟨8820704872545082083043073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5880469915030054722028715 8820704872545082083043073)
                ·
                  refine ⟨6615528654408811562282305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8820704872545082083043073 6615528654408811562282305)
                  ·
                    refine ⟨4961646490806608671711729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6615528654408811562282305 4961646490806608671711729)
                    ·
                      refine ⟨3721234868104956503783797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4961646490806608671711729 3721234868104956503783797)
                      ·
                        rfl

theorem cell23_7247079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 3, 1, 2, 2, 2].length) (baseStart_7247079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7247079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7247079 prefixEnd_7247079 := by exact prefixLift 7247079
  have htrace : WordTrace (prefixWord ++ tailWord_7247079) baseStart_7247079 baseEnd_7247079 := by
    simpa [prefixWord, tailWord_7247079, baseEnd_7247079] using wordTrace_append hprefix tailTrace_7247079
  have hstable : (prefixWord ++ tailWord_7247079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7247079).length < 2 ^ (prefixWord ++ tailWord_7247079).sum := by decide
  have hdescent : baseEnd_7247079 < baseStart_7247079 := by decide
  rcases family_descends (prefixWord ++ tailWord_7247079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7247104 : List Nat := [2, 1, 1, 2, 1, 1, 3, 2, 2, 3, 5]
def baseStart_7247104 : Nat := 118140960795 + 7247104 * 2 ^ 59
def prefixEnd_7247104 : Nat := 4983230072969 + 3 ^ 40 * 7247104 * 2
def baseEnd_7247104 : Nat := 3721247705121318905971181

theorem tailTrace_7247104 : CollatzResearch.WordTrace tailWord_7247104 prefixEnd_7247104 3721247705121318905971181 := by
  unfold tailWord_7247104
  simp only [CollatzResearch.WordTrace]
  refine ⟨132161798968493694834718183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176215731957991593112957577 132161798968493694834718183)
  ·
    refine ⟨198242698452740542252077275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132161798968493694834718183 198242698452740542252077275)
    ·
      refine ⟨297364047679110813378115913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198242698452740542252077275 297364047679110813378115913)
      ·
        refine ⟨223023035759333110033586935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 297364047679110813378115913 223023035759333110033586935)
        ·
          refine ⟨334534553638999665050380403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 223023035759333110033586935 334534553638999665050380403)
          ·
            refine ⟨501801830458499497575570605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 334534553638999665050380403 501801830458499497575570605)
            ·
              refine ⟨188175686421937311590838977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 501801830458499497575570605 188175686421937311590838977)
              ·
                refine ⟨141131764816452983693129233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 188175686421937311590838977 141131764816452983693129233)
                ·
                  refine ⟨105848823612339737769846925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 141131764816452983693129233 105848823612339737769846925)
                  ·
                    refine ⟨39693308854627401663692597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 105848823612339737769846925 39693308854627401663692597)
                    ·
                      refine ⟨3721247705121318905971181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39693308854627401663692597 3721247705121318905971181)
                      ·
                        rfl

theorem cell23_7247104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 2, 2, 3, 5].length) (baseStart_7247104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7247104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7247104 prefixEnd_7247104 := by exact prefixLift 7247104
  have htrace : WordTrace (prefixWord ++ tailWord_7247104) baseStart_7247104 baseEnd_7247104 := by
    simpa [prefixWord, tailWord_7247104, baseEnd_7247104] using wordTrace_append hprefix tailTrace_7247104
  have hstable : (prefixWord ++ tailWord_7247104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7247104).length < 2 ^ (prefixWord ++ tailWord_7247104).sum := by decide
  have hdescent : baseEnd_7247104 < baseStart_7247104 := by decide
  rcases family_descends (prefixWord ++ tailWord_7247104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
