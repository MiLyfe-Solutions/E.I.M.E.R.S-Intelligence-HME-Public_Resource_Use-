import V185TrunkScan22Chunk126

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_1136398 : List Nat := [4, 1, 1, 2, 1, 1, 2, 4, 6]
def baseStart_1136398 : Nat := 118140960795 + 1136398 * 2 ^ 59
def prefixEnd_1136398 : Nat := 4983230072969 + 3 ^ 40 * 1136398 * 2
def baseEnd_1136398 : Nat := 129670753068477793621957

theorem tailTrace_1136398 : CollatzResearch.WordTrace tailWord_1136398 prefixEnd_1136398 129670753068477793621957 := by
  unfold tailWord_1136398
  simp only [CollatzResearch.WordTrace]
  refine ⟨5180980017128950271488231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27631893424687734781270565 5180980017128950271488231)
  ·
    refine ⟨7771470025693425407232347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5180980017128950271488231 7771470025693425407232347)
    ·
      refine ⟨11657205038540138110848521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7771470025693425407232347 11657205038540138110848521)
      ·
        refine ⟨8742903778905103583136391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11657205038540138110848521 8742903778905103583136391)
        ·
          refine ⟨13114355668357655374704587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8742903778905103583136391 13114355668357655374704587)
          ·
            refine ⟨19671533502536483062056881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13114355668357655374704587 19671533502536483062056881)
            ·
              refine ⟨14753650126902362296542661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19671533502536483062056881 14753650126902362296542661)
              ·
                refine ⟨2766309398794192930601749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14753650126902362296542661 2766309398794192930601749)
                ·
                  refine ⟨129670753068477793621957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2766309398794192930601749 129670753068477793621957)
                  ·
                    rfl

theorem cell22_1136398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 4, 6].length) (baseStart_1136398 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1136398 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1136398 prefixEnd_1136398 := by exact prefixLift 1136398
  have htrace : WordTrace (prefixWord ++ tailWord_1136398) baseStart_1136398 baseEnd_1136398 := by
    simpa [prefixWord, tailWord_1136398, baseEnd_1136398] using wordTrace_append hprefix tailTrace_1136398
  have hstable : (prefixWord ++ tailWord_1136398).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1136398).length < 2 ^ (prefixWord ++ tailWord_1136398).sum := by decide
  have hdescent : baseEnd_1136398 < baseStart_1136398 := by decide
  rcases family_descends (prefixWord ++ tailWord_1136398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1136415 : List Nat := [1, 1, 2, 4, 2, 1, 2, 5, 4]
def baseStart_1136415 : Nat := 118140960795 + 1136415 * 2 ^ 59
def prefixEnd_1136415 : Nat := 4983230072969 + 3 ^ 40 * 1136415 * 2
def baseEnd_1136415 : Nat := 129672692884283667730273

theorem tailTrace_1136415 : CollatzResearch.WordTrace tailWord_1136415 prefixEnd_1136415 129672692884283667730273 := by
  unfold tailWord_1136415
  simp only [CollatzResearch.WordTrace]
  refine ⟨41448460177970014075274699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27632306785313342716849799 41448460177970014075274699)
  ·
    refine ⟨62172690266955021112912049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41448460177970014075274699 62172690266955021112912049)
    ·
      refine ⟨46629517700216265834684037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62172690266955021112912049 46629517700216265834684037)
      ·
        refine ⟨8743034568790549844003257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 46629517700216265834684037 8743034568790549844003257)
        ·
          refine ⟨6557275926592912383002443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8743034568790549844003257 6557275926592912383002443)
          ·
            refine ⟨9835913889889368574503665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6557275926592912383002443 9835913889889368574503665)
            ·
              refine ⟨7376935417417026430877749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9835913889889368574503665 7376935417417026430877749)
              ·
                refine ⟨691587695382846227894789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7376935417417026430877749 691587695382846227894789)
                ·
                  refine ⟨129672692884283667730273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 691587695382846227894789 129672692884283667730273)
                  ·
                    rfl

theorem cell22_1136415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 2, 5, 4].length) (baseStart_1136415 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1136415 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1136415 prefixEnd_1136415 := by exact prefixLift 1136415
  have htrace : WordTrace (prefixWord ++ tailWord_1136415) baseStart_1136415 baseEnd_1136415 := by
    simpa [prefixWord, tailWord_1136415, baseEnd_1136415] using wordTrace_append hprefix tailTrace_1136415
  have hstable : (prefixWord ++ tailWord_1136415).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1136415).length < 2 ^ (prefixWord ++ tailWord_1136415).sum := by decide
  have hdescent : baseEnd_1136415 < baseStart_1136415 := by decide
  rcases family_descends (prefixWord ++ tailWord_1136415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1136417 : List Nat := [1, 2, 3, 2, 1, 4, 3, 1, 1, 4]
def baseStart_1136417 : Nat := 118140960795 + 1136417 * 2 ^ 59
def prefixEnd_1136417 : Nat := 4983230072969 + 3 ^ 40 * 1136417 * 2
def baseEnd_1136417 : Nat := 389018763293723664640813

theorem tailTrace_1136417 : CollatzResearch.WordTrace tailWord_1136417 prefixEnd_1136417 389018763293723664640813 := by
  unfold tailWord_1136417
  simp only [CollatzResearch.WordTrace]
  refine ⟨41448533123962768416847505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27632355415975178944565003 41448533123962768416847505)
  ·
    refine ⟨31086399842972076312635629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41448533123962768416847505 31086399842972076312635629)
    ·
      refine ⟨11657399941114528617238361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31086399842972076312635629 11657399941114528617238361)
      ·
        refine ⟨8743049955835896462928771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11657399941114528617238361 8743049955835896462928771)
        ·
          refine ⟨13114574933753844694393157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8743049955835896462928771 13114574933753844694393157)
          ·
            refine ⟨2458982800078845880198717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13114574933753844694393157 2458982800078845880198717)
            ·
              refine ⟨922118550029567205074519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2458982800078845880198717 922118550029567205074519)
              ·
                refine ⟨1383177825044350807611779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 922118550029567205074519 1383177825044350807611779)
                ·
                  refine ⟨2074766737566526211417669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1383177825044350807611779 2074766737566526211417669)
                  ·
                    refine ⟨389018763293723664640813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2074766737566526211417669 389018763293723664640813)
                    ·
                      rfl

theorem cell22_1136417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 3, 1, 1, 4].length) (baseStart_1136417 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1136417 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1136417 prefixEnd_1136417 := by exact prefixLift 1136417
  have htrace : WordTrace (prefixWord ++ tailWord_1136417) baseStart_1136417 baseEnd_1136417 := by
    simpa [prefixWord, tailWord_1136417, baseEnd_1136417] using wordTrace_append hprefix tailTrace_1136417
  have hstable : (prefixWord ++ tailWord_1136417).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1136417).length < 2 ^ (prefixWord ++ tailWord_1136417).sum := by decide
  have hdescent : baseEnd_1136417 < baseStart_1136417 := by decide
  rcases family_descends (prefixWord ++ tailWord_1136417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1136492 : List Nat := [2, 2, 1, 1, 4, 3, 2, 1, 3, 3]
def baseStart_1136492 : Nat := 118140960795 + 1136492 * 2 ^ 59
def prefixEnd_1136492 : Nat := 4983230072969 + 3 ^ 40 * 1136492 * 2
def baseEnd_1136492 : Nat := 389044437326448469015583

theorem tailTrace_1136492 : CollatzResearch.WordTrace tailWord_1136492 prefixEnd_1136492 389044437326448469015583 := by
  unfold tailWord_1136492
  simp only [CollatzResearch.WordTrace]
  refine ⟨20725634299345528112913865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27634179065794037483885153 20725634299345528112913865)
  ·
    refine ⟨15544225724509146084685399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20725634299345528112913865 15544225724509146084685399)
    ·
      refine ⟨23316338586763719127028099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15544225724509146084685399 23316338586763719127028099)
      ·
        refine ⟨34974507880145578690542149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23316338586763719127028099 34974507880145578690542149)
        ·
          refine ⟨6557720227527296004476653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 34974507880145578690542149 6557720227527296004476653)
          ·
            refine ⟨2459145085322736001678745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6557720227527296004476653 2459145085322736001678745)
            ·
              refine ⟨1844358813992052001259059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2459145085322736001678745 1844358813992052001259059)
              ·
                refine ⟨2766538220988078001888589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1844358813992052001259059 2766538220988078001888589)
                ·
                  refine ⟨1037451832870529250708221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2766538220988078001888589 1037451832870529250708221)
                  ·
                    refine ⟨389044437326448469015583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1037451832870529250708221 389044437326448469015583)
                    ·
                      rfl

theorem cell22_1136492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 3, 3].length) (baseStart_1136492 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1136492 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1136492 prefixEnd_1136492 := by exact prefixLift 1136492
  have htrace : WordTrace (prefixWord ++ tailWord_1136492) baseStart_1136492 baseEnd_1136492 := by
    simpa [prefixWord, tailWord_1136492, baseEnd_1136492] using wordTrace_append hprefix tailTrace_1136492
  have hstable : (prefixWord ++ tailWord_1136492).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1136492).length < 2 ^ (prefixWord ++ tailWord_1136492).sum := by decide
  have hdescent : baseEnd_1136492 < baseStart_1136492 := by decide
  rcases family_descends (prefixWord ++ tailWord_1136492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1136597 : List Nat := [1, 3, 2, 3, 2, 1, 2, 2, 2, 4]
def baseStart_1136597 : Nat := 118140960795 + 1136597 * 2 ^ 59
def prefixEnd_1136597 : Nat := 4983230072969 + 3 ^ 40 * 1136597 * 2
def baseEnd_1136597 : Nat := 389080380972263195140261

theorem tailTrace_1136597 : CollatzResearch.WordTrace tailWord_1136597 prefixEnd_1136597 389080380972263195140261 := by
  unfold tailWord_1136597
  simp only [CollatzResearch.WordTrace]
  refine ⟨41455098263310659158400045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27636732175540439438933363 41455098263310659158400045)
  ·
    refine ⟨15545661848741497184400017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41455098263310659158400045 15545661848741497184400017)
    ·
      refine ⟨11659246386556122888300013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15545661848741497184400017 11659246386556122888300013)
      ·
        refine ⟨4372217394958546083112505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11659246386556122888300013 4372217394958546083112505)
        ·
          refine ⟨3279163046218909562334379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4372217394958546083112505 3279163046218909562334379)
          ·
            refine ⟨4918744569328364343501569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3279163046218909562334379 4918744569328364343501569)
            ·
              refine ⟨3689058426996273257626177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4918744569328364343501569 3689058426996273257626177)
              ·
                refine ⟨2766793820247204943219633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3689058426996273257626177 2766793820247204943219633)
                ·
                  refine ⟨2075095365185403707414725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2766793820247204943219633 2075095365185403707414725)
                  ·
                    refine ⟨389080380972263195140261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2075095365185403707414725 389080380972263195140261)
                    ·
                      rfl

theorem cell22_1136597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 2, 2, 2, 4].length) (baseStart_1136597 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1136597 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1136597 prefixEnd_1136597 := by exact prefixLift 1136597
  have htrace : WordTrace (prefixWord ++ tailWord_1136597) baseStart_1136597 baseEnd_1136597 := by
    simpa [prefixWord, tailWord_1136597, baseEnd_1136597] using wordTrace_append hprefix tailTrace_1136597
  have hstable : (prefixWord ++ tailWord_1136597).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1136597).length < 2 ^ (prefixWord ++ tailWord_1136597).sum := by decide
  have hdescent : baseEnd_1136597 < baseStart_1136597 := by decide
  rcases family_descends (prefixWord ++ tailWord_1136597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1136601 : List Nat := [1, 2, 1, 2, 6, 2, 2, 2, 4]
def baseStart_1136601 : Nat := 118140960795 + 1136601 * 2 ^ 59
def prefixEnd_1136601 : Nat := 4983230072969 + 3 ^ 40 * 1136601 * 2
def baseEnd_1136601 : Nat := 129693916751336172680083

theorem tailTrace_1136601 : CollatzResearch.WordTrace tailWord_1136601 prefixEnd_1136601 129693916751336172680083 := by
  unfold tailWord_1136601
  simp only [CollatzResearch.WordTrace]
  refine ⟨41455244155296167841545657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27636829436864111894363771 41455244155296167841545657)
  ·
    refine ⟨31091433116472125881159243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41455244155296167841545657 31091433116472125881159243)
    ·
      refine ⟨46637149674708188821738865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31091433116472125881159243 46637149674708188821738865)
      ·
        refine ⟨34977862256031141616304149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46637149674708188821738865 34977862256031141616304149)
        ·
          refine ⟨1639587293251459763264257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 34977862256031141616304149 1639587293251459763264257)
          ·
            refine ⟨1229690469938594822448193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1639587293251459763264257 1229690469938594822448193)
            ·
              refine ⟨922267852453946116836145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1229690469938594822448193 922267852453946116836145)
              ·
                refine ⟨691700889340459587627109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 922267852453946116836145 691700889340459587627109)
                ·
                  refine ⟨129693916751336172680083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 691700889340459587627109 129693916751336172680083)
                  ·
                    rfl

theorem cell22_1136601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 2, 2, 2, 4].length) (baseStart_1136601 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1136601 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1136601 prefixEnd_1136601 := by exact prefixLift 1136601
  have htrace : WordTrace (prefixWord ++ tailWord_1136601) baseStart_1136601 baseEnd_1136601 := by
    simpa [prefixWord, tailWord_1136601, baseEnd_1136601] using wordTrace_append hprefix tailTrace_1136601
  have hstable : (prefixWord ++ tailWord_1136601).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1136601).length < 2 ^ (prefixWord ++ tailWord_1136601).sum := by decide
  have hdescent : baseEnd_1136601 < baseStart_1136601 := by decide
  rcases family_descends (prefixWord ++ tailWord_1136601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1136674 : List Nat := [3, 3, 1, 1, 1, 2, 5, 1, 5]
def baseStart_1136674 : Nat := 118140960795 + 1136674 * 2 ^ 59
def prefixEnd_1136674 : Nat := 4983230072969 + 3 ^ 40 * 1136674 * 2
def baseEnd_1136674 : Nat := 129702246548620220321675

theorem tailTrace_1136674 : CollatzResearch.WordTrace tailWord_1136674 prefixEnd_1136674 129702246548620220321675 := by
  unfold tailWord_1136674
  simp only [CollatzResearch.WordTrace]
  refine ⟨10364476671007925327238269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27638604456021134205968717 10364476671007925327238269)
  ·
    refine ⟨3886678751627971997714351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10364476671007925327238269 3886678751627971997714351)
    ·
      refine ⟨5830018127441957996571527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3886678751627971997714351 5830018127441957996571527)
      ·
        refine ⟨8745027191162936994857291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5830018127441957996571527 8745027191162936994857291)
        ·
          refine ⟨13117540786744405492285937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8745027191162936994857291 13117540786744405492285937)
          ·
            refine ⟨9838155590058304119214453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13117540786744405492285937 9838155590058304119214453)
            ·
              refine ⟨922327086567966011176355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9838155590058304119214453 922327086567966011176355)
              ·
                refine ⟨1383490629851949016764533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 922327086567966011176355 1383490629851949016764533)
                ·
                  refine ⟨129702246548620220321675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1383490629851949016764533 129702246548620220321675)
                  ·
                    rfl

theorem cell22_1136674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 5, 1, 5].length) (baseStart_1136674 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1136674 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1136674 prefixEnd_1136674 := by exact prefixLift 1136674
  have htrace : WordTrace (prefixWord ++ tailWord_1136674) baseStart_1136674 baseEnd_1136674 := by
    simpa [prefixWord, tailWord_1136674, baseEnd_1136674] using wordTrace_append hprefix tailTrace_1136674
  have hstable : (prefixWord ++ tailWord_1136674).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1136674).length < 2 ^ (prefixWord ++ tailWord_1136674).sum := by decide
  have hdescent : baseEnd_1136674 < baseStart_1136674 := by decide
  rcases family_descends (prefixWord ++ tailWord_1136674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1136738 : List Nat := [3, 3, 2, 2, 2, 2, 1, 2, 1, 4]
def baseStart_1136738 : Nat := 118140960795 + 1136738 * 2 ^ 59
def prefixEnd_1136738 : Nat := 4983230072969 + 3 ^ 40 * 1136738 * 2
def baseEnd_1136738 : Nat := 389128648153785827364829

theorem tailTrace_1136738 : CollatzResearch.WordTrace tailWord_1136738 prefixEnd_1136738 389128648153785827364829 := by
  unfold tailWord_1136738
  simp only [CollatzResearch.WordTrace]
  refine ⟨10365060238949960059820717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27640160637199893492855245 10365060238949960059820717)
  ·
    refine ⟨3886897589606235022432769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10365060238949960059820717 3886897589606235022432769)
    ·
      refine ⟨2915173192204676266824577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3886897589606235022432769 2915173192204676266824577)
      ·
        refine ⟨2186379894153507200118433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2915173192204676266824577 2186379894153507200118433)
        ·
          refine ⟨1639784920615130400088825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2186379894153507200118433 1639784920615130400088825)
          ·
            refine ⟨1229838690461347800066619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1639784920615130400088825 1229838690461347800066619)
            ·
              refine ⟨1844758035692021700099929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1229838690461347800066619 1844758035692021700099929)
              ·
                refine ⟨1383568526769016275074947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1844758035692021700099929 1383568526769016275074947)
                ·
                  refine ⟨2075352790153524412612421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1383568526769016275074947 2075352790153524412612421)
                  ·
                    refine ⟨389128648153785827364829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2075352790153524412612421 389128648153785827364829)
                    ·
                      rfl

theorem cell22_1136738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 2, 1, 2, 1, 4].length) (baseStart_1136738 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1136738 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1136738 prefixEnd_1136738 := by exact prefixLift 1136738
  have htrace : WordTrace (prefixWord ++ tailWord_1136738) baseStart_1136738 baseEnd_1136738 := by
    simpa [prefixWord, tailWord_1136738, baseEnd_1136738] using wordTrace_append hprefix tailTrace_1136738
  have hstable : (prefixWord ++ tailWord_1136738).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1136738).length < 2 ^ (prefixWord ++ tailWord_1136738).sum := by decide
  have hdescent : baseEnd_1136738 < baseStart_1136738 := by decide
  rcases family_descends (prefixWord ++ tailWord_1136738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1136749 : List Nat := [1, 5, 1, 1, 2, 1, 4, 1, 2, 4]
def baseStart_1136749 : Nat := 118140960795 + 1136749 * 2 ^ 59
def prefixEnd_1136749 : Nat := 4983230072969 + 3 ^ 40 * 1136749 * 2
def baseEnd_1136749 : Nat := 389132413678585465339795

theorem tailTrace_1136749 : CollatzResearch.WordTrace tailWord_1136749 prefixEnd_1136749 389132413678585465339795 := by
  unfold tailWord_1136749
  simp only [CollatzResearch.WordTrace]
  refine ⟨41460642158759989117933301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27640428105839992745288867 41460642158759989117933301)
  ·
    refine ⟨3886935202383748979806247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 41460642158759989117933301 3886935202383748979806247)
    ·
      refine ⟨5830402803575623469709371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3886935202383748979806247 5830402803575623469709371)
      ·
        refine ⟨8745604205363435204564057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5830402803575623469709371 8745604205363435204564057)
        ·
          refine ⟨6559203154022576403423043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8745604205363435204564057 6559203154022576403423043)
          ·
            refine ⟨9838804731033864605134565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6559203154022576403423043 9838804731033864605134565)
            ·
              refine ⟨1844775887068849613462731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9838804731033864605134565 1844775887068849613462731)
              ·
                refine ⟨2767163830603274420194097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1844775887068849613462731 2767163830603274420194097)
                ·
                  refine ⟨2075372872952455815145573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2767163830603274420194097 2075372872952455815145573)
                  ·
                    refine ⟨389132413678585465339795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2075372872952455815145573 389132413678585465339795)
                    ·
                      rfl

theorem cell22_1136749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 4, 1, 2, 4].length) (baseStart_1136749 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1136749 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1136749 prefixEnd_1136749 := by exact prefixLift 1136749
  have htrace : WordTrace (prefixWord ++ tailWord_1136749) baseStart_1136749 baseEnd_1136749 := by
    simpa [prefixWord, tailWord_1136749, baseEnd_1136749] using wordTrace_append hprefix tailTrace_1136749
  have hstable : (prefixWord ++ tailWord_1136749).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1136749).length < 2 ^ (prefixWord ++ tailWord_1136749).sum := by decide
  have hdescent : baseEnd_1136749 < baseStart_1136749 := by decide
  rcases family_descends (prefixWord ++ tailWord_1136749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1136813 : List Nat := [1, 5, 2, 1, 2, 1, 1, 5, 1, 3]
def baseStart_1136813 : Nat := 118140960795 + 1136813 * 2 ^ 59
def prefixEnd_1136813 : Nat := 4983230072969 + 3 ^ 40 * 1136813 * 2
def baseEnd_1136813 : Nat := 389154322186510631739599

theorem tailTrace_1136813 : CollatzResearch.WordTrace tailWord_1136813 prefixEnd_1136813 389154322186510631739599 := by
  unfold tailWord_1136813
  simp only [CollatzResearch.WordTrace]
  refine ⟨41462976430528128048263093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27641984287018752032175395 41462976430528128048263093)
  ·
    refine ⟨3887154040362012004524665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 41462976430528128048263093 3887154040362012004524665)
    ·
      refine ⟨2915365530271509003393499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3887154040362012004524665 2915365530271509003393499)
      ·
        refine ⟨4373048295407263505090249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2915365530271509003393499 4373048295407263505090249)
        ·
          refine ⟨3279786221555447628817687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4373048295407263505090249 3279786221555447628817687)
          ·
            refine ⟨4919679332333171443226531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3279786221555447628817687 4919679332333171443226531)
            ·
              refine ⟨7379518998499757164839797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4919679332333171443226531 7379518998499757164839797)
              ·
                refine ⟨691829906109352234203731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7379518998499757164839797 691829906109352234203731)
                ·
                  refine ⟨1037744859164028351305597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 691829906109352234203731 1037744859164028351305597)
                  ·
                    refine ⟨389154322186510631739599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1037744859164028351305597 389154322186510631739599)
                    ·
                      rfl

theorem cell22_1136813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 1, 5, 1, 3].length) (baseStart_1136813 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1136813 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1136813 prefixEnd_1136813 := by exact prefixLift 1136813
  have htrace : WordTrace (prefixWord ++ tailWord_1136813) baseStart_1136813 baseEnd_1136813 := by
    simpa [prefixWord, tailWord_1136813, baseEnd_1136813] using wordTrace_append hprefix tailTrace_1136813
  have hstable : (prefixWord ++ tailWord_1136813).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1136813).length < 2 ^ (prefixWord ++ tailWord_1136813).sum := by decide
  have hdescent : baseEnd_1136813 < baseStart_1136813 := by decide
  rcases family_descends (prefixWord ++ tailWord_1136813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1136837 : List Nat := [1, 3, 1, 1, 1, 1, 5, 3, 6]
def baseStart_1136837 : Nat := 118140960795 + 1136837 * 2 ^ 59
def prefixEnd_1136837 : Nat := 4983230072969 + 3 ^ 40 * 1136837 * 2
def baseEnd_1136837 : Nat := 129720845958994189713175

theorem tailTrace_1136837 : CollatzResearch.WordTrace tailWord_1136837 prefixEnd_1136837 129720845958994189713175 := by
  unfold tailWord_1136837
  simp only [CollatzResearch.WordTrace]
  refine ⟨41463851782441180147136765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27642567854960786764757843 41463851782441180147136765)
  ·
    refine ⟨15548944418415442555176287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41463851782441180147136765 15548944418415442555176287)
    ·
      refine ⟨23323416627623163832764431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15548944418415442555176287 23323416627623163832764431)
      ·
        refine ⟨34985124941434745749146647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23323416627623163832764431 34985124941434745749146647)
        ·
          refine ⟨52477687412152118623719971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34985124941434745749146647 52477687412152118623719971)
          ·
            refine ⟨78716531118228177935579957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52477687412152118623719971 78716531118228177935579957)
            ·
              refine ⟨7379674792333891681460621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 78716531118228177935579957 7379674792333891681460621)
              ·
                refine ⟨2767378047125209380547733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7379674792333891681460621 2767378047125209380547733)
                ·
                  refine ⟨129720845958994189713175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2767378047125209380547733 129720845958994189713175)
                  ·
                    rfl

theorem cell22_1136837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 5, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 5, 3, 6].length) (baseStart_1136837 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1136837 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1136837 prefixEnd_1136837 := by exact prefixLift 1136837
  have htrace : WordTrace (prefixWord ++ tailWord_1136837) baseStart_1136837 baseEnd_1136837 := by
    simpa [prefixWord, tailWord_1136837, baseEnd_1136837] using wordTrace_append hprefix tailTrace_1136837
  have hstable : (prefixWord ++ tailWord_1136837).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1136837).length < 2 ^ (prefixWord ++ tailWord_1136837).sum := by decide
  have hdescent : baseEnd_1136837 < baseStart_1136837 := by decide
  rcases family_descends (prefixWord ++ tailWord_1136837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1136856 : List Nat := [2, 1, 2, 2, 4, 2, 2, 2, 1, 4]
def baseStart_1136856 : Nat := 118140960795 + 1136856 * 2 ^ 59
def prefixEnd_1136856 : Nat := 4983230072969 + 3 ^ 40 * 1136856 * 2
def baseEnd_1136856 : Nat := 389169041965272852914467

theorem tailTrace_1136856 : CollatzResearch.WordTrace tailWord_1136856 prefixEnd_1136856 389169041965272852914467 := by
  unfold tailWord_1136856
  simp only [CollatzResearch.WordTrace]
  refine ⟨20732272384686173196039211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27643029846248230928052281 20732272384686173196039211)
  ·
    refine ⟨31098408577029259794058817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20732272384686173196039211 31098408577029259794058817)
    ·
      refine ⟨23323806432771944845544113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31098408577029259794058817 23323806432771944845544113)
      ·
        refine ⟨17492854824578958634158085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23323806432771944845544113 17492854824578958634158085)
        ·
          refine ⟨3279910279608554743904641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17492854824578958634158085 3279910279608554743904641)
          ·
            refine ⟨2459932709706416057928481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3279910279608554743904641 2459932709706416057928481)
            ·
              refine ⟨1844949532279812043446361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2459932709706416057928481 1844949532279812043446361)
              ·
                refine ⟨1383712149209859032584771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1844949532279812043446361 1383712149209859032584771)
                ·
                  refine ⟨2075568223814788548877157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1383712149209859032584771 2075568223814788548877157)
                  ·
                    refine ⟨389169041965272852914467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2075568223814788548877157 389169041965272852914467)
                    ·
                      rfl

theorem cell22_1136856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 2, 2, 1, 4].length) (baseStart_1136856 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1136856 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1136856 prefixEnd_1136856 := by exact prefixLift 1136856
  have htrace : WordTrace (prefixWord ++ tailWord_1136856) baseStart_1136856 baseEnd_1136856 := by
    simpa [prefixWord, tailWord_1136856, baseEnd_1136856] using wordTrace_append hprefix tailTrace_1136856
  have hstable : (prefixWord ++ tailWord_1136856).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1136856).length < 2 ^ (prefixWord ++ tailWord_1136856).sum := by decide
  have hdescent : baseEnd_1136856 < baseStart_1136856 := by decide
  rcases family_descends (prefixWord ++ tailWord_1136856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1136886 : List Nat := [5, 1, 1, 1, 1, 1, 4, 1, 4, 3]
def baseStart_1136886 : Nat := 118140960795 + 1136886 * 2 ^ 59
def prefixEnd_1136886 : Nat := 4983230072969 + 3 ^ 40 * 1136886 * 2
def baseEnd_1136886 : Nat := 389179311578362774664375

theorem tailTrace_1136886 : CollatzResearch.WordTrace tailWord_1136886 prefixEnd_1136886 389179311578362774664375 := by
  unfold tailWord_1136886
  simp only [CollatzResearch.WordTrace]
  refine ⟨2591602434953978844729407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 27643759306175774343780341 2591602434953978844729407)
  ·
    refine ⟨3887403652430968267094111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2591602434953978844729407 3887403652430968267094111)
    ·
      refine ⟨5831105478646452400641167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3887403652430968267094111 5831105478646452400641167)
      ·
        refine ⟨8746658217969678600961751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5831105478646452400641167 8746658217969678600961751)
        ·
          refine ⟨13119987326954517901442627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8746658217969678600961751 13119987326954517901442627)
          ·
            refine ⟨19679980990431776852163941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13119987326954517901442627 19679980990431776852163941)
            ·
              refine ⟨3689996435705958159780739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19679980990431776852163941 3689996435705958159780739)
              ·
                refine ⟨5534994653558937239671109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3689996435705958159780739 5534994653558937239671109)
                ·
                  refine ⟨1037811497542300732438333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5534994653558937239671109 1037811497542300732438333)
                  ·
                    refine ⟨389179311578362774664375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1037811497542300732438333 389179311578362774664375)
                    ·
                      rfl

theorem cell22_1136886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 4, 1, 4, 3].length) (baseStart_1136886 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1136886 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1136886 prefixEnd_1136886 := by exact prefixLift 1136886
  have htrace : WordTrace (prefixWord ++ tailWord_1136886) baseStart_1136886 baseEnd_1136886 := by
    simpa [prefixWord, tailWord_1136886, baseEnd_1136886] using wordTrace_append hprefix tailTrace_1136886
  have hstable : (prefixWord ++ tailWord_1136886).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1136886).length < 2 ^ (prefixWord ++ tailWord_1136886).sum := by decide
  have hdescent : baseEnd_1136886 < baseStart_1136886 := by decide
  rcases family_descends (prefixWord ++ tailWord_1136886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1136959 : List Nat := [1, 1, 2, 2, 4, 1, 3, 1, 2, 5]
def baseStart_1136959 : Nat := 118140960795 + 1136959 * 2 ^ 59
def prefixEnd_1136959 : Nat := 4983230072969 + 3 ^ 40 * 1136959 * 2
def baseEnd_1136959 : Nat := 389204300970214917589151

theorem tailTrace_1136959 : CollatzResearch.WordTrace tailWord_1136959 prefixEnd_1136959 389204300970214917589151 := by
  unfold tailWord_1136959
  simp only [CollatzResearch.WordTrace]
  refine ⟨41468301487999194983077931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27645534325332796655385287 41468301487999194983077931)
  ·
    refine ⟨62202452231998792474616897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41468301487999194983077931 62202452231998792474616897)
    ·
      refine ⟨46651839173999094355962673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62202452231998792474616897 46651839173999094355962673)
      ·
        refine ⟨34988879380499320766972005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46651839173999094355962673 34988879380499320766972005)
        ·
          refine ⟨6560414883843622643807251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 34988879380499320766972005 6560414883843622643807251)
          ·
            refine ⟨9840622325765433965710877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6560414883843622643807251 9840622325765433965710877)
            ·
              refine ⟨3690233372162037737141579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9840622325765433965710877 3690233372162037737141579)
              ·
                refine ⟨5535350058243056605712369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3690233372162037737141579 5535350058243056605712369)
                ·
                  refine ⟨4151512543682292454284277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5535350058243056605712369 4151512543682292454284277)
                  ·
                    refine ⟨389204300970214917589151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4151512543682292454284277 389204300970214917589151)
                    ·
                      rfl

theorem cell22_1136959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 3, 1, 2, 5].length) (baseStart_1136959 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1136959 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1136959 prefixEnd_1136959 := by exact prefixLift 1136959
  have htrace : WordTrace (prefixWord ++ tailWord_1136959) baseStart_1136959 baseEnd_1136959 := by
    simpa [prefixWord, tailWord_1136959, baseEnd_1136959] using wordTrace_append hprefix tailTrace_1136959
  have hstable : (prefixWord ++ tailWord_1136959).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1136959).length < 2 ^ (prefixWord ++ tailWord_1136959).sum := by decide
  have hdescent : baseEnd_1136959 < baseStart_1136959 := by decide
  rcases family_descends (prefixWord ++ tailWord_1136959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1137019 : List Nat := [1, 1, 1, 1, 1, 7, 1, 2, 1, 6]
def baseStart_1137019 : Nat := 118140960795 + 1137019 * 2 ^ 59
def prefixEnd_1137019 : Nat := 4983230072969 + 3 ^ 40 * 1137019 * 2
def baseEnd_1137019 : Nat := 389224840196394761088967

theorem tailTrace_1137019 : CollatzResearch.WordTrace tailWord_1137019 prefixEnd_1137019 389224840196394761088967 := by
  unfold tailWord_1137019
  simp only [CollatzResearch.WordTrace]
  refine ⟨41470489867781825230262111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27646993245187883486841407 41470489867781825230262111)
  ·
    refine ⟨62205734801672737845393167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41470489867781825230262111 62205734801672737845393167)
    ·
      refine ⟨93308602202509106768089751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62205734801672737845393167 93308602202509106768089751)
      ·
        refine ⟨139962903303763660152134627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93308602202509106768089751 139962903303763660152134627)
        ·
          refine ⟨209944354955645490228201941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 139962903303763660152134627 209944354955645490228201941)
          ·
            refine ⟨4920570819272941177223483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 209944354955645490228201941 4920570819272941177223483)
            ·
              refine ⟨7380856228909411765835225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4920570819272941177223483 7380856228909411765835225)
              ·
                refine ⟨5535642171682058824376419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7380856228909411765835225 5535642171682058824376419)
                ·
                  refine ⟨8303463257523088236564629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5535642171682058824376419 8303463257523088236564629)
                  ·
                    refine ⟨389224840196394761088967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8303463257523088236564629 389224840196394761088967)
                    ·
                      rfl

theorem cell22_1137019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 1, 2, 1, 6].length) (baseStart_1137019 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1137019 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1137019 prefixEnd_1137019 := by exact prefixLift 1137019
  have htrace : WordTrace (prefixWord ++ tailWord_1137019) baseStart_1137019 baseEnd_1137019 := by
    simpa [prefixWord, tailWord_1137019, baseEnd_1137019] using wordTrace_append hprefix tailTrace_1137019
  have hstable : (prefixWord ++ tailWord_1137019).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1137019).length < 2 ^ (prefixWord ++ tailWord_1137019).sum := by decide
  have hdescent : baseEnd_1137019 < baseStart_1137019 := by decide
  rcases family_descends (prefixWord ++ tailWord_1137019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1137021 : List Nat := [1, 4, 1, 1, 2, 3, 3, 1, 1, 5]
def baseStart_1137021 : Nat := 118140960795 + 1137021 * 2 ^ 59
def prefixEnd_1137021 : Nat := 4983230072969 + 3 ^ 40 * 1137021 * 2
def baseEnd_1137021 : Nat := 389225524837267422538961

theorem tailTrace_1137021 : CollatzResearch.WordTrace tailWord_1137021 prefixEnd_1137021 389225524837267422538961 := by
  unfold tailWord_1137021
  simp only [CollatzResearch.WordTrace]
  refine ⟨41470562813774579571834917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27647041875849719714556611 41470562813774579571834917)
  ·
    refine ⟨7775730527582733669719047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 41470562813774579571834917 7775730527582733669719047)
    ·
      refine ⟨11663595791374100504578571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7775730527582733669719047 11663595791374100504578571)
      ·
        refine ⟨17495393687061150756867857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11663595791374100504578571 17495393687061150756867857)
        ·
          refine ⟨13121545265295863067650893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17495393687061150756867857 13121545265295863067650893)
          ·
            refine ⟨4920579474485948650369085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13121545265295863067650893 4920579474485948650369085)
            ·
              refine ⟨1845217302932230743888407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4920579474485948650369085 1845217302932230743888407)
              ·
                refine ⟨2767825954398346115832611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1845217302932230743888407 2767825954398346115832611)
                ·
                  refine ⟨4151738931597519173748917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2767825954398346115832611 4151738931597519173748917)
                  ·
                    refine ⟨389225524837267422538961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4151738931597519173748917 389225524837267422538961)
                    ·
                      rfl

theorem cell22_1137021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 3, 1, 1, 5].length) (baseStart_1137021 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1137021 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1137021 prefixEnd_1137021 := by exact prefixLift 1137021
  have htrace : WordTrace (prefixWord ++ tailWord_1137021) baseStart_1137021 baseEnd_1137021 := by
    simpa [prefixWord, tailWord_1137021, baseEnd_1137021] using wordTrace_append hprefix tailTrace_1137021
  have hstable : (prefixWord ++ tailWord_1137021).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1137021).length < 2 ^ (prefixWord ++ tailWord_1137021).sum := by decide
  have hdescent : baseEnd_1137021 < baseStart_1137021 := by decide
  rcases family_descends (prefixWord ++ tailWord_1137021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1137038 : List Nat := [4, 1, 1, 4, 1, 1, 1, 2, 4, 3]
def baseStart_1137038 : Nat := 118140960795 + 1137038 * 2 ^ 59
def prefixEnd_1137038 : Nat := 4983230072969 + 3 ^ 40 * 1137038 * 2
def baseEnd_1137038 : Nat := 389231344284685044863909

theorem tailTrace_1137038 : CollatzResearch.WordTrace tailWord_1137038 prefixEnd_1137038 389231344284685044863909 := by
  unfold tailWord_1137038
  simp only [CollatzResearch.WordTrace]
  refine ⟨5183897856839123934400471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27647455236475327650135845 5183897856839123934400471)
  ·
    refine ⟨7775846785258685901600707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5183897856839123934400471 7775846785258685901600707)
    ·
      refine ⟨11663770177888028852401061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7775846785258685901600707 11663770177888028852401061)
      ·
        refine ⟨2186956908354005409825199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11663770177888028852401061 2186956908354005409825199)
        ·
          refine ⟨3280435362531008114737799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2186956908354005409825199 3280435362531008114737799)
          ·
            refine ⟨4920653043796512172106699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3280435362531008114737799 4920653043796512172106699)
            ·
              refine ⟨7380979565694768258160049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4920653043796512172106699 7380979565694768258160049)
              ·
                refine ⟨5535734674271076193620037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7380979565694768258160049 5535734674271076193620037)
                ·
                  refine ⟨1037950251425826786303757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5535734674271076193620037 1037950251425826786303757)
                  ·
                    refine ⟨389231344284685044863909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1037950251425826786303757 389231344284685044863909)
                    ·
                      rfl

theorem cell22_1137038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 1, 2, 4, 3].length) (baseStart_1137038 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1137038 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1137038 prefixEnd_1137038 := by exact prefixLift 1137038
  have htrace : WordTrace (prefixWord ++ tailWord_1137038) baseStart_1137038 baseEnd_1137038 := by
    simpa [prefixWord, tailWord_1137038, baseEnd_1137038] using wordTrace_append hprefix tailTrace_1137038
  have hstable : (prefixWord ++ tailWord_1137038).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1137038).length < 2 ^ (prefixWord ++ tailWord_1137038).sum := by decide
  have hdescent : baseEnd_1137038 < baseStart_1137038 := by decide
  rcases family_descends (prefixWord ++ tailWord_1137038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1137053 : List Nat := [1, 4, 2, 1, 4, 1, 1, 2, 2, 4]
def baseStart_1137053 : Nat := 118140960795 + 1137053 * 2 ^ 59
def prefixEnd_1137053 : Nat := 4983230072969 + 3 ^ 40 * 1137053 * 2
def baseEnd_1137053 : Nat := 389236479091230005738863

theorem tailTrace_1137053 : CollatzResearch.WordTrace tailWord_1137053 prefixEnd_1137053 389236479091230005738863 := by
  unfold tailWord_1137053
  simp only [CollatzResearch.WordTrace]
  refine ⟨41471729949658649036999813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27647819966439099357999875 41471729949658649036999813)
  ·
    refine ⟨7775949365560996694437465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 41471729949658649036999813 7775949365560996694437465)
    ·
      refine ⟨5831962024170747520828099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7775949365560996694437465 5831962024170747520828099)
      ·
        refine ⟨8747943036256121281242149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5831962024170747520828099 8747943036256121281242149)
        ·
          refine ⟨1640239319298022740232903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8747943036256121281242149 1640239319298022740232903)
          ·
            refine ⟨2460358978947034110349355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1640239319298022740232903 2460358978947034110349355)
            ·
              refine ⟨3690538468420551165524033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2460358978947034110349355 3690538468420551165524033)
              ·
                refine ⟨2767903851315413374143025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3690538468420551165524033 2767903851315413374143025)
                ·
                  refine ⟨2075927888486560030607269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2767903851315413374143025 2075927888486560030607269)
                  ·
                    refine ⟨389236479091230005738863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2075927888486560030607269 389236479091230005738863)
                    ·
                      rfl

theorem cell22_1137053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 1, 2, 2, 4].length) (baseStart_1137053 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1137053 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1137053 prefixEnd_1137053 := by exact prefixLift 1137053
  have htrace : WordTrace (prefixWord ++ tailWord_1137053) baseStart_1137053 baseEnd_1137053 := by
    simpa [prefixWord, tailWord_1137053, baseEnd_1137053] using wordTrace_append hprefix tailTrace_1137053
  have hstable : (prefixWord ++ tailWord_1137053).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1137053).length < 2 ^ (prefixWord ++ tailWord_1137053).sum := by decide
  have hdescent : baseEnd_1137053 < baseStart_1137053 := by decide
  rcases family_descends (prefixWord ++ tailWord_1137053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1137057 : List Nat := [1, 2, 3, 5, 1, 1, 3, 2, 4]
def baseStart_1137057 : Nat := 118140960795 + 1137057 * 2 ^ 59
def prefixEnd_1137057 : Nat := 4983230072969 + 3 ^ 40 * 1137057 * 2
def baseEnd_1137057 : Nat := 129745949457658442879617

theorem tailTrace_1137057 : CollatzResearch.WordTrace tailWord_1137057 prefixEnd_1137057 129745949457658442879617 := by
  unfold tailWord_1137057
  simp only [CollatzResearch.WordTrace]
  refine ⟨41471875841644157720145425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27647917227762771813430283 41471875841644157720145425)
  ·
    refine ⟨31103906881233118290109069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41471875841644157720145425 31103906881233118290109069)
    ·
      refine ⟨11663965080462419358790901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31103906881233118290109069 11663965080462419358790901)
      ·
        refine ⟨1093496726293351814886647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 11663965080462419358790901 1093496726293351814886647)
        ·
          refine ⟨1640245089440027722329971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1093496726293351814886647 1640245089440027722329971)
          ·
            refine ⟨2460367634160041583494957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1640245089440027722329971 2460367634160041583494957)
            ·
              refine ⟨922637862810015593810609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2460367634160041583494957 922637862810015593810609)
              ·
                refine ⟨691978397107511695357957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 922637862810015593810609 691978397107511695357957)
                ·
                  refine ⟨129745949457658442879617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 691978397107511695357957 129745949457658442879617)
                  ·
                    rfl

theorem cell22_1137057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 3, 2, 4].length) (baseStart_1137057 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1137057 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1137057 prefixEnd_1137057 := by exact prefixLift 1137057
  have htrace : WordTrace (prefixWord ++ tailWord_1137057) baseStart_1137057 baseEnd_1137057 := by
    simpa [prefixWord, tailWord_1137057, baseEnd_1137057] using wordTrace_append hprefix tailTrace_1137057
  have hstable : (prefixWord ++ tailWord_1137057).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1137057).length < 2 ^ (prefixWord ++ tailWord_1137057).sum := by decide
  have hdescent : baseEnd_1137057 < baseStart_1137057 := by decide
  rcases family_descends (prefixWord ++ tailWord_1137057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1137171 : List Nat := [1, 1, 1, 2, 1, 5, 2, 1, 4, 4]
def baseStart_1137171 : Nat := 118140960795 + 1137171 * 2 ^ 59
def prefixEnd_1137171 : Nat := 4983230072969 + 3 ^ 40 * 1137171 * 2
def baseEnd_1137171 : Nat := 389276872902717031288501

theorem tailTrace_1137171 : CollatzResearch.WordTrace tailWord_1137171 prefixEnd_1137171 389276872902717031288501 := by
  unfold tailWord_1137171
  simp only [CollatzResearch.WordTrace]
  refine ⟨41476033763231155189795367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27650689175487436793196911 41476033763231155189795367)
  ·
    refine ⟨62214050644846732784693051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41476033763231155189795367 62214050644846732784693051)
    ·
      refine ⟨93321075967270099177039577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62214050644846732784693051 93321075967270099177039577)
      ·
        refine ⟨69990806975452574382779683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93321075967270099177039577 69990806975452574382779683)
        ·
          refine ⟨104986210463178861574169525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69990806975452574382779683 104986210463178861574169525)
          ·
            refine ⟨9842457230923018272578393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 104986210463178861574169525 9842457230923018272578393)
            ·
              refine ⟨7381842923192263704433795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9842457230923018272578393 7381842923192263704433795)
              ·
                refine ⟨11072764384788395556650693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7381842923192263704433795 11072764384788395556650693)
                ·
                  refine ⟨2076143322147824166872005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11072764384788395556650693 2076143322147824166872005)
                  ·
                    refine ⟨389276872902717031288501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2076143322147824166872005 389276872902717031288501)
                    ·
                      rfl

theorem cell22_1137171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 2, 1, 4, 4].length) (baseStart_1137171 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1137171 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1137171 prefixEnd_1137171 := by exact prefixLift 1137171
  have htrace : WordTrace (prefixWord ++ tailWord_1137171) baseStart_1137171 baseEnd_1137171 := by
    simpa [prefixWord, tailWord_1137171, baseEnd_1137171] using wordTrace_append hprefix tailTrace_1137171
  have hstable : (prefixWord ++ tailWord_1137171).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1137171).length < 2 ^ (prefixWord ++ tailWord_1137171).sum := by decide
  have hdescent : baseEnd_1137171 < baseStart_1137171 := by decide
  rcases family_descends (prefixWord ++ tailWord_1137171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1137173 : List Nat := [1, 3, 2, 1, 3, 1, 3, 1, 4, 3]
def baseStart_1137173 : Nat := 118140960795 + 1137173 * 2 ^ 59
def prefixEnd_1137173 : Nat := 4983230072969 + 3 ^ 40 * 1137173 * 2
def baseEnd_1137173 : Nat := 389277557543589692738495

theorem tailTrace_1137173 : CollatzResearch.WordTrace tailWord_1137173 prefixEnd_1137173 389277557543589692738495 := by
  unfold tailWord_1137173
  simp only [CollatzResearch.WordTrace]
  refine ⟨41476106709223909531368173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27650737806149273020912115 41476106709223909531368173)
  ·
    refine ⟨15553540015958966074263065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41476106709223909531368173 15553540015958966074263065)
    ·
      refine ⟨11665155011969224555697299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15553540015958966074263065 11665155011969224555697299)
      ·
        refine ⟨17497732517953836833545949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11665155011969224555697299 17497732517953836833545949)
        ·
          refine ⟨6561649694232688812579731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17497732517953836833545949 6561649694232688812579731)
          ·
            refine ⟨9842474541349033218869597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6561649694232688812579731 9842474541349033218869597)
            ·
              refine ⟨3690927953005887457076099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9842474541349033218869597 3690927953005887457076099)
              ·
                refine ⟨5536391929508831185614149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3690927953005887457076099 5536391929508831185614149)
                ·
                  refine ⟨1038073486782905847302653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5536391929508831185614149 1038073486782905847302653)
                  ·
                    refine ⟨389277557543589692738495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1038073486782905847302653 389277557543589692738495)
                    ·
                      rfl

theorem cell22_1137173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 3, 1, 4, 3].length) (baseStart_1137173 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1137173 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1137173 prefixEnd_1137173 := by exact prefixLift 1137173
  have htrace : WordTrace (prefixWord ++ tailWord_1137173) baseStart_1137173 baseEnd_1137173 := by
    simpa [prefixWord, tailWord_1137173, baseEnd_1137173] using wordTrace_append hprefix tailTrace_1137173
  have hstable : (prefixWord ++ tailWord_1137173).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1137173).length < 2 ^ (prefixWord ++ tailWord_1137173).sum := by decide
  have hdescent : baseEnd_1137173 < baseStart_1137173 := by decide
  rcases family_descends (prefixWord ++ tailWord_1137173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1137175 : List Nat := [1, 1, 3, 6, 1, 1, 2, 1, 6]
def baseStart_1137175 : Nat := 118140960795 + 1137175 * 2 ^ 59
def prefixEnd_1137175 : Nat := 4983230072969 + 3 ^ 40 * 1137175 * 2
def baseEnd_1137175 : Nat := 129759414061487451396163

theorem tailTrace_1137175 : CollatzResearch.WordTrace tailWord_1137175 prefixEnd_1137175 129759414061487451396163 := by
  unfold tailWord_1137175
  simp only [CollatzResearch.WordTrace]
  refine ⟨41476179655216663872940979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27650786436811109248627319 41476179655216663872940979)
  ·
    refine ⟨62214269482824995809411469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41476179655216663872940979 62214269482824995809411469)
    ·
      refine ⟨23330351056059373428529301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62214269482824995809411469 23330351056059373428529301)
      ·
        refine ⟨1093610205752783129462311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 23330351056059373428529301 1093610205752783129462311)
        ·
          refine ⟨1640415308629174694193467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1093610205752783129462311 1640415308629174694193467)
          ·
            refine ⟨2460622962943762041290201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1640415308629174694193467 2460622962943762041290201)
            ·
              refine ⟨1845467222207821530967651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2460622962943762041290201 1845467222207821530967651)
              ·
                refine ⟨2768200833311732296451477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1845467222207821530967651 2768200833311732296451477)
                ·
                  refine ⟨129759414061487451396163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2768200833311732296451477 129759414061487451396163)
                  ·
                    rfl

theorem cell22_1137175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 2, 1, 6].length) (baseStart_1137175 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1137175 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1137175 prefixEnd_1137175 := by exact prefixLift 1137175
  have htrace : WordTrace (prefixWord ++ tailWord_1137175) baseStart_1137175 baseEnd_1137175 := by
    simpa [prefixWord, tailWord_1137175, baseEnd_1137175] using wordTrace_append hprefix tailTrace_1137175
  have hstable : (prefixWord ++ tailWord_1137175).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1137175).length < 2 ^ (prefixWord ++ tailWord_1137175).sum := by decide
  have hdescent : baseEnd_1137175 < baseStart_1137175 := by decide
  rcases family_descends (prefixWord ++ tailWord_1137175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1137186 : List Nat := [3, 3, 1, 1, 1, 1, 1, 11]
def baseStart_1137186 : Nat := 118140960795 + 1137186 * 2 ^ 59
def prefixEnd_1137186 : Nat := 4983230072969 + 3 ^ 40 * 1137186 * 2
def baseEnd_1137186 : Nat := 43253556412140221351495

theorem tailTrace_1137186 : CollatzResearch.WordTrace tailWord_1137186 prefixEnd_1137186 43253556412140221351495 := by
  unfold tailWord_1137186
  simp only [CollatzResearch.WordTrace]
  refine ⟨10369145214544203187897853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27651053905451208501060941 10369145214544203187897853)
  ·
    refine ⟨3888429455454076195461695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10369145214544203187897853 3888429455454076195461695)
    ·
      refine ⟨5832644183181114293192543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3888429455454076195461695 5832644183181114293192543)
      ·
        refine ⟨8748966274771671439788815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5832644183181114293192543 8748966274771671439788815)
        ·
          refine ⟨13123449412157507159683223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8748966274771671439788815 13123449412157507159683223)
          ·
            refine ⟨19685174118236260739524835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13123449412157507159683223 19685174118236260739524835)
            ·
              refine ⟨29527761177354391109287253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19685174118236260739524835 29527761177354391109287253)
              ·
                refine ⟨43253556412140221351495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 29527761177354391109287253 43253556412140221351495)
                ·
                  rfl

theorem cell22_1137186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 11].length) (baseStart_1137186 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1137186 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1137186 prefixEnd_1137186 := by exact prefixLift 1137186
  have htrace : WordTrace (prefixWord ++ tailWord_1137186) baseStart_1137186 baseEnd_1137186 := by
    simpa [prefixWord, tailWord_1137186, baseEnd_1137186] using wordTrace_append hprefix tailTrace_1137186
  have hstable : (prefixWord ++ tailWord_1137186).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1137186).length < 2 ^ (prefixWord ++ tailWord_1137186).sum := by decide
  have hdescent : baseEnd_1137186 < baseStart_1137186 := by decide
  rcases family_descends (prefixWord ++ tailWord_1137186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1137222 : List Nat := [6, 1, 1, 1, 2, 2, 1, 2, 2, 4]
def baseStart_1137222 : Nat := 118140960795 + 1137222 * 2 ^ 59
def prefixEnd_1137222 : Nat := 4983230072969 + 3 ^ 40 * 1137222 * 2
def baseEnd_1137222 : Nat := 389294331244969898263345

theorem tailTrace_1137222 : CollatzResearch.WordTrace tailWord_1137222 prefixEnd_1137222 389294331244969898263345 := by
  unfold tailWord_1137222
  simp only [CollatzResearch.WordTrace]
  refine ⟨1296184183938949715621935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 27651929257364260599934613 1296184183938949715621935)
  ·
    refine ⟨1944276275908424573432903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1296184183938949715621935 1944276275908424573432903)
    ·
      refine ⟨2916414413862636860149355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1944276275908424573432903 2916414413862636860149355)
      ·
        refine ⟨4374621620793955290224033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2916414413862636860149355 4374621620793955290224033)
        ·
          refine ⟨3280966215595466467668025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4374621620793955290224033 3280966215595466467668025)
          ·
            refine ⟨2460724661696599850751019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3280966215595466467668025 2460724661696599850751019)
            ·
              refine ⟨3691086992544899776126529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2460724661696599850751019 3691086992544899776126529)
              ·
                refine ⟨2768315244408674832094897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3691086992544899776126529 2768315244408674832094897)
                ·
                  refine ⟨2076236433306506124071173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2768315244408674832094897 2076236433306506124071173)
                  ·
                    refine ⟨389294331244969898263345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2076236433306506124071173 389294331244969898263345)
                    ·
                      rfl

theorem cell22_1137222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 1, 2, 2, 4].length) (baseStart_1137222 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1137222 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1137222 prefixEnd_1137222 := by exact prefixLift 1137222
  have htrace : WordTrace (prefixWord ++ tailWord_1137222) baseStart_1137222 baseEnd_1137222 := by
    simpa [prefixWord, tailWord_1137222, baseEnd_1137222] using wordTrace_append hprefix tailTrace_1137222
  have hstable : (prefixWord ++ tailWord_1137222).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1137222).length < 2 ^ (prefixWord ++ tailWord_1137222).sum := by decide
  have hdescent : baseEnd_1137222 < baseStart_1137222 := by decide
  rcases family_descends (prefixWord ++ tailWord_1137222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1137231 : List Nat := [1, 1, 2, 1, 1, 2, 6, 1, 7]
def baseStart_1137231 : Nat := 118140960795 + 1137231 * 2 ^ 59
def prefixEnd_1137231 : Nat := 4983230072969 + 3 ^ 40 * 1137231 * 2
def baseEnd_1137231 : Nat := 129765804042965624929439

theorem tailTrace_1137231 : CollatzResearch.WordTrace tailWord_1137231 prefixEnd_1137231 129765804042965624929439 := by
  unfold tailWord_1137231
  simp only [CollatzResearch.WordTrace]
  refine ⟨41478222143013785436979547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27652148095342523624653031 41478222143013785436979547)
  ·
    refine ⟨62217333214520678155469321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41478222143013785436979547 62217333214520678155469321)
    ·
      refine ⟨46662999910890508616601991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62217333214520678155469321 46662999910890508616601991)
      ·
        refine ⟨69994499866335762924902987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46662999910890508616601991 69994499866335762924902987)
        ·
          refine ⟨104991749799503644387354481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69994499866335762924902987 104991749799503644387354481)
          ·
            refine ⟨78743812349627733290515861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 104991749799503644387354481 78743812349627733290515861)
            ·
              refine ⟨3691116203888799997992931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 78743812349627733290515861 3691116203888799997992931)
              ·
                refine ⟨5536674305833199996989397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3691116203888799997992931 5536674305833199996989397)
                ·
                  refine ⟨129765804042965624929439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5536674305833199996989397 129765804042965624929439)
                  ·
                    rfl

theorem cell22_1137231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 6, 1, 7].length) (baseStart_1137231 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1137231 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1137231 prefixEnd_1137231 := by exact prefixLift 1137231
  have htrace : WordTrace (prefixWord ++ tailWord_1137231) baseStart_1137231 baseEnd_1137231 := by
    simpa [prefixWord, tailWord_1137231, baseEnd_1137231] using wordTrace_append hprefix tailTrace_1137231
  have hstable : (prefixWord ++ tailWord_1137231).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1137231).length < 2 ^ (prefixWord ++ tailWord_1137231).sum := by decide
  have hdescent : baseEnd_1137231 < baseStart_1137231 := by decide
  rcases family_descends (prefixWord ++ tailWord_1137231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1137310 : List Nat := [4, 3, 1, 1, 1, 1, 3, 2, 6]
def baseStart_1137310 : Nat := 118140960795 + 1137310 * 2 ^ 59
def prefixEnd_1137310 : Nat := 4983230072969 + 3 ^ 40 * 1137310 * 2
def baseEnd_1137310 : Nat := 129774818481122334021025

theorem tailTrace_1137310 : CollatzResearch.WordTrace tailWord_1137310 prefixEnd_1137310 129774818481122334021025 := by
  unfold tailWord_1137310
  simp only [CollatzResearch.WordTrace]
  refine ⟨5185137938715947741138173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27654069006485054619403589 5185137938715947741138173)
  ·
    refine ⟨1944426727018480402926815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5185137938715947741138173 1944426727018480402926815)
    ·
      refine ⟨2916640090527720604390223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1944426727018480402926815 2916640090527720604390223)
      ·
        refine ⟨4374960135791580906585335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2916640090527720604390223 4374960135791580906585335)
        ·
          refine ⟨6562440203687371359878003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4374960135791580906585335 6562440203687371359878003)
          ·
            refine ⟨9843660305531057039817005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6562440203687371359878003 9843660305531057039817005)
            ·
              refine ⟨3691372614574146389931377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9843660305531057039817005 3691372614574146389931377)
              ·
                refine ⟨2768529460930609792448533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3691372614574146389931377 2768529460930609792448533)
                ·
                  refine ⟨129774818481122334021025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2768529460930609792448533 129774818481122334021025)
                  ·
                    rfl

theorem cell22_1137310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 3, 2, 6].length) (baseStart_1137310 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1137310 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1137310 prefixEnd_1137310 := by exact prefixLift 1137310
  have htrace : WordTrace (prefixWord ++ tailWord_1137310) baseStart_1137310 baseEnd_1137310 := by
    simpa [prefixWord, tailWord_1137310, baseEnd_1137310] using wordTrace_append hprefix tailTrace_1137310
  have hstable : (prefixWord ++ tailWord_1137310).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1137310).length < 2 ^ (prefixWord ++ tailWord_1137310).sum := by decide
  have hdescent : baseEnd_1137310 < baseStart_1137310 := by decide
  rcases family_descends (prefixWord ++ tailWord_1137310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1137325 : List Nat := [1, 5, 2, 1, 1, 2, 2, 2, 1, 5]
def baseStart_1137325 : Nat := 118140960795 + 1137325 * 2 ^ 59
def prefixEnd_1137325 : Nat := 4983230072969 + 3 ^ 40 * 1137325 * 2
def baseEnd_1137325 : Nat := 389329590249911962938029

theorem tailTrace_1137325 : CollatzResearch.WordTrace tailWord_1137325 prefixEnd_1137325 389329590249911962938029 := by
  unfold tailWord_1137325
  simp only [CollatzResearch.WordTrace]
  refine ⟨41481650604673239490901429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27654433736448826327267619 41481650604673239490901429)
  ·
    refine ⟨3888904744188116202272009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 41481650604673239490901429 3888904744188116202272009)
    ·
      refine ⟨2916678558141087151704007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3888904744188116202272009 2916678558141087151704007)
      ·
        refine ⟨4375017837211630727556011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2916678558141087151704007 4375017837211630727556011)
        ·
          refine ⟨6562526755817446091334017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4375017837211630727556011 6562526755817446091334017)
          ·
            refine ⟨4921895066863084568500513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6562526755817446091334017 4921895066863084568500513)
            ·
              refine ⟨3691421300147313426375385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4921895066863084568500513 3691421300147313426375385)
              ·
                refine ⟨2768565975110485069781539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3691421300147313426375385 2768565975110485069781539)
                ·
                  refine ⟨4152848962665727604672309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2768565975110485069781539 4152848962665727604672309)
                  ·
                    refine ⟨389329590249911962938029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4152848962665727604672309 389329590249911962938029)
                    ·
                      rfl

theorem cell22_1137325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 2, 2, 1, 5].length) (baseStart_1137325 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1137325 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1137325 prefixEnd_1137325 := by exact prefixLift 1137325
  have htrace : WordTrace (prefixWord ++ tailWord_1137325) baseStart_1137325 baseEnd_1137325 := by
    simpa [prefixWord, tailWord_1137325, baseEnd_1137325] using wordTrace_append hprefix tailTrace_1137325
  have hstable : (prefixWord ++ tailWord_1137325).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1137325).length < 2 ^ (prefixWord ++ tailWord_1137325).sum := by decide
  have hdescent : baseEnd_1137325 < baseStart_1137325 := by decide
  rcases family_descends (prefixWord ++ tailWord_1137325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1137370 : List Nat := [3, 1, 1, 2, 2, 2, 1, 4, 3, 3]
def baseStart_1137370 : Nat := 118140960795 + 1137370 * 2 ^ 59
def prefixEnd_1137370 : Nat := 4983230072969 + 3 ^ 40 * 1137370 * 2
def baseEnd_1137370 : Nat := 389344994669546845562891

theorem tailTrace_1137370 : CollatzResearch.WordTrace tailWord_1137370 prefixEnd_1137370 389344994669546845562891 := by
  unfold tailWord_1137370
  simp only [CollatzResearch.WordTrace]
  refine ⟨10370822972377553044072391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27655527926340141450859709 10370822972377553044072391)
  ·
    refine ⟨15556234458566329566108587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10370822972377553044072391 15556234458566329566108587)
    ·
      refine ⟨23334351687849494349162881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15556234458566329566108587 23334351687849494349162881)
      ·
        refine ⟨17500763765887120761872161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23334351687849494349162881 17500763765887120761872161)
        ·
          refine ⟨13125572824415340571404121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17500763765887120761872161 13125572824415340571404121)
          ·
            refine ⟨9844179618311505428553091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13125572824415340571404121 9844179618311505428553091)
            ·
              refine ⟨14766269427467258142829637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9844179618311505428553091 14766269427467258142829637)
              ·
                refine ⟨2768675517650110901780557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14766269427467258142829637 2768675517650110901780557)
                ·
                  refine ⟨1038253319118791588167709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2768675517650110901780557 1038253319118791588167709)
                  ·
                    refine ⟨389344994669546845562891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1038253319118791588167709 389344994669546845562891)
                    ·
                      rfl

theorem cell22_1137370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 4, 3, 3].length) (baseStart_1137370 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1137370 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1137370 prefixEnd_1137370 := by exact prefixLift 1137370
  have htrace : WordTrace (prefixWord ++ tailWord_1137370) baseStart_1137370 baseEnd_1137370 := by
    simpa [prefixWord, tailWord_1137370, baseEnd_1137370] using wordTrace_append hprefix tailTrace_1137370
  have hstable : (prefixWord ++ tailWord_1137370).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1137370).length < 2 ^ (prefixWord ++ tailWord_1137370).sum := by decide
  have hdescent : baseEnd_1137370 < baseStart_1137370 := by decide
  rcases family_descends (prefixWord ++ tailWord_1137370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1137372 : List Nat := [2, 2, 5, 1, 1, 1, 4, 6]
def baseStart_1137372 : Nat := 118140960795 + 1137372 * 2 ^ 59
def prefixEnd_1137372 : Nat := 4983230072969 + 3 ^ 40 * 1137372 * 2
def baseEnd_1137372 : Nat := 43260631034491056334765

theorem tailTrace_1137372 : CollatzResearch.WordTrace tailWord_1137372 prefixEnd_1137372 43260631034491056334765 := by
  unfold tailWord_1137372
  simp only [CollatzResearch.WordTrace]
  refine ⟨20741682417751483258931185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27655576557001977678574913 20741682417751483258931185)
  ·
    refine ⟨15556261813313612444198389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20741682417751483258931185 15556261813313612444198389)
    ·
      refine ⟨1458399544998151166643599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 15556261813313612444198389 1458399544998151166643599)
      ·
        refine ⟨2187599317497226749965399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1458399544998151166643599 2187599317497226749965399)
        ·
          refine ⟨3281398976245840124948099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2187599317497226749965399 3281398976245840124948099)
          ·
            refine ⟨4922098464368760187422149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3281398976245840124948099 4922098464368760187422149)
            ·
              refine ⟨922893462069142535141653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4922098464368760187422149 922893462069142535141653)
              ·
                refine ⟨43260631034491056334765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 922893462069142535141653 43260631034491056334765)
                ·
                  rfl

theorem cell22_1137372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 4, 6].length) (baseStart_1137372 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1137372 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1137372 prefixEnd_1137372 := by exact prefixLift 1137372
  have htrace : WordTrace (prefixWord ++ tailWord_1137372) baseStart_1137372 baseEnd_1137372 := by
    simpa [prefixWord, tailWord_1137372, baseEnd_1137372] using wordTrace_append hprefix tailTrace_1137372
  have hstable : (prefixWord ++ tailWord_1137372).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1137372).length < 2 ^ (prefixWord ++ tailWord_1137372).sum := by decide
  have hdescent : baseEnd_1137372 < baseStart_1137372 := by decide
  rcases family_descends (prefixWord ++ tailWord_1137372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1137492 : List Nat := [2, 4, 1, 1, 4, 1, 1, 1, 1, 6]
def baseStart_1137492 : Nat := 118140960795 + 1137492 * 2 ^ 59
def prefixEnd_1137492 : Nat := 4983230072969 + 3 ^ 40 * 1137492 * 2
def baseEnd_1137492 : Nat := 389386757762779194012517

theorem tailTrace_1137492 : CollatzResearch.WordTrace tailWord_1137492 prefixEnd_1137492 389386757762779194012517 := by
  unfold tailWord_1137492
  simp only [CollatzResearch.WordTrace]
  refine ⟨20743870797534113506115365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27658494396712151341487153 20743870797534113506115365)
  ·
    refine ⟨3889475774537646282396631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20743870797534113506115365 3889475774537646282396631)
    ·
      refine ⟨5834213661806469423594947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3889475774537646282396631 5834213661806469423594947)
      ·
        refine ⟨8751320492709704135392421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5834213661806469423594947 8751320492709704135392421)
        ·
          refine ⟨1640872592383069525386079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8751320492709704135392421 1640872592383069525386079)
          ·
            refine ⟨2461308888574604288079119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1640872592383069525386079 2461308888574604288079119)
            ·
              refine ⟨3691963332861906432118679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2461308888574604288079119 3691963332861906432118679)
              ·
                refine ⟨5537944999292859648178019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3691963332861906432118679 5537944999292859648178019)
                ·
                  refine ⟨8306917498939289472267029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5537944999292859648178019 8306917498939289472267029)
                  ·
                    refine ⟨389386757762779194012517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8306917498939289472267029 389386757762779194012517)
                    ·
                      rfl

theorem cell22_1137492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 1, 1, 1, 6].length) (baseStart_1137492 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1137492 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1137492 prefixEnd_1137492 := by exact prefixLift 1137492
  have htrace : WordTrace (prefixWord ++ tailWord_1137492) baseStart_1137492 baseEnd_1137492 := by
    simpa [prefixWord, tailWord_1137492, baseEnd_1137492] using wordTrace_append hprefix tailTrace_1137492
  have hstable : (prefixWord ++ tailWord_1137492).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1137492).length < 2 ^ (prefixWord ++ tailWord_1137492).sum := by decide
  have hdescent : baseEnd_1137492 < baseStart_1137492 := by decide
  rcases family_descends (prefixWord ++ tailWord_1137492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1137522 : List Nat := [3, 2, 1, 2, 1, 1, 3, 3, 3, 3]
def baseStart_1137522 : Nat := 118140960795 + 1137522 * 2 ^ 59
def prefixEnd_1137522 : Nat := 4983230072969 + 3 ^ 40 * 1137522 * 2
def baseEnd_1137522 : Nat := 389397027375869115762425

theorem tailTrace_1137522 : CollatzResearch.WordTrace tailWord_1137522 prefixEnd_1137522 389397027375869115762425 := by
  unfold tailWord_1137522
  simp only [CollatzResearch.WordTrace]
  refine ⟨10372208946239885533955705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27659223856639694757215213 10372208946239885533955705)
  ·
    refine ⟨7779156709679914150466779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10372208946239885533955705 7779156709679914150466779)
    ·
      refine ⟨11668735064519871225700169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7779156709679914150466779 11668735064519871225700169)
      ·
        refine ⟨8751551298389903419275127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11668735064519871225700169 8751551298389903419275127)
        ·
          refine ⟨13127326947584855128912691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8751551298389903419275127 13127326947584855128912691)
          ·
            refine ⟨19690990421377282693369037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13127326947584855128912691 19690990421377282693369037)
            ·
              refine ⟨7384121408016481010013389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19690990421377282693369037 7384121408016481010013389)
              ·
                refine ⟨2769045528006180378755021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7384121408016481010013389 2769045528006180378755021)
                ·
                  refine ⟨1038392073002317642033133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2769045528006180378755021 1038392073002317642033133)
                  ·
                    refine ⟨389397027375869115762425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1038392073002317642033133 389397027375869115762425)
                    ·
                      rfl

theorem cell22_1137522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 3, 3, 3, 3].length) (baseStart_1137522 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1137522 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1137522 prefixEnd_1137522 := by exact prefixLift 1137522
  have htrace : WordTrace (prefixWord ++ tailWord_1137522) baseStart_1137522 baseEnd_1137522 := by
    simpa [prefixWord, tailWord_1137522, baseEnd_1137522] using wordTrace_append hprefix tailTrace_1137522
  have hstable : (prefixWord ++ tailWord_1137522).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1137522).length < 2 ^ (prefixWord ++ tailWord_1137522).sum := by decide
  have hdescent : baseEnd_1137522 < baseStart_1137522 := by decide
  rcases family_descends (prefixWord ++ tailWord_1137522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1137535 : List Nat := [1, 1, 2, 2, 1, 1, 4, 5, 5]
def baseStart_1137535 : Nat := 118140960795 + 1137535 * 2 ^ 59
def prefixEnd_1137535 : Nat := 4983230072969 + 3 ^ 40 * 1137535 * 2
def baseEnd_1137535 : Nat := 129800492513847138395795

theorem tailTrace_1137535 : CollatzResearch.WordTrace tailWord_1137535 prefixEnd_1137535 129800492513847138395795 := by
  unfold tailWord_1137535
  simp only [CollatzResearch.WordTrace]
  refine ⟨41489309933912445356046059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27659539955941630237364039 41489309933912445356046059)
  ·
    refine ⟨62233964900868668034069089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41489309933912445356046059 62233964900868668034069089)
    ·
      refine ⟨46675473675651501025551817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62233964900868668034069089 46675473675651501025551817)
      ·
        refine ⟨35006605256738625769163863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46675473675651501025551817 35006605256738625769163863)
        ·
          refine ⟨52509907885107938653745795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35006605256738625769163863 52509907885107938653745795)
          ·
            refine ⟨78764861827661907980618693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52509907885107938653745795 78764861827661907980618693)
            ·
              refine ⟨14768411592686607746366005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 78764861827661907980618693 14768411592686607746366005)
              ·
                refine ⟨1384538586814369476221813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14768411592686607746366005 1384538586814369476221813)
                ·
                  refine ⟨129800492513847138395795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1384538586814369476221813 129800492513847138395795)
                  ·
                    rfl

theorem cell22_1137535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 5, 5].length) (baseStart_1137535 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1137535 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1137535 prefixEnd_1137535 := by exact prefixLift 1137535
  have htrace : WordTrace (prefixWord ++ tailWord_1137535) baseStart_1137535 baseEnd_1137535 := by
    simpa [prefixWord, tailWord_1137535, baseEnd_1137535] using wordTrace_append hprefix tailTrace_1137535
  have hstable : (prefixWord ++ tailWord_1137535).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1137535).length < 2 ^ (prefixWord ++ tailWord_1137535).sum := by decide
  have hdescent : baseEnd_1137535 < baseStart_1137535 := by decide
  rcases family_descends (prefixWord ++ tailWord_1137535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1137612 : List Nat := [2, 2, 1, 4, 1, 1, 3, 2, 1, 5]
def baseStart_1137612 : Nat := 118140960795 + 1137612 * 2 ^ 59
def prefixEnd_1137612 : Nat := 4983230072969 + 3 ^ 40 * 1137612 * 2
def baseEnd_1137612 : Nat := 389427836215138881012149

theorem tailTrace_1137612 : CollatzResearch.WordTrace tailWord_1137612 prefixEnd_1137612 389427836215138881012149 := by
  unfold tailWord_1137612
  simp only [CollatzResearch.WordTrace]
  refine ⟨20746059177316743753299545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27661412236422325004399393 20746059177316743753299545)
  ·
    refine ⟨15559544382987557814974659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20746059177316743753299545 15559544382987557814974659)
    ·
      refine ⟨23339316574481336722461989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15559544382987557814974659 23339316574481336722461989)
      ·
        refine ⟨4376121857715250635461623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23339316574481336722461989 4376121857715250635461623)
        ·
          refine ⟨6564182786572875953192435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4376121857715250635461623 6564182786572875953192435)
          ·
            refine ⟨9846274179859313929788653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6564182786572875953192435 9846274179859313929788653)
            ·
              refine ⟨3692352817447242723670745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9846274179859313929788653 3692352817447242723670745)
              ·
                refine ⟨2769264613085432042753059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3692352817447242723670745 2769264613085432042753059)
                ·
                  refine ⟨4153896919628148064129589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2769264613085432042753059 4153896919628148064129589)
                  ·
                    refine ⟨389427836215138881012149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4153896919628148064129589 389427836215138881012149)
                    ·
                      rfl

theorem cell22_1137612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 3, 2, 1, 5].length) (baseStart_1137612 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1137612 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1137612 prefixEnd_1137612 := by exact prefixLift 1137612
  have htrace : WordTrace (prefixWord ++ tailWord_1137612) baseStart_1137612 baseEnd_1137612 := by
    simpa [prefixWord, tailWord_1137612, baseEnd_1137612] using wordTrace_append hprefix tailTrace_1137612
  have hstable : (prefixWord ++ tailWord_1137612).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1137612).length < 2 ^ (prefixWord ++ tailWord_1137612).sum := by decide
  have hdescent : baseEnd_1137612 < baseStart_1137612 := by decide
  rcases family_descends (prefixWord ++ tailWord_1137612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1137625 : List Nat := [1, 2, 1, 2, 5, 11]
def baseStart_1137625 : Nat := 118140960795 + 1137625 * 2 ^ 59
def prefixEnd_1137625 : Nat := 4983230072969 + 3 ^ 40 * 1137625 * 2
def baseEnd_1137625 : Nat := 4807806004701372597989

theorem tailTrace_1137625 : CollatzResearch.WordTrace tailWord_1137625 prefixEnd_1137625 4807806004701372597989 := by
  unfold tailWord_1137625
  simp only [CollatzResearch.WordTrace]
  refine ⟨41492592503586390726822329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27661728335724260484548219 41492592503586390726822329)
  ·
    refine ⟨31119444377689793045116747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41492592503586390726822329 31119444377689793045116747)
    ·
      refine ⟨46679166566534689567675121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31119444377689793045116747 46679166566534689567675121)
      ·
        refine ⟨35009374924901017175756341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46679166566534689567675121 35009374924901017175756341)
        ·
          refine ⟨3282128899209470360227157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 35009374924901017175756341 3282128899209470360227157)
          ·
            refine ⟨4807806004701372597989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 3282128899209470360227157 4807806004701372597989)
            ·
              rfl

theorem cell22_1137625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 11].length) (baseStart_1137625 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1137625 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1137625 prefixEnd_1137625 := by exact prefixLift 1137625
  have htrace : WordTrace (prefixWord ++ tailWord_1137625) baseStart_1137625 baseEnd_1137625 := by
    simpa [prefixWord, tailWord_1137625, baseEnd_1137625] using wordTrace_append hprefix tailTrace_1137625
  have hstable : (prefixWord ++ tailWord_1137625).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1137625).length < 2 ^ (prefixWord ++ tailWord_1137625).sum := by decide
  have hdescent : baseEnd_1137625 < baseStart_1137625 := by decide
  rcases family_descends (prefixWord ++ tailWord_1137625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1137642 : List Nat := [3, 1, 3, 1, 2, 2, 3, 7]
def baseStart_1137642 : Nat := 118140960795 + 1137642 * 2 ^ 59
def prefixEnd_1137642 : Nat := 4983230072969 + 3 ^ 40 * 1137642 * 2
def baseEnd_1137642 : Nat := 43270900647580978084673

theorem tailTrace_1137642 : CollatzResearch.WordTrace tailWord_1137642 prefixEnd_1137642 43270900647580978084673 := by
  unfold tailWord_1137642
  simp only [CollatzResearch.WordTrace]
  refine ⟨10373303136131200657547795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27662141696349868420127453 10373303136131200657547795)
  ·
    refine ⟨15559954704196800986321693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10373303136131200657547795 15559954704196800986321693)
    ·
      refine ⟨5834983014073800369870635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15559954704196800986321693 5834983014073800369870635)
      ·
        refine ⟨8752474521110700554805953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5834983014073800369870635 8752474521110700554805953)
        ·
          refine ⟨6564355890833025416104465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8752474521110700554805953 6564355890833025416104465)
          ·
            refine ⟨4923266918124769062078349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6564355890833025416104465 4923266918124769062078349)
            ·
              refine ⟨1846225094296788398279381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4923266918124769062078349 1846225094296788398279381)
              ·
                refine ⟨43270900647580978084673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1846225094296788398279381 43270900647580978084673)
                ·
                  rfl

theorem cell22_1137642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 3, 7].length) (baseStart_1137642 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1137642 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1137642 prefixEnd_1137642 := by exact prefixLift 1137642
  have htrace : WordTrace (prefixWord ++ tailWord_1137642) baseStart_1137642 baseEnd_1137642 := by
    simpa [prefixWord, tailWord_1137642, baseEnd_1137642] using wordTrace_append hprefix tailTrace_1137642
  have hstable : (prefixWord ++ tailWord_1137642).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1137642).length < 2 ^ (prefixWord ++ tailWord_1137642).sum := by decide
  have hdescent : baseEnd_1137642 < baseStart_1137642 := by decide
  rcases family_descends (prefixWord ++ tailWord_1137642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1137800 : List Nat := [2, 1, 3, 4, 2, 2, 2, 2, 4]
def baseStart_1137800 : Nat := 118140960795 + 1137800 * 2 ^ 59
def prefixEnd_1137800 : Nat := 4983230072969 + 3 ^ 40 * 1137800 * 2
def baseEnd_1137800 : Nat := 129830730819056352437191

theorem tailTrace_1137800 : CollatzResearch.WordTrace tailWord_1137800 prefixEnd_1137800 129830730819056352437191 := by
  unfold tailWord_1137800
  simp only [CollatzResearch.WordTrace]
  refine ⟨20749487638976197807221427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27665983518634930409628569 20749487638976197807221427)
  ·
    refine ⟨31124231458464296710832141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20749487638976197807221427 31124231458464296710832141)
    ·
      refine ⟨11671586796924111266562053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31124231458464296710832141 11671586796924111266562053)
      ·
        refine ⟨2188422524423270862480385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11671586796924111266562053 2188422524423270862480385)
        ·
          refine ⟨1641316893317453146860289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2188422524423270862480385 1641316893317453146860289)
          ·
            refine ⟨1230987669988089860145217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1641316893317453146860289 1230987669988089860145217)
            ·
              refine ⟨923240752491067395108913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1230987669988089860145217 923240752491067395108913)
              ·
                refine ⟨692430564368300546331685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 923240752491067395108913 692430564368300546331685)
                ·
                  refine ⟨129830730819056352437191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 692430564368300546331685 129830730819056352437191)
                  ·
                    rfl

theorem cell22_1137800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 2, 2, 2, 4].length) (baseStart_1137800 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1137800 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1137800 prefixEnd_1137800 := by exact prefixLift 1137800
  have htrace : WordTrace (prefixWord ++ tailWord_1137800) baseStart_1137800 baseEnd_1137800 := by
    simpa [prefixWord, tailWord_1137800, baseEnd_1137800] using wordTrace_append hprefix tailTrace_1137800
  have hstable : (prefixWord ++ tailWord_1137800).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1137800).length < 2 ^ (prefixWord ++ tailWord_1137800).sum := by decide
  have hdescent : baseEnd_1137800 < baseStart_1137800 := by decide
  rcases family_descends (prefixWord ++ tailWord_1137800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1137918 : List Nat := [4, 2, 2, 1, 1, 4, 1, 1, 6]
def baseStart_1137918 : Nat := 118140960795 + 1137918 * 2 ^ 59
def prefixEnd_1137918 : Nat := 4983230072969 + 3 ^ 40 * 1137918 * 2
def baseEnd_1137918 : Nat := 129844195422885360953737

theorem tailTrace_1137918 : CollatzResearch.WordTrace tailWord_1137918 prefixEnd_1137918 129844195422885360953737 := by
  unfold tailWord_1137918
  simp only [CollatzResearch.WordTrace]
  refine ⟨5187909886440612720904801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27668852727683267844825605 5187909886440612720904801)
  ·
    refine ⟨3890932414830459540678601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5187909886440612720904801 3890932414830459540678601)
    ·
      refine ⟨2918199311122844655508951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3890932414830459540678601 2918199311122844655508951)
      ·
        refine ⟨4377298966684266983263427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2918199311122844655508951 4377298966684266983263427)
        ·
          refine ⟨6565948450026400474895141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4377298966684266983263427 6565948450026400474895141)
          ·
            refine ⟨1231115334379950089042839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6565948450026400474895141 1231115334379950089042839)
            ·
              refine ⟨1846673001569925133564259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1231115334379950089042839 1846673001569925133564259)
              ·
                refine ⟨2770009502354887700346389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1846673001569925133564259 2770009502354887700346389)
                ·
                  refine ⟨129844195422885360953737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2770009502354887700346389 129844195422885360953737)
                  ·
                    rfl

theorem cell22_1137918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 4, 1, 1, 6].length) (baseStart_1137918 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1137918 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1137918 prefixEnd_1137918 := by exact prefixLift 1137918
  have htrace : WordTrace (prefixWord ++ tailWord_1137918) baseStart_1137918 baseEnd_1137918 := by
    simpa [prefixWord, tailWord_1137918, baseEnd_1137918] using wordTrace_append hprefix tailTrace_1137918
  have hstable : (prefixWord ++ tailWord_1137918).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1137918).length < 2 ^ (prefixWord ++ tailWord_1137918).sum := by decide
  have hdescent : baseEnd_1137918 < baseStart_1137918 := by decide
  rcases family_descends (prefixWord ++ tailWord_1137918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1137929 : List Nat := [1, 2, 1, 1, 3, 3, 4, 7]
def baseStart_1137929 : Nat := 118140960795 + 1137929 * 2 ^ 59
def prefixEnd_1137929 : Nat := 4983230072969 + 3 ^ 40 * 1137929 * 2
def baseEnd_1137929 : Nat := 43281816865939524537353

theorem tailTrace_1137929 : CollatzResearch.WordTrace tailWord_1137929 prefixEnd_1137929 43281816865939524537353 := by
  unfold tailWord_1137929
  simp only [CollatzResearch.WordTrace]
  refine ⟨41503680294485050645888841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27669120196323367097259227 41503680294485050645888841)
  ·
    refine ⟨31127760220863787984416631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41503680294485050645888841 31127760220863787984416631)
    ·
      refine ⟨46691640331295681976624947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31127760220863787984416631 46691640331295681976624947)
      ·
        refine ⟨70037460496943522964937421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46691640331295681976624947 70037460496943522964937421)
        ·
          refine ⟨26264047686353821111851533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 70037460496943522964937421 26264047686353821111851533)
          ·
            refine ⟨9849017882382682916944325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26264047686353821111851533 9849017882382682916944325)
            ·
              refine ⟨1846690852946753046927061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9849017882382682916944325 1846690852946753046927061)
              ·
                refine ⟨43281816865939524537353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1846690852946753046927061 43281816865939524537353)
                ·
                  rfl

theorem cell22_1137929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 4, 7].length) (baseStart_1137929 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1137929 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1137929 prefixEnd_1137929 := by exact prefixLift 1137929
  have htrace : WordTrace (prefixWord ++ tailWord_1137929) baseStart_1137929 baseEnd_1137929 := by
    simpa [prefixWord, tailWord_1137929, baseEnd_1137929] using wordTrace_append hprefix tailTrace_1137929
  have hstable : (prefixWord ++ tailWord_1137929).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1137929).length < 2 ^ (prefixWord ++ tailWord_1137929).sum := by decide
  have hdescent : baseEnd_1137929 < baseStart_1137929 := by decide
  rcases family_descends (prefixWord ++ tailWord_1137929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1137950 : List Nat := [4, 3, 2, 1, 2, 1, 1, 2, 1, 5]
def baseStart_1137950 : Nat := 118140960795 + 1137950 * 2 ^ 59
def prefixEnd_1137950 : Nat := 4983230072969 + 3 ^ 40 * 1137950 * 2
def baseEnd_1137950 : Nat := 389543540522618666061113

theorem tailTrace_1137950 : CollatzResearch.WordTrace tailWord_1137950 prefixEnd_1137950 389543540522618666061113 := by
  unfold tailWord_1137950
  simp only [CollatzResearch.WordTrace]
  refine ⟨5188055778426121404050413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27669630818272647488268869 5188055778426121404050413)
  ·
    refine ⟨1945520916909795526518905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5188055778426121404050413 1945520916909795526518905)
    ·
      refine ⟨1459140687682346644889179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1945520916909795526518905 1459140687682346644889179)
      ·
        refine ⟨2188711031523519967333769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1459140687682346644889179 2188711031523519967333769)
        ·
          refine ⟨1641533273642639975500327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2188711031523519967333769 1641533273642639975500327)
          ·
            refine ⟨2462299910463959963250491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1641533273642639975500327 2462299910463959963250491)
            ·
              refine ⟨3693449865695939944875737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2462299910463959963250491 3693449865695939944875737)
              ·
                refine ⟨2770087399271954958656803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3693449865695939944875737 2770087399271954958656803)
                ·
                  refine ⟨4155131098907932437985205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2770087399271954958656803 4155131098907932437985205)
                  ·
                    refine ⟨389543540522618666061113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4155131098907932437985205 389543540522618666061113)
                    ·
                      rfl

theorem cell22_1137950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 1, 2, 1, 5].length) (baseStart_1137950 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1137950 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1137950 prefixEnd_1137950 := by exact prefixLift 1137950
  have htrace : WordTrace (prefixWord ++ tailWord_1137950) baseStart_1137950 baseEnd_1137950 := by
    simpa [prefixWord, tailWord_1137950, baseEnd_1137950] using wordTrace_append hprefix tailTrace_1137950
  have hstable : (prefixWord ++ tailWord_1137950).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1137950).length < 2 ^ (prefixWord ++ tailWord_1137950).sum := by decide
  have hdescent : baseEnd_1137950 < baseStart_1137950 := by decide
  rcases family_descends (prefixWord ++ tailWord_1137950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1137991 : List Nat := [1, 1, 4, 1, 2, 3, 2, 3, 5]
def baseStart_1137991 : Nat := 118140960795 + 1137991 * 2 ^ 59
def prefixEnd_1137991 : Nat := 4983230072969 + 3 ^ 40 * 1137991 * 2
def baseEnd_1137991 : Nat := 129852525220169408595329

theorem tailTrace_1137991 : CollatzResearch.WordTrace tailWord_1137991 prefixEnd_1137991 129852525220169408595329 := by
  unfold tailWord_1137991
  simp only [CollatzResearch.WordTrace]
  refine ⟨41505941620260435234645827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27670627746840290156430551 41505941620260435234645827)
  ·
    refine ⟨62258912430390652851968741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41505941620260435234645827 62258912430390652851968741)
    ·
      refine ⟨11673546080698247409744139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 62258912430390652851968741 11673546080698247409744139)
      ·
        refine ⟨17510319121047371114616209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11673546080698247409744139 17510319121047371114616209)
        ·
          refine ⟨13132739340785528335962157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17510319121047371114616209 13132739340785528335962157)
          ·
            refine ⟨4924777252794573125985809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13132739340785528335962157 4924777252794573125985809)
            ·
              refine ⟨3693582939595929844489357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4924777252794573125985809 3693582939595929844489357)
              ·
                refine ⟨1385093602348473691683509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3693582939595929844489357 1385093602348473691683509)
                ·
                  refine ⟨129852525220169408595329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1385093602348473691683509 129852525220169408595329)
                  ·
                    rfl

theorem cell22_1137991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 2, 3, 5].length) (baseStart_1137991 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1137991 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1137991 prefixEnd_1137991 := by exact prefixLift 1137991
  have htrace : WordTrace (prefixWord ++ tailWord_1137991) baseStart_1137991 baseEnd_1137991 := by
    simpa [prefixWord, tailWord_1137991, baseEnd_1137991] using wordTrace_append hprefix tailTrace_1137991
  have hstable : (prefixWord ++ tailWord_1137991).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1137991).length < 2 ^ (prefixWord ++ tailWord_1137991).sum := by decide
  have hdescent : baseEnd_1137991 < baseStart_1137991 := by decide
  rcases family_descends (prefixWord ++ tailWord_1137991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1138126 : List Nat := [4, 1, 1, 1, 2, 1, 2, 1, 9]
def baseStart_1138126 : Nat := 118140960795 + 1138126 * 2 ^ 59
def prefixEnd_1138126 : Nat := 4983230072969 + 3 ^ 40 * 1138126 * 2
def baseEnd_1138126 : Nat := 129867929639804291220191

theorem tailTrace_1138126 : CollatzResearch.WordTrace tailWord_1138126 prefixEnd_1138126 129867929639804291220191 := by
  unfold tailWord_1138126
  simp only [CollatzResearch.WordTrace]
  refine ⟨5188858184346419161351279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27673910316514235527206821 5188858184346419161351279)
  ·
    refine ⟨7783287276519628742026919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5188858184346419161351279 7783287276519628742026919)
    ·
      refine ⟨11674930914779443113040379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7783287276519628742026919 11674930914779443113040379)
      ·
        refine ⟨17512396372169164669560569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11674930914779443113040379 17512396372169164669560569)
        ·
          refine ⟨13134297279126873502170427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17512396372169164669560569 13134297279126873502170427)
          ·
            refine ⟨19701445918690310253255641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13134297279126873502170427 19701445918690310253255641)
            ·
              refine ⟨14776084439017732689941731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19701445918690310253255641 14776084439017732689941731)
              ·
                refine ⟨22164126658526599034912597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14776084439017732689941731 22164126658526599034912597)
                ·
                  refine ⟨129867929639804291220191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 22164126658526599034912597 129867929639804291220191)
                  ·
                    rfl

theorem cell22_1138126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 1, 9].length) (baseStart_1138126 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1138126 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1138126 prefixEnd_1138126 := by exact prefixLift 1138126
  have htrace : WordTrace (prefixWord ++ tailWord_1138126) baseStart_1138126 baseEnd_1138126 := by
    simpa [prefixWord, tailWord_1138126, baseEnd_1138126] using wordTrace_append hprefix tailTrace_1138126
  have hstable : (prefixWord ++ tailWord_1138126).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1138126).length < 2 ^ (prefixWord ++ tailWord_1138126).sum := by decide
  have hdescent : baseEnd_1138126 < baseStart_1138126 := by decide
  rcases family_descends (prefixWord ++ tailWord_1138126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1138143 : List Nat := [1, 1, 2, 3, 3, 1, 4, 2, 5]
def baseStart_1138143 : Nat := 118140960795 + 1138143 * 2 ^ 59
def prefixEnd_1138143 : Nat := 4983230072969 + 3 ^ 40 * 1138143 * 2
def baseEnd_1138143 : Nat := 129869869455610165328507

theorem tailTrace_1138143 : CollatzResearch.WordTrace tailWord_1138143 prefixEnd_1138143 129869869455610165328507 := by
  unfold tailWord_1138143
  simp only [CollatzResearch.WordTrace]
  refine ⟨41511485515709765194179083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27674323677139843462786055 41511485515709765194179083)
  ·
    refine ⟨62267228273564647791268625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41511485515709765194179083 62267228273564647791268625)
    ·
      refine ⟨46700421205173485843451469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62267228273564647791268625 46700421205173485843451469)
      ·
        refine ⟨17512657951940057191294301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46700421205173485843451469 17512657951940057191294301)
        ·
          refine ⟨6567246731977521446735363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17512657951940057191294301 6567246731977521446735363)
          ·
            refine ⟨9850870097966282170103045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6567246731977521446735363 9850870097966282170103045)
            ·
              refine ⟨1847038143368677906894321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9850870097966282170103045 1847038143368677906894321)
              ·
                refine ⟨1385278607526508430170741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1847038143368677906894321 1385278607526508430170741)
                ·
                  refine ⟨129869869455610165328507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1385278607526508430170741 129869869455610165328507)
                  ·
                    rfl

theorem cell22_1138143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 4, 2, 5].length) (baseStart_1138143 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1138143 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1138143 prefixEnd_1138143 := by exact prefixLift 1138143
  have htrace : WordTrace (prefixWord ++ tailWord_1138143) baseStart_1138143 baseEnd_1138143 := by
    simpa [prefixWord, tailWord_1138143, baseEnd_1138143] using wordTrace_append hprefix tailTrace_1138143
  have hstable : (prefixWord ++ tailWord_1138143).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1138143).length < 2 ^ (prefixWord ++ tailWord_1138143).sum := by decide
  have hdescent : baseEnd_1138143 < baseStart_1138143 := by decide
  rcases family_descends (prefixWord ++ tailWord_1138143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1138147 : List Nat := [1, 1, 1, 6, 2, 2, 1, 4, 1, 3]
def baseStart_1138147 : Nat := 118140960795 + 1138147 * 2 ^ 59
def prefixEnd_1138147 : Nat := 4983230072969 + 3 ^ 40 * 1138147 * 2
def baseEnd_1138147 : Nat := 389610977648575818885509

theorem tailTrace_1138147 : CollatzResearch.WordTrace tailWord_1138147 prefixEnd_1138147 389610977648575818885509 := by
  unfold tailWord_1138147
  simp only [CollatzResearch.WordTrace]
  refine ⟨41511631407695273877324695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27674420938463515918216463 41511631407695273877324695)
  ·
    refine ⟨62267447111542910815987043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41511631407695273877324695 62267447111542910815987043)
    ·
      refine ⟨93401170667314366223980565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62267447111542910815987043 93401170667314366223980565)
      ·
        refine ⟨4378179875030360916749089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 93401170667314366223980565 4378179875030360916749089)
        ·
          refine ⟨3283634906272770687561817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4378179875030360916749089 3283634906272770687561817)
          ·
            refine ⟨2462726179704578015671363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3283634906272770687561817 2462726179704578015671363)
            ·
              refine ⟨3694089269556867023507045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2462726179704578015671363 3694089269556867023507045)
              ·
                refine ⟨692641738041912566907571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3694089269556867023507045 692641738041912566907571)
                ·
                  refine ⟨1038962607062868850361357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 692641738041912566907571 1038962607062868850361357)
                  ·
                    refine ⟨389610977648575818885509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1038962607062868850361357 389610977648575818885509)
                    ·
                      rfl

theorem cell22_1138147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 1, 4, 1, 3].length) (baseStart_1138147 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1138147 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1138147 prefixEnd_1138147 := by exact prefixLift 1138147
  have htrace : WordTrace (prefixWord ++ tailWord_1138147) baseStart_1138147 baseEnd_1138147 := by
    simpa [prefixWord, tailWord_1138147, baseEnd_1138147] using wordTrace_append hprefix tailTrace_1138147
  have hstable : (prefixWord ++ tailWord_1138147).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1138147).length < 2 ^ (prefixWord ++ tailWord_1138147).sum := by decide
  have hdescent : baseEnd_1138147 < baseStart_1138147 := by decide
  rcases family_descends (prefixWord ++ tailWord_1138147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1138158 : List Nat := [4, 1, 2, 1, 2, 1, 3, 1, 2, 5]
def baseStart_1138158 : Nat := 118140960795 + 1138158 * 2 ^ 59
def prefixEnd_1138158 : Nat := 4983230072969 + 3 ^ 40 * 1138158 * 2
def baseEnd_1138158 : Nat := 389614743173375456860475

theorem tailTrace_1138158 : CollatzResearch.WordTrace tailWord_1138158 prefixEnd_1138158 389614743173375456860475 := by
  unfold tailWord_1138158
  simp only [CollatzResearch.WordTrace]
  refine ⟨5189004076331927844496891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27674688407103615170650085 5189004076331927844496891)
  ·
    refine ⟨7783506114497891766745337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5189004076331927844496891 7783506114497891766745337)
    ·
      refine ⟨5837629585873418825059003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7783506114497891766745337 5837629585873418825059003)
      ·
        refine ⟨8756444378810128237588505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5837629585873418825059003 8756444378810128237588505)
        ·
          refine ⟨6567333284107596178191379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8756444378810128237588505 6567333284107596178191379)
          ·
            refine ⟨9850999926161394267287069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6567333284107596178191379 9850999926161394267287069)
            ·
              refine ⟨3694124972310522850232651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9850999926161394267287069 3694124972310522850232651)
              ·
                refine ⟨5541187458465784275348977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3694124972310522850232651 5541187458465784275348977)
                ·
                  refine ⟨4155890593849338206511733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5541187458465784275348977 4155890593849338206511733)
                  ·
                    refine ⟨389614743173375456860475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4155890593849338206511733 389614743173375456860475)
                    ·
                      rfl

theorem cell22_1138158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 3, 1, 2, 5].length) (baseStart_1138158 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1138158 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1138158 prefixEnd_1138158 := by exact prefixLift 1138158
  have htrace : WordTrace (prefixWord ++ tailWord_1138158) baseStart_1138158 baseEnd_1138158 := by
    simpa [prefixWord, tailWord_1138158, baseEnd_1138158] using wordTrace_append hprefix tailTrace_1138158
  have hstable : (prefixWord ++ tailWord_1138158).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1138158).length < 2 ^ (prefixWord ++ tailWord_1138158).sum := by decide
  have hdescent : baseEnd_1138158 < baseStart_1138158 := by decide
  rcases family_descends (prefixWord ++ tailWord_1138158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1138171 : List Nat := [1, 1, 1, 1, 1, 3, 2, 6, 6]
def baseStart_1138171 : Nat := 118140960795 + 1138171 * 2 ^ 59
def prefixEnd_1138171 : Nat := 4983230072969 + 3 ^ 40 * 1138171 * 2
def baseEnd_1138171 : Nat := 129873064446349252095145

theorem tailTrace_1138171 : CollatzResearch.WordTrace tailWord_1138171 prefixEnd_1138171 129873064446349252095145 := by
  unfold tailWord_1138171
  simp only [CollatzResearch.WordTrace]
  refine ⟨41512506759608325976198367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27675004506405550650798911 41512506759608325976198367)
  ·
    refine ⟨62268760139412488964297551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41512506759608325976198367 62268760139412488964297551)
    ·
      refine ⟨93403140209118733446446327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62268760139412488964297551 93403140209118733446446327)
      ·
        refine ⟨140104710313678100169669491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93403140209118733446446327 140104710313678100169669491)
        ·
          refine ⟨210157065470517150254504237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 140104710313678100169669491 210157065470517150254504237)
          ·
            refine ⟨78808899551443931345439089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 210157065470517150254504237 78808899551443931345439089)
            ·
              refine ⟨59106674663582948509079317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 78808899551443931345439089 59106674663582948509079317)
              ·
                refine ⟨2770625374855450711363093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 59106674663582948509079317 2770625374855450711363093)
                ·
                  refine ⟨129873064446349252095145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2770625374855450711363093 129873064446349252095145)
                  ·
                    rfl

theorem cell22_1138171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 6, 6].length) (baseStart_1138171 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1138171 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1138171 prefixEnd_1138171 := by exact prefixLift 1138171
  have htrace : WordTrace (prefixWord ++ tailWord_1138171) baseStart_1138171 baseEnd_1138171 := by
    simpa [prefixWord, tailWord_1138171, baseEnd_1138171] using wordTrace_append hprefix tailTrace_1138171
  have hstable : (prefixWord ++ tailWord_1138171).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1138171).length < 2 ^ (prefixWord ++ tailWord_1138171).sum := by decide
  have hdescent : baseEnd_1138171 < baseStart_1138171 := by decide
  rcases family_descends (prefixWord ++ tailWord_1138171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1138173 : List Nat := [1, 4, 1, 1, 1, 4, 2, 1, 3, 4]
def baseStart_1138173 : Nat := 118140960795 + 1138173 * 2 ^ 59
def prefixEnd_1138173 : Nat := 4983230072969 + 3 ^ 40 * 1138173 * 2
def baseEnd_1138173 : Nat := 389619877979920417735429

theorem tailTrace_1138173 : CollatzResearch.WordTrace tailWord_1138173 prefixEnd_1138173 389619877979920417735429 := by
  unfold tailWord_1138173
  simp only [CollatzResearch.WordTrace]
  refine ⟨41512579705601080317771173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27675053137067386878514115 41512579705601080317771173)
  ·
    refine ⟨7783608694800202559582095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 41512579705601080317771173 7783608694800202559582095)
    ·
      refine ⟨11675413042200303839373143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7783608694800202559582095 11675413042200303839373143)
      ·
        refine ⟨17513119563300455759059715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11675413042200303839373143 17513119563300455759059715)
        ·
          refine ⟨26269679344950683638589573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17513119563300455759059715 26269679344950683638589573)
          ·
            refine ⟨4925564877178253182235545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26269679344950683638589573 4925564877178253182235545)
            ·
              refine ⟨3694173657883689886676659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4925564877178253182235545 3694173657883689886676659)
              ·
                refine ⟨5541260486825534830014989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3694173657883689886676659 5541260486825534830014989)
                ·
                  refine ⟨2077972682559575561255621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5541260486825534830014989 2077972682559575561255621)
                  ·
                    refine ⟨389619877979920417735429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2077972682559575561255621 389619877979920417735429)
                    ·
                      rfl

theorem cell22_1138173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 2, 1, 3, 4].length) (baseStart_1138173 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1138173 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1138173 prefixEnd_1138173 := by exact prefixLift 1138173
  have htrace : WordTrace (prefixWord ++ tailWord_1138173) baseStart_1138173 baseEnd_1138173 := by
    simpa [prefixWord, tailWord_1138173, baseEnd_1138173] using wordTrace_append hprefix tailTrace_1138173
  have hstable : (prefixWord ++ tailWord_1138173).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1138173).length < 2 ^ (prefixWord ++ tailWord_1138173).sum := by decide
  have hdescent : baseEnd_1138173 < baseStart_1138173 := by decide
  rcases family_descends (prefixWord ++ tailWord_1138173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1138201 : List Nat := [1, 2, 1, 2, 1, 1, 2, 1, 5, 6]
def baseStart_1138201 : Nat := 118140960795 + 1138201 * 2 ^ 59
def prefixEnd_1138201 : Nat := 4983230072969 + 3 ^ 40 * 1138201 * 2
def baseEnd_1138201 : Nat := 389629462952137678035343

theorem tailTrace_1138201 : CollatzResearch.WordTrace tailWord_1138201 prefixEnd_1138201 389629462952137678035343 := by
  unfold tailWord_1138201
  simp only [CollatzResearch.WordTrace]
  refine ⟨41513600949499641099790457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27675733966333094066526971 41513600949499641099790457)
  ·
    refine ⟨31135200712124730824842843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41513600949499641099790457 31135200712124730824842843)
    ·
      refine ⟨46702801068187096237264265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31135200712124730824842843 46702801068187096237264265)
      ·
        refine ⟨35027100801140322177948199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46702801068187096237264265 35027100801140322177948199)
        ·
          refine ⟨52540651201710483266922299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35027100801140322177948199 52540651201710483266922299)
          ·
            refine ⟨78810976802565724900383449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52540651201710483266922299 78810976802565724900383449)
            ·
              refine ⟨59108232601924293675287587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 78810976802565724900383449 59108232601924293675287587)
              ·
                refine ⟨88662348902886440512931381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59108232601924293675287587 88662348902886440512931381)
                ·
                  refine ⟨8312095209645603798087317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 88662348902886440512931381 8312095209645603798087317)
                  ·
                    refine ⟨389629462952137678035343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8312095209645603798087317 389629462952137678035343)
                    ·
                      rfl

theorem cell22_1138201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 1, 5, 6].length) (baseStart_1138201 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1138201 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1138201 prefixEnd_1138201 := by exact prefixLift 1138201
  have htrace : WordTrace (prefixWord ++ tailWord_1138201) baseStart_1138201 baseEnd_1138201 := by
    simpa [prefixWord, tailWord_1138201, baseEnd_1138201] using wordTrace_append hprefix tailTrace_1138201
  have hstable : (prefixWord ++ tailWord_1138201).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1138201).length < 2 ^ (prefixWord ++ tailWord_1138201).sum := by decide
  have hdescent : baseEnd_1138201 < baseStart_1138201 := by decide
  rcases family_descends (prefixWord ++ tailWord_1138201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1138205 : List Nat := [1, 4, 2, 2, 1, 1, 1, 6, 4]
def baseStart_1138205 : Nat := 118140960795 + 1138205 * 2 ^ 59
def prefixEnd_1138205 : Nat := 4983230072969 + 3 ^ 40 * 1138205 * 2
def baseEnd_1138205 : Nat := 129876944077961000311777

theorem tailTrace_1138205 : CollatzResearch.WordTrace tailWord_1138205 prefixEnd_1138205 129876944077961000311777 := by
  unfold tailWord_1138205
  simp only [CollatzResearch.WordTrace]
  refine ⟨41513746841485149782936069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27675831227656766521957379 41513746841485149782936069)
  ·
    refine ⟨7783827532778465584300513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 41513746841485149782936069 7783827532778465584300513)
    ·
      refine ⟨5837870649583849188225385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7783827532778465584300513 5837870649583849188225385)
      ·
        refine ⟨4378402987187886891169039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5837870649583849188225385 4378402987187886891169039)
        ·
          refine ⟨6567604480781830336753559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4378402987187886891169039 6567604480781830336753559)
          ·
            refine ⟨9851406721172745505130339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6567604480781830336753559 9851406721172745505130339)
            ·
              refine ⟨14777110081759118257695509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9851406721172745505130339 14777110081759118257695509)
              ·
                refine ⟨692677035082458668329477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 14777110081759118257695509 692677035082458668329477)
                ·
                  refine ⟨129876944077961000311777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 692677035082458668329477 129876944077961000311777)
                  ·
                    rfl

theorem cell22_1138205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 6, 4].length) (baseStart_1138205 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1138205 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1138205 prefixEnd_1138205 := by exact prefixLift 1138205
  have htrace : WordTrace (prefixWord ++ tailWord_1138205) baseStart_1138205 baseEnd_1138205 := by
    simpa [prefixWord, tailWord_1138205, baseEnd_1138205] using wordTrace_append hprefix tailTrace_1138205
  have hstable : (prefixWord ++ tailWord_1138205).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1138205).length < 2 ^ (prefixWord ++ tailWord_1138205).sum := by decide
  have hdescent : baseEnd_1138205 < baseStart_1138205 := by decide
  rcases family_descends (prefixWord ++ tailWord_1138205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1138218 : List Nat := [3, 1, 4, 1, 1, 1, 1, 1, 3, 6]
def baseStart_1138218 : Nat := 118140960795 + 1138218 * 2 ^ 59
def prefixEnd_1138218 : Nat := 4983230072969 + 3 ^ 40 * 1138218 * 2
def baseEnd_1138218 : Nat := 389635282399555300360291

theorem tailTrace_1138218 : CollatzResearch.WordTrace tailWord_1138218 prefixEnd_1138218 389635282399555300360291 := by
  unfold tailWord_1138218
  simp only [CollatzResearch.WordTrace]
  refine ⟨10378555247609513250789827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27676147326958702002106205 10378555247609513250789827)
  ·
    refine ⟨15567832871414269876184741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10378555247609513250789827 15567832871414269876184741)
    ·
      refine ⟨2918968663390175601784639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15567832871414269876184741 2918968663390175601784639)
      ·
        refine ⟨4378452995085263402676959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2918968663390175601784639 4378452995085263402676959)
        ·
          refine ⟨6567679492627895104015439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4378452995085263402676959 6567679492627895104015439)
          ·
            refine ⟨9851519238941842656023159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6567679492627895104015439 9851519238941842656023159)
            ·
              refine ⟨14777278858412763984034739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9851519238941842656023159 14777278858412763984034739)
              ·
                refine ⟨22165918287619145976052109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14777278858412763984034739 22165918287619145976052109)
                ·
                  refine ⟨8312219357857179741019541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22165918287619145976052109 8312219357857179741019541)
                  ·
                    refine ⟨389635282399555300360291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8312219357857179741019541 389635282399555300360291)
                    ·
                      rfl

theorem cell22_1138218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 1, 3, 6].length) (baseStart_1138218 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1138218 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1138218 prefixEnd_1138218 := by exact prefixLift 1138218
  have htrace : WordTrace (prefixWord ++ tailWord_1138218) baseStart_1138218 baseEnd_1138218 := by
    simpa [prefixWord, tailWord_1138218, baseEnd_1138218] using wordTrace_append hprefix tailTrace_1138218
  have hstable : (prefixWord ++ tailWord_1138218).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1138218).length < 2 ^ (prefixWord ++ tailWord_1138218).sum := by decide
  have hdescent : baseEnd_1138218 < baseStart_1138218 := by decide
  rcases family_descends (prefixWord ++ tailWord_1138218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1138233 : List Nat := [1, 2, 1, 5, 1, 3, 1, 8]
def baseStart_1138233 : Nat := 118140960795 + 1138233 * 2 ^ 59
def prefixEnd_1138233 : Nat := 4983230072969 + 3 ^ 40 * 1138233 * 2
def baseEnd_1138233 : Nat := 43293379689566695692805

theorem tailTrace_1138233 : CollatzResearch.WordTrace tailWord_1138233 prefixEnd_1138233 43293379689566695692805 := by
  unfold tailWord_1138233
  simp only [CollatzResearch.WordTrace]
  refine ⟨41514768085383710564955353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27676512056922473709970235 41514768085383710564955353)
  ·
    refine ⟨31136076064037782923716515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41514768085383710564955353 31136076064037782923716515)
    ·
      refine ⟨46704114096056674385574773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31136076064037782923716515 46704114096056674385574773)
      ·
        refine ⟨4378510696505313223647635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 46704114096056674385574773 4378510696505313223647635)
        ·
          refine ⟨6567766044757969835471453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4378510696505313223647635 6567766044757969835471453)
          ·
            refine ⟨2462912266784238688301795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6567766044757969835471453 2462912266784238688301795)
            ·
              refine ⟨3694368400176358032452693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2462912266784238688301795 3694368400176358032452693)
              ·
                refine ⟨43293379689566695692805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3694368400176358032452693 43293379689566695692805)
                ·
                  rfl

theorem cell22_1138233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 1, 8].length) (baseStart_1138233 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1138233 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1138233 prefixEnd_1138233 := by exact prefixLift 1138233
  have htrace : WordTrace (prefixWord ++ tailWord_1138233) baseStart_1138233 baseEnd_1138233 := by
    simpa [prefixWord, tailWord_1138233, baseEnd_1138233] using wordTrace_append hprefix tailTrace_1138233
  have hstable : (prefixWord ++ tailWord_1138233).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1138233).length < 2 ^ (prefixWord ++ tailWord_1138233).sum := by decide
  have hdescent : baseEnd_1138233 < baseStart_1138233 := by decide
  rcases family_descends (prefixWord ++ tailWord_1138233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1138340 : List Nat := [2, 3, 1, 2, 2, 3, 1, 2, 6]
def baseStart_1138340 : Nat := 118140960795 + 1138340 * 2 ^ 59
def prefixEnd_1138340 : Nat := 4983230072969 + 3 ^ 40 * 1138340 * 2
def baseEnd_1138340 : Nat := 129892348497595882936639

theorem tailTrace_1138340 : CollatzResearch.WordTrace tailWord_1138340 prefixEnd_1138340 129892348497595882936639 := by
  unfold tailWord_1138340
  simp only [CollatzResearch.WordTrace]
  refine ⟨20759335347998033919550237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27679113797330711892733649 20759335347998033919550237)
  ·
    refine ⟨7784750755499262719831339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20759335347998033919550237 7784750755499262719831339)
    ·
      refine ⟨11677126133248894079747009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7784750755499262719831339 11677126133248894079747009)
      ·
        refine ⟨8757844599936670559810257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11677126133248894079747009 8757844599936670559810257)
        ·
          refine ⟨6568383449952502919857693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8757844599936670559810257 6568383449952502919857693)
          ·
            refine ⟨2463143793732188594946635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6568383449952502919857693 2463143793732188594946635)
            ·
              refine ⟨3694715690598282892419953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2463143793732188594946635 3694715690598282892419953)
              ·
                refine ⟨2771036767948712169314965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3694715690598282892419953 2771036767948712169314965)
                ·
                  refine ⟨129892348497595882936639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2771036767948712169314965 129892348497595882936639)
                  ·
                    rfl

theorem cell22_1138340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 1, 2, 6].length) (baseStart_1138340 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1138340 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1138340 prefixEnd_1138340 := by exact prefixLift 1138340
  have htrace : WordTrace (prefixWord ++ tailWord_1138340) baseStart_1138340 baseEnd_1138340 := by
    simpa [prefixWord, tailWord_1138340, baseEnd_1138340] using wordTrace_append hprefix tailTrace_1138340
  have hstable : (prefixWord ++ tailWord_1138340).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1138340).length < 2 ^ (prefixWord ++ tailWord_1138340).sum := by decide
  have hdescent : baseEnd_1138340 < baseStart_1138340 := by decide
  rcases family_descends (prefixWord ++ tailWord_1138340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1138355 : List Nat := [1, 1, 1, 2, 3, 3, 2, 2, 4, 3]
def baseStart_1138355 : Nat := 118140960795 + 1138355 * 2 ^ 59
def prefixEnd_1138355 : Nat := 4983230072969 + 3 ^ 40 * 1138355 * 2
def baseEnd_1138355 : Nat := 389682180299332609684871

theorem tailTrace_1138355 : CollatzResearch.WordTrace tailWord_1138355 prefixEnd_1138355 389682180299332609684871 := by
  unfold tailWord_1138355
  simp only [CollatzResearch.WordTrace]
  refine ⟨41519217790941725400896519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27679478527294483600597679 41519217790941725400896519)
  ·
    refine ⟨62278826686412588101344779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41519217790941725400896519 62278826686412588101344779)
    ·
      refine ⟨93418240029618882152017169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62278826686412588101344779 93418240029618882152017169)
      ·
        refine ⟨70063680022214161614012877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93418240029618882152017169 70063680022214161614012877)
        ·
          refine ⟨26273880008330310605254829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 70063680022214161614012877 26273880008330310605254829)
          ·
            refine ⟨9852705003123866476970561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26273880008330310605254829 9852705003123866476970561)
            ·
              refine ⟨7389528752342899857727921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9852705003123866476970561 7389528752342899857727921)
              ·
                refine ⟨5542146564257174893295941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7389528752342899857727921 5542146564257174893295941)
                ·
                  refine ⟨1039152480798220292492989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5542146564257174893295941 1039152480798220292492989)
                  ·
                    refine ⟨389682180299332609684871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1039152480798220292492989 389682180299332609684871)
                    ·
                      rfl

theorem cell22_1138355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 2, 2, 4, 3].length) (baseStart_1138355 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1138355 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1138355 prefixEnd_1138355 := by exact prefixLift 1138355
  have htrace : WordTrace (prefixWord ++ tailWord_1138355) baseStart_1138355 baseEnd_1138355 := by
    simpa [prefixWord, tailWord_1138355, baseEnd_1138355] using wordTrace_append hprefix tailTrace_1138355
  have hstable : (prefixWord ++ tailWord_1138355).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1138355).length < 2 ^ (prefixWord ++ tailWord_1138355).sum := by decide
  have hdescent : baseEnd_1138355 < baseStart_1138355 := by decide
  rcases family_descends (prefixWord ++ tailWord_1138355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1138359 : List Nat := [1, 1, 3, 1, 5, 3, 2, 1, 1, 4]
def baseStart_1138359 : Nat := 118140960795 + 1138359 * 2 ^ 59
def prefixEnd_1138359 : Nat := 4983230072969 + 3 ^ 40 * 1138359 * 2
def baseEnd_1138359 : Nat := 389683549581077932584859

theorem tailTrace_1138359 : CollatzResearch.WordTrace tailWord_1138359 prefixEnd_1138359 389683549581077932584859 := by
  unfold tailWord_1138359
  simp only [CollatzResearch.WordTrace]
  refine ⟨41519363682927234084042131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27679575788618156056028087 41519363682927234084042131)
  ·
    refine ⟨62279045524390851126063197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41519363682927234084042131 62279045524390851126063197)
    ·
      refine ⟨23354642071646569172273699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62279045524390851126063197 23354642071646569172273699)
      ·
        refine ⟨35031963107469853758410549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23354642071646569172273699 35031963107469853758410549)
        ·
          refine ⟨3284246541325298789850989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 35031963107469853758410549 3284246541325298789850989)
          ·
            refine ⟨1231592452996987046194121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3284246541325298789850989 1231592452996987046194121)
            ·
              refine ⟨923694339747740284645591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1231592452996987046194121 923694339747740284645591)
              ·
                refine ⟨1385541509621610426968387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 923694339747740284645591 1385541509621610426968387)
                ·
                  refine ⟨2078312264432415640452581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1385541509621610426968387 2078312264432415640452581)
                  ·
                    refine ⟨389683549581077932584859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2078312264432415640452581 389683549581077932584859)
                    ·
                      rfl

theorem cell22_1138359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 3, 2, 1, 1, 4].length) (baseStart_1138359 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1138359 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1138359 prefixEnd_1138359 := by exact prefixLift 1138359
  have htrace : WordTrace (prefixWord ++ tailWord_1138359) baseStart_1138359 baseEnd_1138359 := by
    simpa [prefixWord, tailWord_1138359, baseEnd_1138359] using wordTrace_append hprefix tailTrace_1138359
  have hstable : (prefixWord ++ tailWord_1138359).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1138359).length < 2 ^ (prefixWord ++ tailWord_1138359).sum := by decide
  have hdescent : baseEnd_1138359 < baseStart_1138359 := by decide
  rcases family_descends (prefixWord ++ tailWord_1138359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1138368 : List Nat := [2, 1, 1, 2, 4, 1, 11]
def baseStart_1138368 : Nat := 118140960795 + 1138368 * 2 ^ 59
def prefixEnd_1138368 : Nat := 4983230072969 + 3 ^ 40 * 1138368 * 2
def baseEnd_1138368 : Nat := 14432838165370552189253

theorem tailTrace_1138368 : CollatzResearch.WordTrace tailWord_1138368 prefixEnd_1138368 14432838165370552189253 := by
  unfold tailWord_1138368
  simp only [CollatzResearch.WordTrace]
  refine ⟨20759845969947314310559879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27679794626596419080746505 20759845969947314310559879)
  ·
    refine ⟨31139768954920971465839819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20759845969947314310559879 31139768954920971465839819)
    ·
      refine ⟨46709653432381457198759729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31139768954920971465839819 46709653432381457198759729)
      ·
        refine ⟨35032240074286092899069797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46709653432381457198759729 35032240074286092899069797)
        ·
          refine ⟨6568545013928642418575587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 35032240074286092899069797 6568545013928642418575587)
          ·
            refine ⟨9852817520892963627863381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6568545013928642418575587 9852817520892963627863381)
            ·
              refine ⟨14432838165370552189253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 9852817520892963627863381 14432838165370552189253)
              ·
                rfl

theorem cell22_1138368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 11].length) (baseStart_1138368 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1138368 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1138368 prefixEnd_1138368 := by exact prefixLift 1138368
  have htrace : WordTrace (prefixWord ++ tailWord_1138368) baseStart_1138368 baseEnd_1138368 := by
    simpa [prefixWord, tailWord_1138368, baseEnd_1138368] using wordTrace_append hprefix tailTrace_1138368
  have hstable : (prefixWord ++ tailWord_1138368).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1138368).length < 2 ^ (prefixWord ++ tailWord_1138368).sum := by decide
  have hdescent : baseEnd_1138368 < baseStart_1138368 := by decide
  rcases family_descends (prefixWord ++ tailWord_1138368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1138372 : List Nat := [2, 3, 3, 1, 1, 1, 3, 1, 4, 3]
def baseStart_1138372 : Nat := 118140960795 + 1138372 * 2 ^ 59
def prefixEnd_1138372 : Nat := 4983230072969 + 3 ^ 40 * 1138372 * 2
def baseEnd_1138372 : Nat := 389687999746750232009819

theorem tailTrace_1138372 : CollatzResearch.WordTrace tailWord_1138372 prefixEnd_1138372 389687999746750232009819 := by
  unfold tailWord_1138372
  simp only [CollatzResearch.WordTrace]
  refine ⟨20759918915940068652132685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27679891887920091536176913 20759918915940068652132685)
  ·
    refine ⟨7784969593477525744549757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20759918915940068652132685 7784969593477525744549757)
    ·
      refine ⟨2919363597554072154206159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7784969593477525744549757 2919363597554072154206159)
      ·
        refine ⟨4379045396331108231309239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2919363597554072154206159 4379045396331108231309239)
        ·
          refine ⟨6568568094496662346963859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4379045396331108231309239 6568568094496662346963859)
          ·
            refine ⟨9852852141744993520445789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6568568094496662346963859 9852852141744993520445789)
            ·
              refine ⟨3694819553154372570167171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9852852141744993520445789 3694819553154372570167171)
              ·
                refine ⟨5542229329731558855250757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3694819553154372570167171 5542229329731558855250757)
                ·
                  refine ⟨1039167999324667285359517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5542229329731558855250757 1039167999324667285359517)
                  ·
                    refine ⟨389687999746750232009819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1039167999324667285359517 389687999746750232009819)
                    ·
                      rfl

theorem cell22_1138372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 3, 1, 4, 3].length) (baseStart_1138372 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1138372 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1138372 prefixEnd_1138372 := by exact prefixLift 1138372
  have htrace : WordTrace (prefixWord ++ tailWord_1138372) baseStart_1138372 baseEnd_1138372 := by
    simpa [prefixWord, tailWord_1138372, baseEnd_1138372] using wordTrace_append hprefix tailTrace_1138372
  have hstable : (prefixWord ++ tailWord_1138372).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1138372).length < 2 ^ (prefixWord ++ tailWord_1138372).sum := by decide
  have hdescent : baseEnd_1138372 < baseStart_1138372 := by decide
  rcases family_descends (prefixWord ++ tailWord_1138372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1138374 : List Nat := [6, 1, 2, 1, 1, 1, 1, 3, 6]
def baseStart_1138374 : Nat := 118140960795 + 1138374 * 2 ^ 59
def prefixEnd_1138374 : Nat := 4983230072969 + 3 ^ 40 * 1138374 * 2
def baseEnd_1138374 : Nat := 129896228129207631153271

theorem tailTrace_1138374 : CollatzResearch.WordTrace tailWord_1138374 prefixEnd_1138374 129896228129207631153271 := by
  unfold tailWord_1138374
  simp only [CollatzResearch.WordTrace]
  refine ⟨1297497211808527863932443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 27679940518581927763892117 1297497211808527863932443)
  ·
    refine ⟨1946245817712791795898665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1297497211808527863932443 1946245817712791795898665)
    ·
      refine ⟨1459684363284593846923999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1946245817712791795898665 1459684363284593846923999)
      ·
        refine ⟨2189526544926890770385999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1459684363284593846923999 2189526544926890770385999)
        ·
          refine ⟨3284289817390336155578999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2189526544926890770385999 3284289817390336155578999)
          ·
            refine ⟨4926434726085504233368499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3284289817390336155578999 4926434726085504233368499)
            ·
              refine ⟨7389652089128256350052749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4926434726085504233368499 7389652089128256350052749)
              ·
                refine ⟨2771119533423096131269781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7389652089128256350052749 2771119533423096131269781)
                ·
                  refine ⟨129896228129207631153271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2771119533423096131269781 129896228129207631153271)
                  ·
                    rfl

theorem cell22_1138374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 1, 3, 6].length) (baseStart_1138374 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1138374 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1138374 prefixEnd_1138374 := by exact prefixLift 1138374
  have htrace : WordTrace (prefixWord ++ tailWord_1138374) baseStart_1138374 baseEnd_1138374 := by
    simpa [prefixWord, tailWord_1138374, baseEnd_1138374] using wordTrace_append hprefix tailTrace_1138374
  have hstable : (prefixWord ++ tailWord_1138374).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1138374).length < 2 ^ (prefixWord ++ tailWord_1138374).sum := by decide
  have hdescent : baseEnd_1138374 < baseStart_1138374 := by decide
  rcases family_descends (prefixWord ++ tailWord_1138374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1138485 : List Nat := [1, 3, 3, 1, 5, 1, 2, 2, 1, 3]
def baseStart_1138485 : Nat := 118140960795 + 1138485 * 2 ^ 59
def prefixEnd_1138485 : Nat := 4983230072969 + 3 ^ 40 * 1138485 * 2
def baseEnd_1138485 : Nat := 389726681956055603934473

theorem tailTrace_1138485 : CollatzResearch.WordTrace tailWord_1138485 prefixEnd_1138485 389726681956055603934473 := by
  unfold tailWord_1138485
  simp only [CollatzResearch.WordTrace]
  refine ⟨41523959280470757603128909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27682639520313838402085939 41523959280470757603128909)
  ·
    refine ⟨15571484730176534101173341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41523959280470757603128909 15571484730176534101173341)
    ·
      refine ⟨5839306773816200287940003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15571484730176534101173341 5839306773816200287940003)
      ·
        refine ⟨8758960160724300431910005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5839306773816200287940003 8758960160724300431910005)
        ·
          refine ⟨821152515067903165491563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 8758960160724300431910005 821152515067903165491563)
          ·
            refine ⟨1231728772601854748237345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 821152515067903165491563 1231728772601854748237345)
            ·
              refine ⟨923796579451391061178009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1231728772601854748237345 923796579451391061178009)
              ·
                refine ⟨692847434588543295883507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 923796579451391061178009 692847434588543295883507)
                ·
                  refine ⟨1039271151882814943825261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 692847434588543295883507 1039271151882814943825261)
                  ·
                    refine ⟨389726681956055603934473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1039271151882814943825261 389726681956055603934473)
                    ·
                      rfl

theorem cell22_1138485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 5, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 5, 1, 2, 2, 1, 3].length) (baseStart_1138485 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1138485 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1138485 prefixEnd_1138485 := by exact prefixLift 1138485
  have htrace : WordTrace (prefixWord ++ tailWord_1138485) baseStart_1138485 baseEnd_1138485 := by
    simpa [prefixWord, tailWord_1138485, baseEnd_1138485] using wordTrace_append hprefix tailTrace_1138485
  have hstable : (prefixWord ++ tailWord_1138485).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1138485).length < 2 ^ (prefixWord ++ tailWord_1138485).sum := by decide
  have hdescent : baseEnd_1138485 < baseStart_1138485 := by decide
  rcases family_descends (prefixWord ++ tailWord_1138485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1138505 : List Nat := [1, 2, 1, 1, 2, 4, 2, 2, 1, 6]
def baseStart_1138505 : Nat := 118140960795 + 1138505 * 2 ^ 59
def prefixEnd_1138505 : Nat := 4983230072969 + 3 ^ 40 * 1138505 * 2
def baseEnd_1138505 : Nat := 389733528364782218434411

theorem tailTrace_1138505 : CollatzResearch.WordTrace tailWord_1138505 prefixEnd_1138505 389733528364782218434411 := by
  unfold tailWord_1138505
  simp only [CollatzResearch.WordTrace]
  refine ⟨41524688740398301018856969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27683125826932200679237979 41524688740398301018856969)
  ·
    refine ⟨31143516555298725764142727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41524688740398301018856969 31143516555298725764142727)
    ·
      refine ⟨46715274832948088646214091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31143516555298725764142727 46715274832948088646214091)
      ·
        refine ⟨70072912249422132969321137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46715274832948088646214091 70072912249422132969321137)
        ·
          refine ⟨52554684187066599726990853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70072912249422132969321137 52554684187066599726990853)
          ·
            refine ⟨9854003285074987448810785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 52554684187066599726990853 9854003285074987448810785)
            ·
              refine ⟨7390502463806240586608089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9854003285074987448810785 7390502463806240586608089)
              ·
                refine ⟨5542876847854680439956067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7390502463806240586608089 5542876847854680439956067)
                ·
                  refine ⟨8314315271782020659934101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5542876847854680439956067 8314315271782020659934101)
                  ·
                    refine ⟨389733528364782218434411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8314315271782020659934101 389733528364782218434411)
                    ·
                      rfl

theorem cell22_1138505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 2, 2, 1, 6].length) (baseStart_1138505 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1138505 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1138505 prefixEnd_1138505 := by exact prefixLift 1138505
  have htrace : WordTrace (prefixWord ++ tailWord_1138505) baseStart_1138505 baseEnd_1138505 := by
    simpa [prefixWord, tailWord_1138505, baseEnd_1138505] using wordTrace_append hprefix tailTrace_1138505
  have hstable : (prefixWord ++ tailWord_1138505).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1138505).length < 2 ^ (prefixWord ++ tailWord_1138505).sum := by decide
  have hdescent : baseEnd_1138505 < baseStart_1138505 := by decide
  rcases family_descends (prefixWord ++ tailWord_1138505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1138509 : List Nat := [1, 6, 1, 2, 1, 2, 1, 2, 6]
def baseStart_1138509 : Nat := 118140960795 + 1138509 * 2 ^ 59
def prefixEnd_1138509 : Nat := 4983230072969 + 3 ^ 40 * 1138509 * 2
def baseEnd_1138509 : Nat := 129911632548842513778133

theorem tailTrace_1138509 : CollatzResearch.WordTrace tailWord_1138509 prefixEnd_1138509 129911632548842513778133 := by
  unfold tailWord_1138509
  simp only [CollatzResearch.WordTrace]
  refine ⟨41524834632383809702002581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27683223088255873134668387 41524834632383809702002581)
  ·
    refine ⟨1946476623392991079781371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 41524834632383809702002581 1946476623392991079781371)
    ·
      refine ⟨2919714935089486619672057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1946476623392991079781371 2919714935089486619672057)
      ·
        refine ⟨2189786201317114964754043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2919714935089486619672057 2189786201317114964754043)
        ·
          refine ⟨3284679301975672447131065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2189786201317114964754043 3284679301975672447131065)
          ·
            refine ⟨2463509476481754335348299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3284679301975672447131065 2463509476481754335348299)
            ·
              refine ⟨3695264214722631503022449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2463509476481754335348299 3695264214722631503022449)
              ·
                refine ⟨2771448161041973627266837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3695264214722631503022449 2771448161041973627266837)
                ·
                  refine ⟨129911632548842513778133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2771448161041973627266837 129911632548842513778133)
                  ·
                    rfl

theorem cell22_1138509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 1, 2, 6].length) (baseStart_1138509 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1138509 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1138509 prefixEnd_1138509 := by exact prefixLift 1138509
  have htrace : WordTrace (prefixWord ++ tailWord_1138509) baseStart_1138509 baseEnd_1138509 := by
    simpa [prefixWord, tailWord_1138509, baseEnd_1138509] using wordTrace_append hprefix tailTrace_1138509
  have hstable : (prefixWord ++ tailWord_1138509).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1138509).length < 2 ^ (prefixWord ++ tailWord_1138509).sum := by decide
  have hdescent : baseEnd_1138509 < baseStart_1138509 := by decide
  rcases family_descends (prefixWord ++ tailWord_1138509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1138672 : List Nat := [2, 1, 1, 1, 3, 2, 5, 7]
def baseStart_1138672 : Nat := 118140960795 + 1138672 * 2 ^ 59
def prefixEnd_1138672 : Nat := 4983230072969 + 3 ^ 40 * 1138672 * 2
def baseEnd_1138672 : Nat := 43310077319738827723211

theorem tailTrace_1138672 : CollatzResearch.WordTrace tailWord_1138672 prefixEnd_1138672 43310077319738827723211 := by
  unfold tailWord_1138672
  simp only [CollatzResearch.WordTrace]
  refine ⟨20765389865396644270093135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27687186487195525693457513 20765389865396644270093135)
  ·
    refine ⟨31148084798094966405139703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20765389865396644270093135 31148084798094966405139703)
    ·
      refine ⟨46722127197142449607709555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31148084798094966405139703 46722127197142449607709555)
      ·
        refine ⟨70083190795713674411564333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46722127197142449607709555 70083190795713674411564333)
        ·
          refine ⟨26281196548392627904336625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 70083190795713674411564333 26281196548392627904336625)
          ·
            refine ⟨19710897411294470928252469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26281196548392627904336625 19710897411294470928252469)
            ·
              refine ⟨1847896632308856649523669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 19710897411294470928252469 1847896632308856649523669)
              ·
                refine ⟨43310077319738827723211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1847896632308856649523669 43310077319738827723211)
                ·
                  rfl

theorem cell22_1138672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 5, 7].length) (baseStart_1138672 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1138672 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1138672 prefixEnd_1138672 := by exact prefixLift 1138672
  have htrace : WordTrace (prefixWord ++ tailWord_1138672) baseStart_1138672 baseEnd_1138672 := by
    simpa [prefixWord, tailWord_1138672, baseEnd_1138672] using wordTrace_append hprefix tailTrace_1138672
  have hstable : (prefixWord ++ tailWord_1138672).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1138672).length < 2 ^ (prefixWord ++ tailWord_1138672).sum := by decide
  have hdescent : baseEnd_1138672 < baseStart_1138672 := by decide
  rcases family_descends (prefixWord ++ tailWord_1138672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1138689 : List Nat := [1, 2, 4, 1, 2, 1, 5, 6]
def baseStart_1138689 : Nat := 118140960795 + 1138689 * 2 ^ 59
def prefixEnd_1138689 : Nat := 4983230072969 + 3 ^ 40 * 1138689 * 2
def baseEnd_1138689 : Nat := 43310723925007452425983

theorem tailTrace_1138689 : CollatzResearch.WordTrace tailWord_1138689 prefixEnd_1138689 43310723925007452425983 := by
  unfold tailWord_1138689
  simp only [CollatzResearch.WordTrace]
  refine ⟨41531399771731700443555121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27687599847821133629036747 41531399771731700443555121)
  ·
    refine ⟨31148549828798775332666341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41531399771731700443555121 31148549828798775332666341)
    ·
      refine ⟨5840353092899770374874939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31148549828798775332666341 5840353092899770374874939)
      ·
        refine ⟨8760529639349655562312409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5840353092899770374874939 8760529639349655562312409)
        ·
          refine ⟨6570397229512241671734307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8760529639349655562312409 6570397229512241671734307)
          ·
            refine ⟨9855595844268362507601461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6570397229512241671734307 9855595844268362507601461)
            ·
              refine ⟨923962110400158985087637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9855595844268362507601461 923962110400158985087637)
              ·
                refine ⟨43310723925007452425983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 923962110400158985087637 43310723925007452425983)
                ·
                  rfl

theorem cell22_1138689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 5, 6].length) (baseStart_1138689 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1138689 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1138689 prefixEnd_1138689 := by exact prefixLift 1138689
  have htrace : WordTrace (prefixWord ++ tailWord_1138689) baseStart_1138689 baseEnd_1138689 := by
    simpa [prefixWord, tailWord_1138689, baseEnd_1138689] using wordTrace_append hprefix tailTrace_1138689
  have hstable : (prefixWord ++ tailWord_1138689).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1138689).length < 2 ^ (prefixWord ++ tailWord_1138689).sum := by decide
  have hdescent : baseEnd_1138689 < baseStart_1138689 := by decide
  rcases family_descends (prefixWord ++ tailWord_1138689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1138732 : List Nat := [2, 2, 1, 1, 1, 2, 2, 3, 1, 7]
def baseStart_1138732 : Nat := 118140960795 + 1138732 * 2 ^ 59
def prefixEnd_1138732 : Nat := 4983230072969 + 3 ^ 40 * 1138732 * 2
def baseEnd_1138732 : Nat := 389811235103829293008715

theorem tailTrace_1138732 : CollatzResearch.WordTrace tailWord_1138732 prefixEnd_1138732 389811235103829293008715 := by
  unfold tailWord_1138732
  simp only [CollatzResearch.WordTrace]
  refine ⟨20766484055287959393685225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27688645407050612524913633 20766484055287959393685225)
  ·
    refine ⟨15574863041465969545263919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20766484055287959393685225 15574863041465969545263919)
    ·
      refine ⟨23362294562198954317895879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15574863041465969545263919 23362294562198954317895879)
      ·
        refine ⟨35043441843298431476843819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23362294562198954317895879 35043441843298431476843819)
        ·
          refine ⟨52565162764947647215265729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35043441843298431476843819 52565162764947647215265729)
          ·
            refine ⟨39423872073710735411449297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52565162764947647215265729 39423872073710735411449297)
            ·
              refine ⟨29567904055283051558586973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39423872073710735411449297 29567904055283051558586973)
              ·
                refine ⟨11087964020731144334470115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29567904055283051558586973 11087964020731144334470115)
                ·
                  refine ⟨16631946031096716501705173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11087964020731144334470115 16631946031096716501705173)
                  ·
                    refine ⟨389811235103829293008715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 16631946031096716501705173 389811235103829293008715)
                    ·
                      rfl

theorem cell22_1138732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 7].length) (baseStart_1138732 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1138732 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1138732 prefixEnd_1138732 := by exact prefixLift 1138732
  have htrace : WordTrace (prefixWord ++ tailWord_1138732) baseStart_1138732 baseEnd_1138732 := by
    simpa [prefixWord, tailWord_1138732, baseEnd_1138732] using wordTrace_append hprefix tailTrace_1138732
  have hstable : (prefixWord ++ tailWord_1138732).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1138732).length < 2 ^ (prefixWord ++ tailWord_1138732).sum := by decide
  have hdescent : baseEnd_1138732 < baseStart_1138732 := by decide
  rcases family_descends (prefixWord ++ tailWord_1138732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1138740 : List Nat := [2, 5, 1, 2, 3, 1, 2, 6]
def baseStart_1138740 : Nat := 118140960795 + 1138740 * 2 ^ 59
def prefixEnd_1138740 : Nat := 4983230072969 + 3 ^ 40 * 1138740 * 2
def baseEnd_1138740 : Nat := 43312663740813326534299

theorem tailTrace_1138740 : CollatzResearch.WordTrace tailWord_1138740 prefixEnd_1138740 43312663740813326534299 := by
  unfold tailWord_1138740
  simp only [CollatzResearch.WordTrace]
  refine ⟨20766629947273468076830837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27688839929697957435774449 20766629947273468076830837)
  ·
    refine ⟨1946871557556887632202891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 20766629947273468076830837 1946871557556887632202891)
    ·
      refine ⟨2920307336335331448304337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1946871557556887632202891 2920307336335331448304337)
      ·
        refine ⟨2190230502251498586228253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2920307336335331448304337 2190230502251498586228253)
        ·
          refine ⟨821336438344311969835595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2190230502251498586228253 821336438344311969835595)
          ·
            refine ⟨1232004657516467954753393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 821336438344311969835595 1232004657516467954753393)
            ·
              refine ⟨924003493137350966065045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1232004657516467954753393 924003493137350966065045)
              ·
                refine ⟨43312663740813326534299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 924003493137350966065045 43312663740813326534299)
                ·
                  rfl

theorem cell22_1138740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 3, 1, 2, 6].length) (baseStart_1138740 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1138740 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1138740 prefixEnd_1138740 := by exact prefixLift 1138740
  have htrace : WordTrace (prefixWord ++ tailWord_1138740) baseStart_1138740 baseEnd_1138740 := by
    simpa [prefixWord, tailWord_1138740, baseEnd_1138740] using wordTrace_append hprefix tailTrace_1138740
  have hstable : (prefixWord ++ tailWord_1138740).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1138740).length < 2 ^ (prefixWord ++ tailWord_1138740).sum := by decide
  have hdescent : baseEnd_1138740 < baseStart_1138740 := by decide
  rcases family_descends (prefixWord ++ tailWord_1138740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1138824 : List Nat := [2, 1, 3, 4, 1, 11]
def baseStart_1138824 : Nat := 118140960795 + 1138824 * 2 ^ 59
def prefixEnd_1138824 : Nat := 4983230072969 + 3 ^ 40 * 1138824 * 2
def baseEnd_1138824 : Nat := 4812873192394712588993

theorem tailTrace_1138824 : CollatzResearch.WordTrace tailWord_1138824 prefixEnd_1138824 4812873192394712588993 := by
  unfold tailWord_1138824
  simp only [CollatzResearch.WordTrace]
  refine ⟨20768161813121309249859763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27690882417495078999813017 20768161813121309249859763)
  ·
    refine ⟨31152242719681963874789645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20768161813121309249859763 31152242719681963874789645)
    ·
      refine ⟨11682091019880736453046117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31152242719681963874789645 11682091019880736453046117)
      ·
        refine ⟨2190392066227638084946147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11682091019880736453046117 2190392066227638084946147)
        ·
          refine ⟨3285588099341457127419221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2190392066227638084946147 3285588099341457127419221)
          ·
            refine ⟨4812873192394712588993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 3285588099341457127419221 4812873192394712588993)
            ·
              rfl

theorem cell22_1138824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 11].length) (baseStart_1138824 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1138824 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1138824 prefixEnd_1138824 := by exact prefixLift 1138824
  have htrace : WordTrace (prefixWord ++ tailWord_1138824) baseStart_1138824 baseEnd_1138824 := by
    simpa [prefixWord, tailWord_1138824, baseEnd_1138824] using wordTrace_append hprefix tailTrace_1138824
  have hstable : (prefixWord ++ tailWord_1138824).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1138824).length < 2 ^ (prefixWord ++ tailWord_1138824).sum := by decide
  have hdescent : baseEnd_1138824 < baseStart_1138824 := by decide
  rcases family_descends (prefixWord ++ tailWord_1138824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1138826 : List Nat := [3, 1, 2, 3, 1, 2, 2, 2, 2, 4]
def baseStart_1138826 : Nat := 118140960795 + 1138826 * 2 ^ 59
def prefixEnd_1138826 : Nat := 4983230072969 + 3 ^ 40 * 1138826 * 2
def baseEnd_1138826 : Nat := 389843413224844381158427

theorem tailTrace_1138826 : CollatzResearch.WordTrace tailWord_1138826 prefixEnd_1138826 389843413224844381158427 := by
  unfold tailWord_1138826
  simp only [CollatzResearch.WordTrace]
  refine ⟨10384099143058843210323083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27690931048156915227528221 10384099143058843210323083)
  ·
    refine ⟨15576148714588264815484625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10384099143058843210323083 15576148714588264815484625)
    ·
      refine ⟨11682111535941198611613469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15576148714588264815484625 11682111535941198611613469)
      ·
        refine ⟨4380791825977949479355051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11682111535941198611613469 4380791825977949479355051)
        ·
          refine ⟨6571187738966924219032577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4380791825977949479355051 6571187738966924219032577)
          ·
            refine ⟨4928390804225193164274433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6571187738966924219032577 4928390804225193164274433)
            ·
              refine ⟨3696293103168894873205825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4928390804225193164274433 3696293103168894873205825)
              ·
                refine ⟨2772219827376671154904369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3696293103168894873205825 2772219827376671154904369)
                ·
                  refine ⟨2079164870532503366178277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2772219827376671154904369 2079164870532503366178277)
                  ·
                    refine ⟨389843413224844381158427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2079164870532503366178277 389843413224844381158427)
                    ·
                      rfl

theorem cell22_1138826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 2, 2, 2, 4].length) (baseStart_1138826 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1138826 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1138826 prefixEnd_1138826 := by exact prefixLift 1138826
  have htrace : WordTrace (prefixWord ++ tailWord_1138826) baseStart_1138826 baseEnd_1138826 := by
    simpa [prefixWord, tailWord_1138826, baseEnd_1138826] using wordTrace_append hprefix tailTrace_1138826
  have hstable : (prefixWord ++ tailWord_1138826).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1138826).length < 2 ^ (prefixWord ++ tailWord_1138826).sum := by decide
  have hdescent : baseEnd_1138826 < baseStart_1138826 := by decide
  rcases family_descends (prefixWord ++ tailWord_1138826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1138976 : List Nat := [2, 1, 1, 5, 2, 1, 2, 8]
def baseStart_1138976 : Nat := 118140960795 + 1138976 * 2 ^ 59
def prefixEnd_1138976 : Nat := 4983230072969 + 3 ^ 40 * 1138976 * 2
def baseEnd_1138976 : Nat := 43321640143365998878663

theorem tailTrace_1138976 : CollatzResearch.WordTrace tailWord_1138976 prefixEnd_1138976 43321640143365998878663 := by
  unfold tailWord_1138976
  simp only [CollatzResearch.WordTrace]
  refine ⟨20770933760845974229626391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27694578347794632306168521 20770933760845974229626391)
  ·
    refine ⟨31156400641268961344439587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20770933760845974229626391 31156400641268961344439587)
    ·
      refine ⟨46734600961903442016659381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31156400641268961344439587 46734600961903442016659381)
      ·
        refine ⟨4381368840178447689061817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 46734600961903442016659381 4381368840178447689061817)
        ·
          refine ⟨3286026630133835766796363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4381368840178447689061817 3286026630133835766796363)
          ·
            refine ⟨4929039945200753650194545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3286026630133835766796363 4929039945200753650194545)
            ·
              refine ⟨3696779958900565237645909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4929039945200753650194545 3696779958900565237645909)
              ·
                refine ⟨43321640143365998878663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3696779958900565237645909 43321640143365998878663)
                ·
                  rfl

theorem cell22_1138976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 2, 8].length) (baseStart_1138976 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1138976 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1138976 prefixEnd_1138976 := by exact prefixLift 1138976
  have htrace : WordTrace (prefixWord ++ tailWord_1138976) baseStart_1138976 baseEnd_1138976 := by
    simpa [prefixWord, tailWord_1138976, baseEnd_1138976] using wordTrace_append hprefix tailTrace_1138976
  have hstable : (prefixWord ++ tailWord_1138976).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1138976).length < 2 ^ (prefixWord ++ tailWord_1138976).sum := by decide
  have hdescent : baseEnd_1138976 < baseStart_1138976 := by decide
  rcases family_descends (prefixWord ++ tailWord_1138976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1138978 : List Nat := [3, 3, 1, 1, 3, 1, 1, 3, 2, 4]
def baseStart_1138978 : Nat := 118140960795 + 1138978 * 2 ^ 59
def prefixEnd_1138978 : Nat := 4983230072969 + 3 ^ 40 * 1138978 * 2
def baseEnd_1138978 : Nat := 389895445931166651357961

theorem tailTrace_1138978 : CollatzResearch.WordTrace tailWord_1138978 prefixEnd_1138978 389895445931166651357961 := by
  unfold tailWord_1138978
  simp only [CollatzResearch.WordTrace]
  refine ⟨10385485116921175700206397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27694626978456468533883725 10385485116921175700206397)
  ·
    refine ⟨3894556918845440887577399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10385485116921175700206397 3894556918845440887577399)
    ·
      refine ⟨5841835378268161331366099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3894556918845440887577399 5841835378268161331366099)
      ·
        refine ⟨8762753067402241997049149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5841835378268161331366099 8762753067402241997049149)
        ·
          refine ⟨3286032400275840748893431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8762753067402241997049149 3286032400275840748893431)
          ·
            refine ⟨4929048600413761123340147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3286032400275840748893431 4929048600413761123340147)
            ·
              refine ⟨7393572900620641685010221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4929048600413761123340147 7393572900620641685010221)
              ·
                refine ⟨2772589837732740631878833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7393572900620641685010221 2772589837732740631878833)
                ·
                  refine ⟨2079442378299555473909125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2772589837732740631878833 2079442378299555473909125)
                  ·
                    refine ⟨389895445931166651357961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2079442378299555473909125 389895445931166651357961)
                    ·
                      rfl

theorem cell22_1138978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 1, 3, 2, 4].length) (baseStart_1138978 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1138978 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1138978 prefixEnd_1138978 := by exact prefixLift 1138978
  have htrace : WordTrace (prefixWord ++ tailWord_1138978) baseStart_1138978 baseEnd_1138978 := by
    simpa [prefixWord, tailWord_1138978, baseEnd_1138978] using wordTrace_append hprefix tailTrace_1138978
  have hstable : (prefixWord ++ tailWord_1138978).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1138978).length < 2 ^ (prefixWord ++ tailWord_1138978).sum := by decide
  have hdescent : baseEnd_1138978 < baseStart_1138978 := by decide
  rcases family_descends (prefixWord ++ tailWord_1138978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1139042 : List Nat := [3, 3, 2, 1, 1, 2, 1, 5, 1, 3]
def baseStart_1139042 : Nat := 118140960795 + 1139042 * 2 ^ 59
def prefixEnd_1139042 : Nat := 4983230072969 + 3 ^ 40 * 1139042 * 2
def baseEnd_1139042 : Nat := 389917354439091817757765

theorem tailTrace_1139042 : CollatzResearch.WordTrace tailWord_1139042 prefixEnd_1139042 389917354439091817757765 := by
  unfold tailWord_1139042
  simp only [CollatzResearch.WordTrace]
  refine ⟨10386068684863210432788845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27696183159635227820770253 10386068684863210432788845)
  ·
    refine ⟨3894775756823703912295817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10386068684863210432788845 3894775756823703912295817)
    ·
      refine ⟨2921081817617777934221863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3894775756823703912295817 2921081817617777934221863)
      ·
        refine ⟨4381622726426666901332795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2921081817617777934221863 4381622726426666901332795)
        ·
          refine ⟨6572434089640000351999193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4381622726426666901332795 6572434089640000351999193)
          ·
            refine ⟨4929325567230000263999395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6572434089640000351999193 4929325567230000263999395)
            ·
              refine ⟨7393988350845000395999093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4929325567230000263999395 7393988350845000395999093)
              ·
                refine ⟨693186407891718787124915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7393988350845000395999093 693186407891718787124915)
                ·
                  refine ⟨1039779611837578180687373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 693186407891718787124915 1039779611837578180687373)
                  ·
                    refine ⟨389917354439091817757765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1039779611837578180687373 389917354439091817757765)
                    ·
                      rfl

theorem cell22_1139042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 1, 5, 1, 3].length) (baseStart_1139042 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1139042 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1139042 prefixEnd_1139042 := by exact prefixLift 1139042
  have htrace : WordTrace (prefixWord ++ tailWord_1139042) baseStart_1139042 baseEnd_1139042 := by
    simpa [prefixWord, tailWord_1139042, baseEnd_1139042] using wordTrace_append hprefix tailTrace_1139042
  have hstable : (prefixWord ++ tailWord_1139042).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1139042).length < 2 ^ (prefixWord ++ tailWord_1139042).sum := by decide
  have hdescent : baseEnd_1139042 < baseStart_1139042 := by decide
  rcases family_descends (prefixWord ++ tailWord_1139042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1139102 : List Nat := [4, 3, 1, 2, 1, 1, 2, 3, 1, 4]
def baseStart_1139102 : Nat := 118140960795 + 1139102 * 2 ^ 59
def prefixEnd_1139102 : Nat := 4983230072969 + 3 ^ 40 * 1139102 * 2
def baseEnd_1139102 : Nat := 389937893665271661257581

theorem tailTrace_1139102 : CollatzResearch.WordTrace tailWord_1139102 prefixEnd_1139102 389937893665271661257581 := by
  unfold tailWord_1139102
  simp only [CollatzResearch.WordTrace]
  refine ⟨5193307889904433997292445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27697642079490314652226373 5193307889904433997292445)
  ·
    refine ⟨1947490458714162748984667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5193307889904433997292445 1947490458714162748984667)
    ·
      refine ⟨2921235688071244123477001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1947490458714162748984667 2921235688071244123477001)
      ·
        refine ⟨2190926766053433092607751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2921235688071244123477001 2190926766053433092607751)
        ·
          refine ⟨3286390149080149638911627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2190926766053433092607751 3286390149080149638911627)
          ·
            refine ⟨4929585223620224458367441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3286390149080149638911627 4929585223620224458367441)
            ·
              refine ⟨3697188917715168343775581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4929585223620224458367441 3697188917715168343775581)
              ·
                refine ⟨1386445844143188128915843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3697188917715168343775581 1386445844143188128915843)
                ·
                  refine ⟨2079668766214782193373765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1386445844143188128915843 2079668766214782193373765)
                  ·
                    refine ⟨389937893665271661257581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2079668766214782193373765 389937893665271661257581)
                    ·
                      rfl

theorem cell22_1139102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 2, 3, 1, 4].length) (baseStart_1139102 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1139102 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1139102 prefixEnd_1139102 := by exact prefixLift 1139102
  have htrace : WordTrace (prefixWord ++ tailWord_1139102) baseStart_1139102 baseEnd_1139102 := by
    simpa [prefixWord, tailWord_1139102, baseEnd_1139102] using wordTrace_append hprefix tailTrace_1139102
  have hstable : (prefixWord ++ tailWord_1139102).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1139102).length < 2 ^ (prefixWord ++ tailWord_1139102).sum := by decide
  have hdescent : baseEnd_1139102 < baseStart_1139102 := by decide
  rcases family_descends (prefixWord ++ tailWord_1139102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1139117 : List Nat := [1, 5, 2, 2, 2, 2, 1, 1, 6]
def baseStart_1139117 : Nat := 118140960795 + 1139117 * 2 ^ 59
def prefixEnd_1139117 : Nat := 4983230072969 + 3 ^ 40 * 1139117 * 2
def baseEnd_1139117 : Nat := 129981009490605540710845

theorem tailTrace_1139117 : CollatzResearch.WordTrace tailWord_1139117 prefixEnd_1139117 129981009490605540710845 := by
  unfold tailWord_1139117
  simp only [CollatzResearch.WordTrace]
  refine ⟨41547010214181129540135605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27698006809454086360090403 41547010214181129540135605)
  ·
    refine ⟨3895032207579480894387713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 41547010214181129540135605 3895032207579480894387713)
    ·
      refine ⟨2921274155684610670790785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3895032207579480894387713 2921274155684610670790785)
      ·
        refine ⟨2190955616763458003093089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2921274155684610670790785 2190955616763458003093089)
        ·
          refine ⟨1643216712572593502319817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2190955616763458003093089 1643216712572593502319817)
          ·
            refine ⟨1232412534429445126739863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1643216712572593502319817 1232412534429445126739863)
            ·
              refine ⟨1848618801644167690109795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1232412534429445126739863 1848618801644167690109795)
              ·
                refine ⟨2772928202466251535164693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1848618801644167690109795 2772928202466251535164693)
                ·
                  refine ⟨129981009490605540710845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2772928202466251535164693 129981009490605540710845)
                  ·
                    rfl

theorem cell22_1139117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 2, 1, 1, 6].length) (baseStart_1139117 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1139117 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1139117 prefixEnd_1139117 := by exact prefixLift 1139117
  have htrace : WordTrace (prefixWord ++ tailWord_1139117) baseStart_1139117 baseEnd_1139117 := by
    simpa [prefixWord, tailWord_1139117, baseEnd_1139117] using wordTrace_append hprefix tailTrace_1139117
  have hstable : (prefixWord ++ tailWord_1139117).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1139117).length < 2 ^ (prefixWord ++ tailWord_1139117).sum := by decide
  have hdescent : baseEnd_1139117 < baseStart_1139117 := by decide
  rcases family_descends (prefixWord ++ tailWord_1139117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1139132 : List Nat := [2, 2, 2, 4, 1, 2, 1, 3, 2, 3]
def baseStart_1139132 : Nat := 118140960795 + 1139132 * 2 ^ 59
def prefixEnd_1139132 : Nat := 4983230072969 + 3 ^ 40 * 1139132 * 2
def baseEnd_1139132 : Nat := 389948163278361583007489

theorem tailTrace_1139132 : CollatzResearch.WordTrace tailWord_1139132 prefixEnd_1139132 389948163278361583007489 := by
  unfold tailWord_1139132
  simp only [CollatzResearch.WordTrace]
  refine ⟨20773778654563393550965825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27698371539417858067954433 20773778654563393550965825)
  ·
    refine ⟨15580333990922545163224369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20773778654563393550965825 15580333990922545163224369)
    ·
      refine ⟨11685250493191908872418277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15580333990922545163224369 11685250493191908872418277)
      ·
        refine ⟨2190984467473482913578427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11685250493191908872418277 2190984467473482913578427)
        ·
          refine ⟨3286476701210224370367641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2190984467473482913578427 3286476701210224370367641)
          ·
            refine ⟨2464857525907668277775731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3286476701210224370367641 2464857525907668277775731)
            ·
              refine ⟨3697286288861502416663597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2464857525907668277775731 3697286288861502416663597)
              ·
                refine ⟨1386482358323063406248849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3697286288861502416663597 1386482358323063406248849)
                ·
                  refine ⟨1039861768742297554686637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1386482358323063406248849 1039861768742297554686637)
                  ·
                    refine ⟨389948163278361583007489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1039861768742297554686637 389948163278361583007489)
                    ·
                      rfl

theorem cell22_1139132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 1, 3, 2, 3].length) (baseStart_1139132 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1139132 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1139132 prefixEnd_1139132 := by exact prefixLift 1139132
  have htrace : WordTrace (prefixWord ++ tailWord_1139132) baseStart_1139132 baseEnd_1139132 := by
    simpa [prefixWord, tailWord_1139132, baseEnd_1139132] using wordTrace_append hprefix tailTrace_1139132
  have hstable : (prefixWord ++ tailWord_1139132).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1139132).length < 2 ^ (prefixWord ++ tailWord_1139132).sum := by decide
  have hdescent : baseEnd_1139132 < baseStart_1139132 := by decide
  rcases family_descends (prefixWord ++ tailWord_1139132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1139190 : List Nat := [5, 1, 1, 1, 2, 1, 1, 5, 5]
def baseStart_1139190 : Nat := 118140960795 + 1139190 * 2 ^ 59
def prefixEnd_1139190 : Nat := 4983230072969 + 3 ^ 40 * 1139190 * 2
def baseEnd_1139190 : Nat := 129989339287889588352437

theorem tailTrace_1139190 : CollatzResearch.WordTrace tailWord_1139190 prefixEnd_1139190 129989339287889588352437 := by
  unfold tailWord_1139190
  simp only [CollatzResearch.WordTrace]
  refine ⟨2596854546432291437971439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 27699781828611108671695349 2596854546432291437971439)
  ·
    refine ⟨3895281819648437156957159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2596854546432291437971439 3895281819648437156957159)
    ·
      refine ⟨5842922729472655735435739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3895281819648437156957159 5842922729472655735435739)
      ·
        refine ⟨8764384094208983603153609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5842922729472655735435739 8764384094208983603153609)
        ·
          refine ⟨6573288070656737702365207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8764384094208983603153609 6573288070656737702365207)
          ·
            refine ⟨9859932105985106553547811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6573288070656737702365207 9859932105985106553547811)
            ·
              refine ⟨14789898158977659830321717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9859932105985106553547811 14789898158977659830321717)
              ·
                refine ⟨1386552952404155609092661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14789898158977659830321717 1386552952404155609092661)
                ·
                  refine ⟨129989339287889588352437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1386552952404155609092661 129989339287889588352437)
                  ·
                    rfl

theorem cell22_1139190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 5, 5].length) (baseStart_1139190 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1139190 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1139190 prefixEnd_1139190 := by exact prefixLift 1139190
  have htrace : WordTrace (prefixWord ++ tailWord_1139190) baseStart_1139190 baseEnd_1139190 := by
    simpa [prefixWord, tailWord_1139190, baseEnd_1139190] using wordTrace_append hprefix tailTrace_1139190
  have hstable : (prefixWord ++ tailWord_1139190).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1139190).length < 2 ^ (prefixWord ++ tailWord_1139190).sum := by decide
  have hdescent : baseEnd_1139190 < baseStart_1139190 := by decide
  rcases family_descends (prefixWord ++ tailWord_1139190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1139203 : List Nat := [1, 1, 1, 3, 2, 1, 3, 3, 3, 4]
def baseStart_1139203 : Nat := 118140960795 + 1139203 * 2 ^ 59
def prefixEnd_1139203 : Nat := 4983230072969 + 3 ^ 40 * 1139203 * 2
def baseEnd_1139203 : Nat := 389972468029341064482271

theorem tailTrace_1139203 : CollatzResearch.WordTrace tailWord_1139203 prefixEnd_1139203 389972468029341064482271 := by
  unfold tailWord_1139203
  simp only [CollatzResearch.WordTrace]
  refine ⟨41550146891869566227766263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27700097927913044151844175 41550146891869566227766263)
  ·
    refine ⟨62325220337804349341649395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41550146891869566227766263 62325220337804349341649395)
    ·
      refine ⟨93487830506706524012474093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62325220337804349341649395 93487830506706524012474093)
      ·
        refine ⟨35057936440014946504677785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 93487830506706524012474093 35057936440014946504677785)
        ·
          refine ⟨26293452330011209878508339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35057936440014946504677785 26293452330011209878508339)
          ·
            refine ⟨39440178495016814817762509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26293452330011209878508339 39440178495016814817762509)
            ·
              refine ⟨14790066935631305556660941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39440178495016814817762509 14790066935631305556660941)
              ·
                refine ⟨5546275100861739583747853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14790066935631305556660941 5546275100861739583747853)
                ·
                  refine ⟨2079853162823152343905445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5546275100861739583747853 2079853162823152343905445)
                  ·
                    refine ⟨389972468029341064482271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2079853162823152343905445 389972468029341064482271)
                    ·
                      rfl

theorem cell22_1139203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 3, 3, 4].length) (baseStart_1139203 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1139203 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1139203 prefixEnd_1139203 := by exact prefixLift 1139203
  have htrace : WordTrace (prefixWord ++ tailWord_1139203) baseStart_1139203 baseEnd_1139203 := by
    simpa [prefixWord, tailWord_1139203, baseEnd_1139203] using wordTrace_append hprefix tailTrace_1139203
  have hstable : (prefixWord ++ tailWord_1139203).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1139203).length < 2 ^ (prefixWord ++ tailWord_1139203).sum := by decide
  have hdescent : baseEnd_1139203 < baseStart_1139203 := by decide
  rcases family_descends (prefixWord ++ tailWord_1139203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1139235 : List Nat := [1, 1, 1, 4, 4, 2, 2, 1, 6]
def baseStart_1139235 : Nat := 118140960795 + 1139235 * 2 ^ 59
def prefixEnd_1139235 : Nat := 4983230072969 + 3 ^ 40 * 1139235 * 2
def baseEnd_1139235 : Nat := 129994474094434549227391

theorem tailTrace_1139235 : CollatzResearch.WordTrace tailWord_1139235 prefixEnd_1139235 129994474094434549227391 := by
  unfold tailWord_1139235
  simp only [CollatzResearch.WordTrace]
  refine ⟨41551314027753635692931159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27700876018502423795287439 41551314027753635692931159)
  ·
    refine ⟨62326971041630453539396739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41551314027753635692931159 62326971041630453539396739)
    ·
      refine ⟨93490456562445680309095109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62326971041630453539396739 93490456562445680309095109)
      ·
        refine ⟨17529460605458565057955333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 93490456562445680309095109 17529460605458565057955333)
        ·
          refine ⟨3286773863523480948366625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17529460605458565057955333 3286773863523480948366625)
          ·
            refine ⟨2465080397642610711274969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3286773863523480948366625 2465080397642610711274969)
            ·
              refine ⟨1848810298231958033456227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2465080397642610711274969 1848810298231958033456227)
              ·
                refine ⟨2773215447347937050184341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1848810298231958033456227 2773215447347937050184341)
                ·
                  refine ⟨129994474094434549227391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2773215447347937050184341 129994474094434549227391)
                  ·
                    rfl

theorem cell22_1139235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 2, 1, 6].length) (baseStart_1139235 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1139235 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1139235 prefixEnd_1139235 := by exact prefixLift 1139235
  have htrace : WordTrace (prefixWord ++ tailWord_1139235) baseStart_1139235 baseEnd_1139235 := by
    simpa [prefixWord, tailWord_1139235, baseEnd_1139235] using wordTrace_append hprefix tailTrace_1139235
  have hstable : (prefixWord ++ tailWord_1139235).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1139235).length < 2 ^ (prefixWord ++ tailWord_1139235).sum := by decide
  have hdescent : baseEnd_1139235 < baseStart_1139235 := by decide
  rcases family_descends (prefixWord ++ tailWord_1139235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1139248 : List Nat := [2, 1, 1, 1, 2, 3, 3, 2, 1, 6]
def baseStart_1139248 : Nat := 118140960795 + 1139248 * 2 ^ 59
def prefixEnd_1139248 : Nat := 4983230072969 + 3 ^ 40 * 1139248 * 2
def baseEnd_1139248 : Nat := 389987872448975947107133

theorem tailTrace_1139248 : CollatzResearch.WordTrace tailWord_1139248 prefixEnd_1139248 389987872448975947107133 := by
  unfold tailWord_1139248
  simp only [CollatzResearch.WordTrace]
  refine ⟨20775894088353269456577199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27701192117804359275436265 20775894088353269456577199)
  ·
    refine ⟨31163841132529904184865799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20775894088353269456577199 31163841132529904184865799)
    ·
      refine ⟨46745761698794856277298699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31163841132529904184865799 46745761698794856277298699)
      ·
        refine ⟨70118642548192284415948049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46745761698794856277298699 70118642548192284415948049)
        ·
          refine ⟨52588981911144213311961037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70118642548192284415948049 52588981911144213311961037)
          ·
            refine ⟨19720868216679079991985389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52588981911144213311961037 19720868216679079991985389)
            ·
              refine ⟨7395325581254654996994521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19720868216679079991985389 7395325581254654996994521)
              ·
                refine ⟨5546494185940991247745891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7395325581254654996994521 5546494185940991247745891)
                ·
                  refine ⟨8319741278911486871618837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5546494185940991247745891 8319741278911486871618837)
                  ·
                    refine ⟨389987872448975947107133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8319741278911486871618837 389987872448975947107133)
                    ·
                      rfl

theorem cell22_1139248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 3, 2, 1, 6].length) (baseStart_1139248 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1139248 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1139248 prefixEnd_1139248 := by exact prefixLift 1139248
  have htrace : WordTrace (prefixWord ++ tailWord_1139248) baseStart_1139248 baseEnd_1139248 := by
    simpa [prefixWord, tailWord_1139248, baseEnd_1139248] using wordTrace_append hprefix tailTrace_1139248
  have hstable : (prefixWord ++ tailWord_1139248).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1139248).length < 2 ^ (prefixWord ++ tailWord_1139248).sum := by decide
  have hdescent : baseEnd_1139248 < baseStart_1139248 := by decide
  rcases family_descends (prefixWord ++ tailWord_1139248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1139250 : List Nat := [3, 2, 1, 1, 2, 1, 5, 1, 1, 5]
def baseStart_1139250 : Nat := 118140960795 + 1139250 * 2 ^ 59
def prefixEnd_1139250 : Nat := 4983230072969 + 3 ^ 40 * 1139250 * 2
def baseEnd_1139250 : Nat := 389988557089848608557127

theorem tailTrace_1139250 : CollatzResearch.WordTrace tailWord_1139250 prefixEnd_1139250 389988557089848608557127 := by
  unfold tailWord_1139250
  simp only [CollatzResearch.WordTrace]
  refine ⟨10387965280674823313681801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27701240748466195503151469 10387965280674823313681801)
  ·
    refine ⟨7790973960506117485261351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10387965280674823313681801 7790973960506117485261351)
    ·
      refine ⟨11686460940759176227892027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7790973960506117485261351 11686460940759176227892027)
      ·
        refine ⟨17529691411138764341838041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11686460940759176227892027 17529691411138764341838041)
        ·
          refine ⟨13147268558354073256378531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17529691411138764341838041 13147268558354073256378531)
          ·
            refine ⟨19720902837531109884567797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13147268558354073256378531 19720902837531109884567797)
            ·
              refine ⟨1848834641018541551678231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 19720902837531109884567797 1848834641018541551678231)
              ·
                refine ⟨2773251961527812327517347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1848834641018541551678231 2773251961527812327517347)
                ·
                  refine ⟨4159877942291718491276021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2773251961527812327517347 4159877942291718491276021)
                  ·
                    refine ⟨389988557089848608557127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4159877942291718491276021 389988557089848608557127)
                    ·
                      rfl

theorem cell22_1139250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 5, 1, 1, 5].length) (baseStart_1139250 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1139250 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1139250 prefixEnd_1139250 := by exact prefixLift 1139250
  have htrace : WordTrace (prefixWord ++ tailWord_1139250) baseStart_1139250 baseEnd_1139250 := by
    simpa [prefixWord, tailWord_1139250, baseEnd_1139250] using wordTrace_append hprefix tailTrace_1139250
  have hstable : (prefixWord ++ tailWord_1139250).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1139250).length < 2 ^ (prefixWord ++ tailWord_1139250).sum := by decide
  have hdescent : baseEnd_1139250 < baseStart_1139250 := by decide
  rcases family_descends (prefixWord ++ tailWord_1139250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1139254 : List Nat := [5, 1, 2, 1, 2, 2, 2, 2, 1, 4]
def baseStart_1139254 : Nat := 118140960795 + 1139254 * 2 ^ 59
def prefixEnd_1139254 : Nat := 4983230072969 + 3 ^ 40 * 1139254 * 2
def baseEnd_1139254 : Nat := 389989926371593931457115

theorem tailTrace_1139254 : CollatzResearch.WordTrace tailWord_1139254 prefixEnd_1139254 389989926371593931457115 := by
  unfold tailWord_1139254
  simp only [CollatzResearch.WordTrace]
  refine ⟨2597000438417800121117051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 27701338009789867958581877 2597000438417800121117051)
  ·
    refine ⟨3895500657626700181675577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2597000438417800121117051 3895500657626700181675577)
    ·
      refine ⟨2921625493220025136256683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3895500657626700181675577 2921625493220025136256683)
      ·
        refine ⟨4382438239830037704385025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2921625493220025136256683 4382438239830037704385025)
        ·
          refine ⟨3286828679872528278288769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4382438239830037704385025 3286828679872528278288769)
          ·
            refine ⟨2465121509904396208716577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3286828679872528278288769 2465121509904396208716577)
            ·
              refine ⟨1848841132428297156537433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2465121509904396208716577 1848841132428297156537433)
              ·
                refine ⟨1386630849321222867403075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1848841132428297156537433 1386630849321222867403075)
                ·
                  refine ⟨2079946273981834301104613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1386630849321222867403075 2079946273981834301104613)
                  ·
                    refine ⟨389989926371593931457115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2079946273981834301104613 389989926371593931457115)
                    ·
                      rfl

theorem cell22_1139254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 2, 2, 1, 4].length) (baseStart_1139254 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1139254 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1139254 prefixEnd_1139254 := by exact prefixLift 1139254
  have htrace : WordTrace (prefixWord ++ tailWord_1139254) baseStart_1139254 baseEnd_1139254 := by
    simpa [prefixWord, tailWord_1139254, baseEnd_1139254] using wordTrace_append hprefix tailTrace_1139254
  have hstable : (prefixWord ++ tailWord_1139254).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1139254).length < 2 ^ (prefixWord ++ tailWord_1139254).sum := by decide
  have hdescent : baseEnd_1139254 < baseStart_1139254 := by decide
  rcases family_descends (prefixWord ++ tailWord_1139254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1139263 : List Nat := [1, 1, 2, 2, 3, 2, 3, 8]
def baseStart_1139263 : Nat := 118140960795 + 1139263 * 2 ^ 59
def prefixEnd_1139263 : Nat := 4983230072969 + 3 ^ 40 * 1139263 * 2
def baseEnd_1139263 : Nat := 43332556361724545331343

theorem tailTrace_1139263 : CollatzResearch.WordTrace tailWord_1139263 prefixEnd_1139263 43332556361724545331343 := by
  unfold tailWord_1139263
  simp only [CollatzResearch.WordTrace]
  refine ⟨41552335271652196474950443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27701556847768130983300295 41552335271652196474950443)
  ·
    refine ⟨62328502907478294712425665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41552335271652196474950443 62328502907478294712425665)
    ·
      refine ⟨46746377180608721034319249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62328502907478294712425665 46746377180608721034319249)
      ·
        refine ⟨35059782885456540775739437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46746377180608721034319249 35059782885456540775739437)
        ·
          refine ⟨13147418582046202790902289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35059782885456540775739437 13147418582046202790902289)
          ·
            refine ⟨9860563936534652093176717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13147418582046202790902289 9860563936534652093176717)
            ·
              refine ⟨3697711476200494534941269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9860563936534652093176717 3697711476200494534941269)
              ·
                refine ⟨43332556361724545331343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3697711476200494534941269 43332556361724545331343)
                ·
                  rfl

theorem cell22_1139263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 3, 8].length) (baseStart_1139263 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1139263 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1139263 prefixEnd_1139263 := by exact prefixLift 1139263
  have htrace : WordTrace (prefixWord ++ tailWord_1139263) baseStart_1139263 baseEnd_1139263 := by
    simpa [prefixWord, tailWord_1139263, baseEnd_1139263] using wordTrace_append hprefix tailTrace_1139263
  have hstable : (prefixWord ++ tailWord_1139263).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1139263).length < 2 ^ (prefixWord ++ tailWord_1139263).sum := by decide
  have hdescent : baseEnd_1139263 < baseStart_1139263 := by decide
  rcases family_descends (prefixWord ++ tailWord_1139263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1139265 : List Nat := [1, 2, 5, 1, 1, 2, 2, 1, 1, 6]
def baseStart_1139265 : Nat := 118140960795 + 1139265 * 2 ^ 59
def prefixEnd_1139265 : Nat := 4983230072969 + 3 ^ 40 * 1139265 * 2
def baseEnd_1139265 : Nat := 389993691896393569432081

theorem tailTrace_1139265 : CollatzResearch.WordTrace tailWord_1139265 prefixEnd_1139265 389993691896393569432081 := by
  unfold tailWord_1139265
  simp only [CollatzResearch.WordTrace]
  refine ⟨41552408217644950816523249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27701605478429967211015499 41552408217644950816523249)
  ·
    refine ⟨31164306163233713112392437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41552408217644950816523249 31164306163233713112392437)
    ·
      refine ⟨2921653702803160604286791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 31164306163233713112392437 2921653702803160604286791)
      ·
        refine ⟨4382480554204740906430187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2921653702803160604286791 4382480554204740906430187)
        ·
          refine ⟨6573720831307111359645281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4382480554204740906430187 6573720831307111359645281)
          ·
            refine ⟨4930290623480333519733961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6573720831307111359645281 4930290623480333519733961)
            ·
              refine ⟨3697717967610250139800471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4930290623480333519733961 3697717967610250139800471)
              ·
                refine ⟨5546576951415375209700707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3697717967610250139800471 5546576951415375209700707)
                ·
                  refine ⟨8319865427123062814551061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5546576951415375209700707 8319865427123062814551061)
                  ·
                    refine ⟨389993691896393569432081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8319865427123062814551061 389993691896393569432081)
                    ·
                      rfl

theorem cell22_1139265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 2, 1, 1, 6].length) (baseStart_1139265 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1139265 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1139265 prefixEnd_1139265 := by exact prefixLift 1139265
  have htrace : WordTrace (prefixWord ++ tailWord_1139265) baseStart_1139265 baseEnd_1139265 := by
    simpa [prefixWord, tailWord_1139265, baseEnd_1139265] using wordTrace_append hprefix tailTrace_1139265
  have hstable : (prefixWord ++ tailWord_1139265).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1139265).length < 2 ^ (prefixWord ++ tailWord_1139265).sum := by decide
  have hdescent : baseEnd_1139265 < baseStart_1139265 := by decide
  rcases family_descends (prefixWord ++ tailWord_1139265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1139301 : List Nat := [1, 3, 1, 3, 4, 2, 2, 1, 2, 3]
def baseStart_1139301 : Nat := 118140960795 + 1139301 * 2 ^ 59
def prefixEnd_1139301 : Nat := 4983230072969 + 3 ^ 40 * 1139301 * 2
def baseEnd_1139301 : Nat := 390006015432101475531971

theorem tailTrace_1139301 : CollatzResearch.WordTrace tailWord_1139301 prefixEnd_1139301 390006015432101475531971 := by
  unfold tailWord_1139301
  simp only [CollatzResearch.WordTrace]
  refine ⟨41553721245514528964833757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27702480830343019309889171 41553721245514528964833757)
  ·
    refine ⟨15582645467067948361812659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41553721245514528964833757 15582645467067948361812659)
    ·
      refine ⟨23373968200601922542718989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15582645467067948361812659 23373968200601922542718989)
      ·
        refine ⟨8765238075225720953519621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23373968200601922542718989 8765238075225720953519621)
        ·
          refine ⟨1643482139104822678784929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8765238075225720953519621 1643482139104822678784929)
          ·
            refine ⟨1232611604328617009088697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1643482139104822678784929 1232611604328617009088697)
            ·
              refine ⟨924458703246462756816523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1232611604328617009088697 924458703246462756816523)
              ·
                refine ⟨1386688054869694135224785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 924458703246462756816523 1386688054869694135224785)
                ·
                  refine ⟨1040016041152270601418589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1386688054869694135224785 1040016041152270601418589)
                  ·
                    refine ⟨390006015432101475531971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1040016041152270601418589 390006015432101475531971)
                    ·
                      rfl

theorem cell22_1139301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 2, 2, 1, 2, 3].length) (baseStart_1139301 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1139301 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1139301 prefixEnd_1139301 := by exact prefixLift 1139301
  have htrace : WordTrace (prefixWord ++ tailWord_1139301) baseStart_1139301 baseEnd_1139301 := by
    simpa [prefixWord, tailWord_1139301, baseEnd_1139301] using wordTrace_append hprefix tailTrace_1139301
  have hstable : (prefixWord ++ tailWord_1139301).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1139301).length < 2 ^ (prefixWord ++ tailWord_1139301).sum := by decide
  have hdescent : baseEnd_1139301 < baseStart_1139301 := by decide
  rcases family_descends (prefixWord ++ tailWord_1139301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1139323 : List Nat := [1, 1, 1, 1, 1, 4, 2, 1, 3, 7]
def baseStart_1139323 : Nat := 118140960795 + 1139323 * 2 ^ 59
def prefixEnd_1139323 : Nat := 4983230072969 + 3 ^ 40 * 1139323 * 2
def baseEnd_1139323 : Nat := 390013546481700751481903

theorem tailTrace_1139323 : CollatzResearch.WordTrace tailWord_1139323 prefixEnd_1139323 390013546481700751481903 := by
  unfold tailWord_1139323
  simp only [CollatzResearch.WordTrace]
  refine ⟨41554523651434826722134623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27703015767623217814756415 41554523651434826722134623)
  ·
    refine ⟨62331785477152240083201935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41554523651434826722134623 62331785477152240083201935)
    ·
      refine ⟨93497678215728360124802903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62331785477152240083201935 93497678215728360124802903)
      ·
        refine ⟨140246517323592540187204355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93497678215728360124802903 140246517323592540187204355)
        ·
          refine ⟨210369775985388810280806533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 140246517323592540187204355 210369775985388810280806533)
          ·
            refine ⟨39444332997260401927651225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 210369775985388810280806533 39444332997260401927651225)
            ·
              refine ⟨29583249747945301445738419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39444332997260401927651225 29583249747945301445738419)
              ·
                refine ⟨44374874621917952168607629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29583249747945301445738419 44374874621917952168607629)
                ·
                  refine ⟨16640577983219232063227861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 44374874621917952168607629 16640577983219232063227861)
                  ·
                    refine ⟨390013546481700751481903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 16640577983219232063227861 390013546481700751481903)
                    ·
                      rfl

theorem cell22_1139323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 1, 3, 7].length) (baseStart_1139323 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1139323 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1139323 prefixEnd_1139323 := by exact prefixLift 1139323
  have htrace : WordTrace (prefixWord ++ tailWord_1139323) baseStart_1139323 baseEnd_1139323 := by
    simpa [prefixWord, tailWord_1139323, baseEnd_1139323] using wordTrace_append hprefix tailTrace_1139323
  have hstable : (prefixWord ++ tailWord_1139323).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1139323).length < 2 ^ (prefixWord ++ tailWord_1139323).sum := by decide
  have hdescent : baseEnd_1139323 < baseStart_1139323 := by decide
  rcases family_descends (prefixWord ++ tailWord_1139323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1139329 : List Nat := [1, 2, 4, 2, 1, 1, 2, 5, 1, 3]
def baseStart_1139329 : Nat := 118140960795 + 1139329 * 2 ^ 59
def prefixEnd_1139329 : Nat := 4983230072969 + 3 ^ 40 * 1139329 * 2
def baseEnd_1139329 : Nat := 390015600404318735831885

theorem tailTrace_1139329 : CollatzResearch.WordTrace tailWord_1139329 prefixEnd_1139329 390015600404318735831885 := by
  unfold tailWord_1139329
  simp only [CollatzResearch.WordTrace]
  refine ⟨41554742489413089746853041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27703161659608726497902027 41554742489413089746853041)
  ·
    refine ⟨31166056867059817310139781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41554742489413089746853041 31166056867059817310139781)
    ·
      refine ⟨5843635662573715745651209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31166056867059817310139781 5843635662573715745651209)
      ·
        refine ⟨4382726746930286809238407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5843635662573715745651209 4382726746930286809238407)
        ·
          refine ⟨6574090120395430213857611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4382726746930286809238407 6574090120395430213857611)
          ·
            refine ⟨9861135180593145320786417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6574090120395430213857611 9861135180593145320786417)
            ·
              refine ⟨7395851385444858990589813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9861135180593145320786417 7395851385444858990589813)
              ·
                refine ⟨693361067385455530367795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7395851385444858990589813 693361067385455530367795)
                ·
                  refine ⟨1040041601078183295551693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 693361067385455530367795 1040041601078183295551693)
                  ·
                    refine ⟨390015600404318735831885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1040041601078183295551693 390015600404318735831885)
                    ·
                      rfl

theorem cell22_1139329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 2, 5, 1, 3].length) (baseStart_1139329 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1139329 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1139329 prefixEnd_1139329 := by exact prefixLift 1139329
  have htrace : WordTrace (prefixWord ++ tailWord_1139329) baseStart_1139329 baseEnd_1139329 := by
    simpa [prefixWord, tailWord_1139329, baseEnd_1139329] using wordTrace_append hprefix tailTrace_1139329
  have hstable : (prefixWord ++ tailWord_1139329).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1139329).length < 2 ^ (prefixWord ++ tailWord_1139329).sum := by decide
  have hdescent : baseEnd_1139329 < baseStart_1139329 := by decide
  rcases family_descends (prefixWord ++ tailWord_1139329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1139342 : List Nat := [4, 1, 1, 3, 1, 1, 4, 2, 5]
def baseStart_1139342 : Nat := 118140960795 + 1139342 * 2 ^ 59
def prefixEnd_1139342 : Nat := 4983230072969 + 3 ^ 40 * 1139342 * 2
def baseEnd_1139342 : Nat := 130006683523330345085615

theorem tailTrace_1139342 : CollatzResearch.WordTrace tailWord_1139342 prefixEnd_1139342 130006683523330345085615 := by
  unfold tailWord_1139342
  simp only [CollatzResearch.WordTrace]
  refine ⟨5194402079795749120884535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27703477758910661978050853 5194402079795749120884535)
  ·
    refine ⟨7791603119693623681326803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5194402079795749120884535 7791603119693623681326803)
    ·
      refine ⟨11687404679540435521990205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7791603119693623681326803 11687404679540435521990205)
      ·
        refine ⟨4382776754827663320746327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11687404679540435521990205 4382776754827663320746327)
        ·
          refine ⟨6574165132241494981119491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4382776754827663320746327 6574165132241494981119491)
          ·
            refine ⟨9861247698362242471679237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6574165132241494981119491 9861247698362242471679237)
            ·
              refine ⟨1848983943442920463439857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9861247698362242471679237 1848983943442920463439857)
              ·
                refine ⟨1386737957582190347579893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1848983943442920463439857 1386737957582190347579893)
                ·
                  refine ⟨130006683523330345085615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1386737957582190347579893 130006683523330345085615)
                  ·
                    rfl

theorem cell22_1139342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 4, 2, 5].length) (baseStart_1139342 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1139342 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1139342 prefixEnd_1139342 := by exact prefixLift 1139342
  have htrace : WordTrace (prefixWord ++ tailWord_1139342) baseStart_1139342 baseEnd_1139342 := by
    simpa [prefixWord, tailWord_1139342, baseEnd_1139342] using wordTrace_append hprefix tailTrace_1139342
  have hstable : (prefixWord ++ tailWord_1139342).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1139342).length < 2 ^ (prefixWord ++ tailWord_1139342).sum := by decide
  have hdescent : baseEnd_1139342 < baseStart_1139342 := by decide
  rcases family_descends (prefixWord ++ tailWord_1139342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1139346 : List Nat := [3, 2, 3, 1, 2, 2, 1, 4, 1, 3]
def baseStart_1139346 : Nat := 118140960795 + 1139346 * 2 ^ 59
def prefixEnd_1139346 : Nat := 4983230072969 + 3 ^ 40 * 1139346 * 2
def baseEnd_1139346 : Nat := 390021419851736358156833

theorem tailTrace_1139346 : CollatzResearch.WordTrace tailWord_1139346 prefixEnd_1139346 390021419851736358156833 := by
  unfold tailWord_1139346
  simp only [CollatzResearch.WordTrace]
  refine ⟨10388840632587875412555473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27703575020234334433481261 10388840632587875412555473)
  ·
    refine ⟨7791630474440906559416605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10388840632587875412555473 7791630474440906559416605)
    ·
      refine ⟨2921861427915339959781227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7791630474440906559416605 2921861427915339959781227)
      ·
        refine ⟨4382792141873009939671841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2921861427915339959781227 4382792141873009939671841)
        ·
          refine ⟨3287094106404757454753881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4382792141873009939671841 3287094106404757454753881)
          ·
            refine ⟨2465320579803568091065411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3287094106404757454753881 2465320579803568091065411)
            ·
              refine ⟨3697980869705352136598117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2465320579803568091065411 3697980869705352136598117)
              ·
                refine ⟨693371413069753525612147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3697980869705352136598117 693371413069753525612147)
                ·
                  refine ⟨1040057119604630288418221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 693371413069753525612147 1040057119604630288418221)
                  ·
                    refine ⟨390021419851736358156833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1040057119604630288418221 390021419851736358156833)
                    ·
                      rfl

theorem cell22_1139346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 1, 4, 1, 3].length) (baseStart_1139346 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1139346 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1139346 prefixEnd_1139346 := by exact prefixLift 1139346
  have htrace : WordTrace (prefixWord ++ tailWord_1139346) baseStart_1139346 baseEnd_1139346 := by
    simpa [prefixWord, tailWord_1139346, baseEnd_1139346] using wordTrace_append hprefix tailTrace_1139346
  have hstable : (prefixWord ++ tailWord_1139346).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1139346).length < 2 ^ (prefixWord ++ tailWord_1139346).sum := by decide
  have hdescent : baseEnd_1139346 < baseStart_1139346 := by decide
  rcases family_descends (prefixWord ++ tailWord_1139346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1139389 : List Nat := [1, 4, 1, 2, 1, 3, 4, 1, 1, 4]
def baseStart_1139389 : Nat := 118140960795 + 1139389 * 2 ^ 59
def prefixEnd_1139389 : Nat := 4983230072969 + 3 ^ 40 * 1139389 * 2
def baseEnd_1139389 : Nat := 390036139630498579331701

theorem tailTrace_1139389 : CollatzResearch.WordTrace tailWord_1139389 prefixEnd_1139389 390036139630498579331701 := by
  unfold tailWord_1139389
  simp only [CollatzResearch.WordTrace]
  refine ⟨41556930869195719994037221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27704620579463813329358147 41556930869195719994037221)
  ·
    refine ⟨7791924537974197498881979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 41556930869195719994037221 7791924537974197498881979)
    ·
      refine ⟨11687886806961296248322969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7791924537974197498881979 11687886806961296248322969)
      ·
        refine ⟨8765915105220972186242227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11687886806961296248322969 8765915105220972186242227)
        ·
          refine ⟨13148872657831458279363341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8765915105220972186242227 13148872657831458279363341)
          ·
            refine ⟨4930827246686796854761253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13148872657831458279363341 4930827246686796854761253)
            ·
              refine ⟨924530108753774410267735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4930827246686796854761253 924530108753774410267735)
              ·
                refine ⟨1386795163130661615401603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 924530108753774410267735 1386795163130661615401603)
                ·
                  refine ⟨2080192744695992423102405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1386795163130661615401603 2080192744695992423102405)
                  ·
                    refine ⟨390036139630498579331701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2080192744695992423102405 390036139630498579331701)
                    ·
                      rfl

theorem cell22_1139389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 4, 1, 1, 4].length) (baseStart_1139389 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1139389 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1139389 prefixEnd_1139389 := by exact prefixLift 1139389
  have htrace : WordTrace (prefixWord ++ tailWord_1139389) baseStart_1139389 baseEnd_1139389 := by
    simpa [prefixWord, tailWord_1139389, baseEnd_1139389] using wordTrace_append hprefix tailTrace_1139389
  have hstable : (prefixWord ++ tailWord_1139389).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1139389).length < 2 ^ (prefixWord ++ tailWord_1139389).sum := by decide
  have hdescent : baseEnd_1139389 < baseStart_1139389 := by decide
  rcases family_descends (prefixWord ++ tailWord_1139389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1139393 : List Nat := [1, 2, 6, 2, 2, 1, 1, 2, 5]
def baseStart_1139393 : Nat := 118140960795 + 1139393 * 2 ^ 59
def prefixEnd_1139393 : Nat := 4983230072969 + 3 ^ 40 * 1139393 * 2
def baseEnd_1139393 : Nat := 130012502970747967410563

theorem tailTrace_1139393 : CollatzResearch.WordTrace tailWord_1139393 prefixEnd_1139393 130012502970747967410563 := by
  unfold tailWord_1139393
  simp only [CollatzResearch.WordTrace]
  refine ⟨41557076761181228677182833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27704717840787485784788555 41557076761181228677182833)
  ·
    refine ⟨31167807570885921507887125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41557076761181228677182833 31167807570885921507887125)
    ·
      refine ⟨1460990979885277570682209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 31167807570885921507887125 1460990979885277570682209)
      ·
        refine ⟨1095743234913958178011657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1460990979885277570682209 1095743234913958178011657)
        ·
          refine ⟨821807426185468633508743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1095743234913958178011657 821807426185468633508743)
          ·
            refine ⟨1232711139278202950263115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 821807426185468633508743 1232711139278202950263115)
            ·
              refine ⟨1849066708917304425394673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1232711139278202950263115 1849066708917304425394673)
              ·
                refine ⟨1386800031687978319046005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1849066708917304425394673 1386800031687978319046005)
                ·
                  refine ⟨130012502970747967410563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1386800031687978319046005 130012502970747967410563)
                  ·
                    rfl

theorem cell22_1139393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 2, 1, 1, 2, 5].length) (baseStart_1139393 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1139393 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1139393 prefixEnd_1139393 := by exact prefixLift 1139393
  have htrace : WordTrace (prefixWord ++ tailWord_1139393) baseStart_1139393 baseEnd_1139393 := by
    simpa [prefixWord, tailWord_1139393, baseEnd_1139393] using wordTrace_append hprefix tailTrace_1139393
  have hstable : (prefixWord ++ tailWord_1139393).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1139393).length < 2 ^ (prefixWord ++ tailWord_1139393).sum := by decide
  have hdescent : baseEnd_1139393 < baseStart_1139393 := by decide
  rcases family_descends (prefixWord ++ tailWord_1139393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1139404 : List Nat := [2, 2, 1, 5, 1, 1, 2, 4, 4]
def baseStart_1139404 : Nat := 118140960795 + 1139404 * 2 ^ 59
def prefixEnd_1139404 : Nat := 4983230072969 + 3 ^ 40 * 1139404 * 2
def baseEnd_1139404 : Nat := 130013758145681180068885

theorem tailTrace_1139404 : CollatzResearch.WordTrace tailWord_1139404 prefixEnd_1139404 130013758145681180068885 := by
  unfold tailWord_1139404
  simp only [CollatzResearch.WordTrace]
  refine ⟨20778738982070688777916633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27704985309427585037222177 20778738982070688777916633)
  ·
    refine ⟨15584054236553016583437475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20778738982070688777916633 15584054236553016583437475)
    ·
      refine ⟨23376081354829524875156213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15584054236553016583437475 23376081354829524875156213)
      ·
        refine ⟨2191507627015267957045895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 23376081354829524875156213 2191507627015267957045895)
        ·
          refine ⟨3287261440522901935568843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2191507627015267957045895 3287261440522901935568843)
          ·
            refine ⟨4930892160784352903353265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3287261440522901935568843 4930892160784352903353265)
            ·
              refine ⟨3698169120588264677514949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4930892160784352903353265 3698169120588264677514949)
              ·
                refine ⟨693406710110299627034053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3698169120588264677514949 693406710110299627034053)
                ·
                  refine ⟨130013758145681180068885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 693406710110299627034053 130013758145681180068885)
                  ·
                    rfl

theorem cell22_1139404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 2, 4, 4].length) (baseStart_1139404 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1139404 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1139404 prefixEnd_1139404 := by exact prefixLift 1139404
  have htrace : WordTrace (prefixWord ++ tailWord_1139404) baseStart_1139404 baseEnd_1139404 := by
    simpa [prefixWord, tailWord_1139404, baseEnd_1139404] using wordTrace_append hprefix tailTrace_1139404
  have hstable : (prefixWord ++ tailWord_1139404).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1139404).length < 2 ^ (prefixWord ++ tailWord_1139404).sum := by decide
  have hdescent : baseEnd_1139404 < baseStart_1139404 := by decide
  rcases family_descends (prefixWord ++ tailWord_1139404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1139432 : List Nat := [2, 1, 4, 1, 4, 1, 1, 8]
def baseStart_1139432 : Nat := 118140960795 + 1139432 * 2 ^ 59
def prefixEnd_1139432 : Nat := 4983230072969 + 3 ^ 40 * 1139432 * 2
def baseEnd_1139432 : Nat := 43338984378806755611841

theorem tailTrace_1139432 : CollatzResearch.WordTrace tailWord_1139432 prefixEnd_1139432 43338984378806755611841 := by
  unfold tailWord_1139432
  simp only [CollatzResearch.WordTrace]
  refine ⟨20779249604019969168926275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27705666138693292225235033 20779249604019969168926275)
  ·
    refine ⟨31168874406029953753389413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20779249604019969168926275 31168874406029953753389413)
    ·
      refine ⟨5844163951130616328760515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31168874406029953753389413 5844163951130616328760515)
      ·
        refine ⟨8766245926695924493140773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5844163951130616328760515 8766245926695924493140773)
        ·
          refine ⟨1643671111255485842463895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8766245926695924493140773 1643671111255485842463895)
          ·
            refine ⟨2465506666883228763695843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1643671111255485842463895 2465506666883228763695843)
            ·
              refine ⟨3698260000324843145543765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2465506666883228763695843 3698260000324843145543765)
              ·
                refine ⟨43338984378806755611841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3698260000324843145543765 43338984378806755611841)
                ·
                  rfl

theorem cell22_1139432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 1, 8].length) (baseStart_1139432 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1139432 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1139432 prefixEnd_1139432 := by exact prefixLift 1139432
  have htrace : WordTrace (prefixWord ++ tailWord_1139432) baseStart_1139432 baseEnd_1139432 := by
    simpa [prefixWord, tailWord_1139432, baseEnd_1139432] using wordTrace_append hprefix tailTrace_1139432
  have hstable : (prefixWord ++ tailWord_1139432).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1139432).length < 2 ^ (prefixWord ++ tailWord_1139432).sum := by decide
  have hdescent : baseEnd_1139432 < baseStart_1139432 := by decide
  rcases family_descends (prefixWord ++ tailWord_1139432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1139464 : List Nat := [2, 1, 3, 2, 2, 2, 3, 1, 3, 3]
def baseStart_1139464 : Nat := 118140960795 + 1139464 * 2 ^ 59
def prefixEnd_1139464 : Nat := 4983230072969 + 3 ^ 40 * 1139464 * 2
def baseEnd_1139464 : Nat := 390061813663223383706471

theorem tailTrace_1139464 : CollatzResearch.WordTrace tailWord_1139464 prefixEnd_1139464 390061813663223383706471 := by
  unfold tailWord_1139464
  simp only [CollatzResearch.WordTrace]
  refine ⟨20779833171962003901508723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27706444229282671868678297 20779833171962003901508723)
  ·
    refine ⟨31169749757943005852263085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20779833171962003901508723 31169749757943005852263085)
    ·
      refine ⟨11688656159228627194598657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31169749757943005852263085 11688656159228627194598657)
      ·
        refine ⟨8766492119421470395948993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11688656159228627194598657 8766492119421470395948993)
        ·
          refine ⟨6574869089566102796961745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8766492119421470395948993 6574869089566102796961745)
          ·
            refine ⟨4931151817174577097721309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6574869089566102796961745 4931151817174577097721309)
            ·
              refine ⟨1849181931440466411645491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4931151817174577097721309 1849181931440466411645491)
              ·
                refine ⟨2773772897160699617468237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1849181931440466411645491 2773772897160699617468237)
                ·
                  refine ⟨1040164836435262356550589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2773772897160699617468237 1040164836435262356550589)
                  ·
                    refine ⟨390061813663223383706471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1040164836435262356550589 390061813663223383706471)
                    ·
                      rfl

theorem cell22_1139464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 3, 1, 3, 3].length) (baseStart_1139464 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1139464 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1139464 prefixEnd_1139464 := by exact prefixLift 1139464
  have htrace : WordTrace (prefixWord ++ tailWord_1139464) baseStart_1139464 baseEnd_1139464 := by
    simpa [prefixWord, tailWord_1139464, baseEnd_1139464] using wordTrace_append hprefix tailTrace_1139464
  have hstable : (prefixWord ++ tailWord_1139464).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1139464).length < 2 ^ (prefixWord ++ tailWord_1139464).sum := by decide
  have hdescent : baseEnd_1139464 < baseStart_1139464 := by decide
  rcases family_descends (prefixWord ++ tailWord_1139464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1139475 : List Nat := [1, 1, 1, 2, 1, 3, 4, 1, 1, 7]
def baseStart_1139475 : Nat := 118140960795 + 1139475 * 2 ^ 59
def prefixEnd_1139475 : Nat := 4983230072969 + 3 ^ 40 * 1139475 * 2
def baseEnd_1139475 : Nat := 390065579188023021681437

theorem tailTrace_1139475 : CollatzResearch.WordTrace tailWord_1139475 prefixEnd_1139475 390065579188023021681437 := by
  unfold tailWord_1139475
  simp only [CollatzResearch.WordTrace]
  refine ⟨41560067546884156681667879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27706711697922771121111919 41560067546884156681667879)
  ·
    refine ⟨62340101320326235022501819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41560067546884156681667879 62340101320326235022501819)
    ·
      refine ⟨93510151980489352533752729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62340101320326235022501819 93510151980489352533752729)
      ·
        refine ⟨70132613985367014400314547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93510151980489352533752729 70132613985367014400314547)
        ·
          refine ⟨105198920978050521600471821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70132613985367014400314547 105198920978050521600471821)
          ·
            refine ⟨39449595366768945600176933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 105198920978050521600471821 39449595366768945600176933)
            ·
              refine ⟨7396799131269177300033175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 39449595366768945600176933 7396799131269177300033175)
              ·
                refine ⟨11095198696903765950049763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7396799131269177300033175 11095198696903765950049763)
                ·
                  refine ⟨16642798045355648925074645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11095198696903765950049763 16642798045355648925074645)
                  ·
                    refine ⟨390065579188023021681437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 16642798045355648925074645 390065579188023021681437)
                    ·
                      rfl

theorem cell22_1139475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 4, 1, 1, 7].length) (baseStart_1139475 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1139475 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1139475 prefixEnd_1139475 := by exact prefixLift 1139475
  have htrace : WordTrace (prefixWord ++ tailWord_1139475) baseStart_1139475 baseEnd_1139475 := by
    simpa [prefixWord, tailWord_1139475, baseEnd_1139475] using wordTrace_append hprefix tailTrace_1139475
  have hstable : (prefixWord ++ tailWord_1139475).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1139475).length < 2 ^ (prefixWord ++ tailWord_1139475).sum := by decide
  have hdescent : baseEnd_1139475 < baseStart_1139475 := by decide
  rcases family_descends (prefixWord ++ tailWord_1139475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1139477 : List Nat := [1, 3, 2, 1, 2, 2, 3, 3, 5]
def baseStart_1139477 : Nat := 118140960795 + 1139477 * 2 ^ 59
def prefixEnd_1139477 : Nat := 4983230072969 + 3 ^ 40 * 1139477 * 2
def baseEnd_1139477 : Nat := 130022087942965227710477

theorem tailTrace_1139477 : CollatzResearch.WordTrace tailWord_1139477 prefixEnd_1139477 130022087942965227710477 := by
  unfold tailWord_1139477
  simp only [CollatzResearch.WordTrace]
  refine ⟨41560140492876911023240685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27706760328584607348827123 41560140492876911023240685)
  ·
    refine ⟨15585052684828841633715257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41560140492876911023240685 15585052684828841633715257)
    ·
      refine ⟨11688789513621631225286443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15585052684828841633715257 11688789513621631225286443)
      ·
        refine ⟨17533184270432446837929665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11688789513621631225286443 17533184270432446837929665)
        ·
          refine ⟨13149888202824335128447249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17533184270432446837929665 13149888202824335128447249)
          ·
            refine ⟨9862416152118251346335437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13149888202824335128447249 9862416152118251346335437)
            ·
              refine ⟨3698406057044344254875789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9862416152118251346335437 3698406057044344254875789)
              ·
                refine ⟨1386902271391629095578421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3698406057044344254875789 1386902271391629095578421)
                ·
                  refine ⟨130022087942965227710477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1386902271391629095578421 130022087942965227710477)
                  ·
                    rfl

theorem cell22_1139477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 3, 3, 5].length) (baseStart_1139477 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1139477 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1139477 prefixEnd_1139477 := by exact prefixLift 1139477
  have htrace : WordTrace (prefixWord ++ tailWord_1139477) baseStart_1139477 baseEnd_1139477 := by
    simpa [prefixWord, tailWord_1139477, baseEnd_1139477] using wordTrace_append hprefix tailTrace_1139477
  have hstable : (prefixWord ++ tailWord_1139477).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1139477).length < 2 ^ (prefixWord ++ tailWord_1139477).sum := by decide
  have hdescent : baseEnd_1139477 < baseStart_1139477 := by decide
  rcases family_descends (prefixWord ++ tailWord_1139477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1139552 : List Nat := [2, 1, 1, 3, 3, 1, 3, 1, 1, 6]
def baseStart_1139552 : Nat := 118140960795 + 1139552 * 2 ^ 59
def prefixEnd_1139552 : Nat := 4983230072969 + 3 ^ 40 * 1139552 * 2
def baseEnd_1139552 : Nat := 390091937861620487506201

theorem tailTrace_1139552 : CollatzResearch.WordTrace tailWord_1139552 prefixEnd_1139552 390091937861620487506201 := by
  unfold tailWord_1139552
  simp only [CollatzResearch.WordTrace]
  refine ⟨20781437983802599416110455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27708583978403465888147273 20781437983802599416110455)
  ·
    refine ⟨31172156975703899124165683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20781437983802599416110455 31172156975703899124165683)
    ·
      refine ⟨46758235463555848686248525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31172156975703899124165683 46758235463555848686248525)
      ·
        refine ⟨17534338298833443257343197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46758235463555848686248525 17534338298833443257343197)
        ·
          refine ⟨6575376862062541221503699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17534338298833443257343197 6575376862062541221503699)
          ·
            refine ⟨9863065293093811832255549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6575376862062541221503699 9863065293093811832255549)
            ·
              refine ⟨3698649484910179437095831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9863065293093811832255549 3698649484910179437095831)
              ·
                refine ⟨5547974227365269155643747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3698649484910179437095831 5547974227365269155643747)
                ·
                  refine ⟨8321961341047903733465621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5547974227365269155643747 8321961341047903733465621)
                  ·
                    refine ⟨390091937861620487506201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8321961341047903733465621 390091937861620487506201)
                    ·
                      rfl

theorem cell22_1139552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 3, 1, 1, 6].length) (baseStart_1139552 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1139552 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1139552 prefixEnd_1139552 := by exact prefixLift 1139552
  have htrace : WordTrace (prefixWord ++ tailWord_1139552) baseStart_1139552 baseEnd_1139552 := by
    simpa [prefixWord, tailWord_1139552, baseEnd_1139552] using wordTrace_append hprefix tailTrace_1139552
  have hstable : (prefixWord ++ tailWord_1139552).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1139552).length < 2 ^ (prefixWord ++ tailWord_1139552).sum := by decide
  have hdescent : baseEnd_1139552 < baseStart_1139552 := by decide
  rcases family_descends (prefixWord ++ tailWord_1139552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1139556 : List Nat := [2, 3, 1, 1, 4, 2, 2, 3, 4]
def baseStart_1139556 : Nat := 118140960795 + 1139556 * 2 ^ 59
def prefixEnd_1139556 : Nat := 4983230072969 + 3 ^ 40 * 1139556 * 2
def baseEnd_1139556 : Nat := 130031102381121936802063

theorem tailTrace_1139556 : CollatzResearch.WordTrace tailWord_1139556 prefixEnd_1139556 130031102381121936802063 := by
  unfold tailWord_1139556
  simp only [CollatzResearch.WordTrace]
  refine ⟨20781510929795353757683261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27708681239727138343577681 20781510929795353757683261)
  ·
    refine ⟨7793066598673257659131223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20781510929795353757683261 7793066598673257659131223)
    ·
      refine ⟨11689599898009886488696835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7793066598673257659131223 11689599898009886488696835)
      ·
        refine ⟨17534399847014829733045253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11689599898009886488696835 17534399847014829733045253)
        ·
          refine ⟨3287699971315280574945985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17534399847014829733045253 3287699971315280574945985)
          ·
            refine ⟨2465774978486460431209489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3287699971315280574945985 2465774978486460431209489)
            ·
              refine ⟨1849331233864845323407117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2465774978486460431209489 1849331233864845323407117)
              ·
                refine ⟨693499212699316996277669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1849331233864845323407117 693499212699316996277669)
                ·
                  refine ⟨130031102381121936802063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 693499212699316996277669 130031102381121936802063)
                  ·
                    rfl

theorem cell22_1139556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 2, 3, 4].length) (baseStart_1139556 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1139556 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1139556 prefixEnd_1139556 := by exact prefixLift 1139556
  have htrace : WordTrace (prefixWord ++ tailWord_1139556) baseStart_1139556 baseEnd_1139556 := by
    simpa [prefixWord, tailWord_1139556, baseEnd_1139556] using wordTrace_append hprefix tailTrace_1139556
  have hstable : (prefixWord ++ tailWord_1139556).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1139556).length < 2 ^ (prefixWord ++ tailWord_1139556).sum := by decide
  have hdescent : baseEnd_1139556 < baseStart_1139556 := by decide
  rcases family_descends (prefixWord ++ tailWord_1139556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1139633 : List Nat := [1, 2, 2, 4, 3, 2, 1, 1, 3, 3]
def baseStart_1139633 : Nat := 118140960795 + 1139633 * 2 ^ 59
def prefixEnd_1139633 : Nat := 4983230072969 + 3 ^ 40 * 1139633 * 2
def baseEnd_1139633 : Nat := 390119665816963276230953

theorem tailTrace_1139633 : CollatzResearch.WordTrace tailWord_1139633 prefixEnd_1139633 390119665816963276230953 := by
  unfold tailWord_1139633
  simp only [CollatzResearch.WordTrace]
  refine ⟨41565830280311749665919553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27710553520207833110613035 41565830280311749665919553)
  ·
    refine ⟨31174372710233812249439665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41565830280311749665919553 31174372710233812249439665)
    ·
      refine ⟨23380779532675359187079749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31174372710233812249439665 23380779532675359187079749)
      ·
        refine ⟨4383896162376629847577453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23380779532675359187079749 4383896162376629847577453)
        ·
          refine ⟨1643961060891236192841545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4383896162376629847577453 1643961060891236192841545)
          ·
            refine ⟨1232970795668427144631159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1643961060891236192841545 1232970795668427144631159)
            ·
              refine ⟨1849456193502640716946739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1232970795668427144631159 1849456193502640716946739)
              ·
                refine ⟨2774184290253961075420109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1849456193502640716946739 2774184290253961075420109)
                ·
                  refine ⟨1040319108845235403282541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2774184290253961075420109 1040319108845235403282541)
                  ·
                    refine ⟨390119665816963276230953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1040319108845235403282541 390119665816963276230953)
                    ·
                      rfl

theorem cell22_1139633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 2, 1, 1, 3, 3].length) (baseStart_1139633 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1139633 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1139633 prefixEnd_1139633 := by exact prefixLift 1139633
  have htrace : WordTrace (prefixWord ++ tailWord_1139633) baseStart_1139633 baseEnd_1139633 := by
    simpa [prefixWord, tailWord_1139633, baseEnd_1139633] using wordTrace_append hprefix tailTrace_1139633
  have hstable : (prefixWord ++ tailWord_1139633).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1139633).length < 2 ^ (prefixWord ++ tailWord_1139633).sum := by decide
  have hdescent : baseEnd_1139633 < baseStart_1139633 := by decide
  rcases family_descends (prefixWord ++ tailWord_1139633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1139659 : List Nat := [1, 1, 1, 1, 3, 6, 1, 1, 3, 4]
def baseStart_1139659 : Nat := 118140960795 + 1139659 * 2 ^ 59
def prefixEnd_1139659 : Nat := 4983230072969 + 3 ^ 40 * 1139659 * 2
def baseEnd_1139659 : Nat := 390128566148307875080873

theorem tailTrace_1139659 : CollatzResearch.WordTrace tailWord_1139659 prefixEnd_1139659 390128566148307875080873 := by
  unfold tailWord_1139659
  simp only [CollatzResearch.WordTrace]
  refine ⟨41566778578217556106366031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27711185718811704070910687 41566778578217556106366031)
  ·
    refine ⟨62350167867326334159549047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41566778578217556106366031 62350167867326334159549047)
    ·
      refine ⟨93525251800989501239323571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62350167867326334159549047 93525251800989501239323571)
      ·
        refine ⟨140287877701484251858985357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93525251800989501239323571 140287877701484251858985357)
        ·
          refine ⟨52607954138056594447119509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 140287877701484251858985357 52607954138056594447119509)
          ·
            refine ⟨2465997850221402864708727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 52607954138056594447119509 2465997850221402864708727)
            ·
              refine ⟨3698996775332104297063091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2465997850221402864708727 3698996775332104297063091)
              ·
                refine ⟨5548495162998156445594637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3698996775332104297063091 5548495162998156445594637)
                ·
                  refine ⟨2080685686124308667097989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5548495162998156445594637 2080685686124308667097989)
                  ·
                    refine ⟨390128566148307875080873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2080685686124308667097989 390128566148307875080873)
                    ·
                      rfl

theorem cell22_1139659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 1, 1, 3, 4].length) (baseStart_1139659 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1139659 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1139659 prefixEnd_1139659 := by exact prefixLift 1139659
  have htrace : WordTrace (prefixWord ++ tailWord_1139659) baseStart_1139659 baseEnd_1139659 := by
    simpa [prefixWord, tailWord_1139659, baseEnd_1139659] using wordTrace_append hprefix tailTrace_1139659
  have hstable : (prefixWord ++ tailWord_1139659).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1139659).length < 2 ^ (prefixWord ++ tailWord_1139659).sum := by decide
  have hdescent : baseEnd_1139659 < baseStart_1139659 := by decide
  rcases family_descends (prefixWord ++ tailWord_1139659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1139740 : List Nat := [2, 2, 3, 1, 4, 2, 1, 2, 2, 3]
def baseStart_1139740 : Nat := 118140960795 + 1139740 * 2 ^ 59
def prefixEnd_1139740 : Nat := 4983230072969 + 3 ^ 40 * 1139740 * 2
def baseEnd_1139740 : Nat := 390156294103650663805625

theorem tailTrace_1139740 : CollatzResearch.WordTrace tailWord_1139740 prefixEnd_1139740 390156294103650663805625 := by
  unfold tailWord_1139740
  simp only [CollatzResearch.WordTrace]
  refine ⟨20784866445462053470032337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27713155260616071293376449 20784866445462053470032337)
  ·
    refine ⟨15588649834096540102524253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20784866445462053470032337 15588649834096540102524253)
    ·
      refine ⟨5845743687786202538446595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15588649834096540102524253 5845743687786202538446595)
      ·
        refine ⟨8768615531679303807669893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5845743687786202538446595 8768615531679303807669893)
        ·
          refine ⟨1644115412189869463938105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8768615531679303807669893 1644115412189869463938105)
          ·
            refine ⟨1233086559142402097953579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1644115412189869463938105 1233086559142402097953579)
            ·
              refine ⟨1849629838713603146930369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1233086559142402097953579 1849629838713603146930369)
              ·
                refine ⟨1387222379035202360197777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1849629838713603146930369 1387222379035202360197777)
                ·
                  refine ⟨1040416784276401770148333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1387222379035202360197777 1040416784276401770148333)
                  ·
                    refine ⟨390156294103650663805625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1040416784276401770148333 390156294103650663805625)
                    ·
                      rfl

theorem cell22_1139740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 2, 1, 2, 2, 3].length) (baseStart_1139740 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1139740 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1139740 prefixEnd_1139740 := by exact prefixLift 1139740
  have htrace : WordTrace (prefixWord ++ tailWord_1139740) baseStart_1139740 baseEnd_1139740 := by
    simpa [prefixWord, tailWord_1139740, baseEnd_1139740] using wordTrace_append hprefix tailTrace_1139740
  have hstable : (prefixWord ++ tailWord_1139740).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1139740).length < 2 ^ (prefixWord ++ tailWord_1139740).sum := by decide
  have hdescent : baseEnd_1139740 < baseStart_1139740 := by decide
  rcases family_descends (prefixWord ++ tailWord_1139740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1139841 : List Nat := [1, 2, 4, 2, 2, 1, 1, 1, 3, 5]
def baseStart_1139841 : Nat := 118140960795 + 1139841 * 2 ^ 59
def prefixEnd_1139841 : Nat := 4983230072969 + 3 ^ 40 * 1139841 * 2
def baseEnd_1139841 : Nat := 390190868467720067030315

theorem tailTrace_1139841 : CollatzResearch.WordTrace tailWord_1139841 prefixEnd_1139841 390190868467720067030315 := by
  unfold tailWord_1139841
  simp only [CollatzResearch.WordTrace]
  refine ⟨41573416663558201189491377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27715611109038800792994251 41573416663558201189491377)
  ·
    refine ⟨31180062497668650892118533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41573416663558201189491377 31180062497668650892118533)
    ·
      refine ⟨5846261718312872042272225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31180062497668650892118533 5846261718312872042272225)
      ·
        refine ⟨4384696288734654031704169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5846261718312872042272225 4384696288734654031704169)
        ·
          refine ⟨3288522216550990523778127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4384696288734654031704169 3288522216550990523778127)
          ·
            refine ⟨4932783324826485785667191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3288522216550990523778127 4932783324826485785667191)
            ·
              refine ⟨7399174987239728678500787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4932783324826485785667191 7399174987239728678500787)
              ·
                refine ⟨11098762480859593017751181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7399174987239728678500787 11098762480859593017751181)
                ·
                  refine ⟨4162035930322347381656693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11098762480859593017751181 4162035930322347381656693)
                  ·
                    refine ⟨390190868467720067030315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4162035930322347381656693 390190868467720067030315)
                    ·
                      rfl

theorem cell22_1139841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 1, 1, 3, 5].length) (baseStart_1139841 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1139841 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1139841 prefixEnd_1139841 := by exact prefixLift 1139841
  have htrace : WordTrace (prefixWord ++ tailWord_1139841) baseStart_1139841 baseEnd_1139841 := by
    simpa [prefixWord, tailWord_1139841, baseEnd_1139841] using wordTrace_append hprefix tailTrace_1139841
  have hstable : (prefixWord ++ tailWord_1139841).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1139841).length < 2 ^ (prefixWord ++ tailWord_1139841).sum := by decide
  have hdescent : baseEnd_1139841 < baseStart_1139841 := by decide
  rcases family_descends (prefixWord ++ tailWord_1139841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1139845 : List Nat := [1, 3, 1, 1, 6, 1, 3, 1, 1, 4]
def baseStart_1139845 : Nat := 118140960795 + 1139845 * 2 ^ 59
def prefixEnd_1139845 : Nat := 4983230072969 + 3 ^ 40 * 1139845 * 2
def baseEnd_1139845 : Nat := 390192237749465389930303

theorem tailTrace_1139845 : CollatzResearch.WordTrace tailWord_1139845 prefixEnd_1139845 390192237749465389930303 := by
  unfold tailWord_1139845
  simp only [CollatzResearch.WordTrace]
  refine ⟨41573562555543709872636989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27715708370362473248424659 41573562555543709872636989)
  ·
    refine ⟨15590085958328891202238871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41573562555543709872636989 15590085958328891202238871)
    ·
      refine ⟨23385128937493336803358307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15590085958328891202238871 23385128937493336803358307)
      ·
        refine ⟨35077693406240005205037461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23385128937493336803358307 35077693406240005205037461)
        ·
          refine ⟨1644266878417500243986131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 35077693406240005205037461 1644266878417500243986131)
          ·
            refine ⟨2466400317626250365979197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1644266878417500243986131 2466400317626250365979197)
            ·
              refine ⟨924900119109843887242199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2466400317626250365979197 924900119109843887242199)
              ·
                refine ⟨1387350178664765830863299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 924900119109843887242199 1387350178664765830863299)
                ·
                  refine ⟨2081025267997148746294949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1387350178664765830863299 2081025267997148746294949)
                  ·
                    refine ⟨390192237749465389930303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2081025267997148746294949 390192237749465389930303)
                    ·
                      rfl

theorem cell22_1139845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 3, 1, 1, 4].length) (baseStart_1139845 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1139845 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1139845 prefixEnd_1139845 := by exact prefixLift 1139845
  have htrace : WordTrace (prefixWord ++ tailWord_1139845) baseStart_1139845 baseEnd_1139845 := by
    simpa [prefixWord, tailWord_1139845, baseEnd_1139845] using wordTrace_append hprefix tailTrace_1139845
  have hstable : (prefixWord ++ tailWord_1139845).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1139845).length < 2 ^ (prefixWord ++ tailWord_1139845).sum := by decide
  have hdescent : baseEnd_1139845 < baseStart_1139845 := by decide
  rcases family_descends (prefixWord ++ tailWord_1139845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1139894 : List Nat := [5, 1, 3, 2, 1, 1, 2, 3, 4]
def baseStart_1139894 : Nat := 118140960795 + 1139894 * 2 ^ 59
def prefixEnd_1139894 : Nat := 4983230072969 + 3 ^ 40 * 1139894 * 2
def baseEnd_1139894 : Nat := 130069670483615198485051

theorem tailTrace_1139894 : CollatzResearch.WordTrace tailWord_1139894 prefixEnd_1139894 130069670483615198485051 := by
  unfold tailWord_1139894
  simp only [CollatzResearch.WordTrace]
  refine ⟨2598459358272886952573171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 27716899821577460827447157 2598459358272886952573171)
  ·
    refine ⟨3897689037409330428859757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2598459358272886952573171 3897689037409330428859757)
    ·
      refine ⟨1461633389028498910822409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3897689037409330428859757 1461633389028498910822409)
      ·
        refine ⟨1096225041771374183116807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1461633389028498910822409 1096225041771374183116807)
        ·
          refine ⟨1644337562657061274675211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1096225041771374183116807 1644337562657061274675211)
          ·
            refine ⟨2466506343985591912012817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1644337562657061274675211 2466506343985591912012817)
            ·
              refine ⟨1849879757989193934009613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2466506343985591912012817 1849879757989193934009613)
              ·
                refine ⟨693704909245947725253605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1849879757989193934009613 693704909245947725253605)
                ·
                  refine ⟨130069670483615198485051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 693704909245947725253605 130069670483615198485051)
                  ·
                    rfl

theorem cell22_1139894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 2, 3, 4].length) (baseStart_1139894 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1139894 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1139894 prefixEnd_1139894 := by exact prefixLift 1139894
  have htrace : WordTrace (prefixWord ++ tailWord_1139894) baseStart_1139894 baseEnd_1139894 := by
    simpa [prefixWord, tailWord_1139894, baseEnd_1139894] using wordTrace_append hprefix tailTrace_1139894
  have hstable : (prefixWord ++ tailWord_1139894).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1139894).length < 2 ^ (prefixWord ++ tailWord_1139894).sum := by decide
  have hdescent : baseEnd_1139894 < baseStart_1139894 := by decide
  rcases family_descends (prefixWord ++ tailWord_1139894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1139954 : List Nat := [3, 2, 1, 3, 3, 2, 1, 3, 1, 3]
def baseStart_1139954 : Nat := 118140960795 + 1139954 * 2 ^ 59
def prefixEnd_1139954 : Nat := 4983230072969 + 3 ^ 40 * 1139954 * 2
def baseEnd_1139954 : Nat := 390229550677025438954969

theorem tailTrace_1139954 : CollatzResearch.WordTrace tailWord_1139954 prefixEnd_1139954 390229550677025438954969 := by
  unfold tailWord_1139954
  simp only [CollatzResearch.WordTrace]
  refine ⟨10394384528037205372088729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27718358741432547658903277 10394384528037205372088729)
  ·
    refine ⟨7795788396027904029066547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10394384528037205372088729 7795788396027904029066547)
    ·
      refine ⟨11693682594041856043599821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7795788396027904029066547 11693682594041856043599821)
      ·
        refine ⟨4385130972765696016349933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11693682594041856043599821 4385130972765696016349933)
        ·
          refine ⟨1644424114787136006131225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4385130972765696016349933 1644424114787136006131225)
          ·
            refine ⟨1233318086090352004598419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1644424114787136006131225 1233318086090352004598419)
            ·
              refine ⟨1849977129135528006897629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1233318086090352004598419 1849977129135528006897629)
              ·
                refine ⟨693741423425823002586611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1849977129135528006897629 693741423425823002586611)
                ·
                  refine ⟨1040612135138734503879917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 693741423425823002586611 1040612135138734503879917)
                  ·
                    refine ⟨390229550677025438954969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1040612135138734503879917 390229550677025438954969)
                    ·
                      rfl

theorem cell22_1139954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 2, 1, 3, 1, 3].length) (baseStart_1139954 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1139954 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1139954 prefixEnd_1139954 := by exact prefixLift 1139954
  have htrace : WordTrace (prefixWord ++ tailWord_1139954) baseStart_1139954 baseEnd_1139954 := by
    simpa [prefixWord, tailWord_1139954, baseEnd_1139954] using wordTrace_append hprefix tailTrace_1139954
  have hstable : (prefixWord ++ tailWord_1139954).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1139954).length < 2 ^ (prefixWord ++ tailWord_1139954).sum := by decide
  have hdescent : baseEnd_1139954 < baseStart_1139954 := by decide
  rcases family_descends (prefixWord ++ tailWord_1139954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1139997 : List Nat := [1, 4, 2, 3, 1, 3, 1, 2, 1, 4]
def baseStart_1139997 : Nat := 118140960795 + 1139997 * 2 ^ 59
def prefixEnd_1139997 : Nat := 4983230072969 + 3 ^ 40 * 1139997 * 2
def baseEnd_1139997 : Nat := 390244270455787660129837

theorem tailTrace_1139997 : CollatzResearch.WordTrace tailWord_1139997 prefixEnd_1139997 390244270455787660129837 := by
  unfold tailWord_1139997
  simp only [CollatzResearch.WordTrace]
  refine ⟨41579106450993039832170245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27719404300662026554780163 41579106450993039832170245)
  ·
    refine ⟨7796082459561194968531921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 41579106450993039832170245 7796082459561194968531921)
    ·
      refine ⟨5847061844670896226398941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7796082459561194968531921 5847061844670896226398941)
      ·
        refine ⟨2192648191751586084899603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5847061844670896226398941 2192648191751586084899603)
        ·
          refine ⟨3288972287627379127349405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2192648191751586084899603 3288972287627379127349405)
          ·
            refine ⟨1233364607860267172756027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3288972287627379127349405 1233364607860267172756027)
            ·
              refine ⟨1850046911790400759134041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1233364607860267172756027 1850046911790400759134041)
              ·
                refine ⟨1387535183842800569350531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1850046911790400759134041 1387535183842800569350531)
                ·
                  refine ⟨2081302775764200854025797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1387535183842800569350531 2081302775764200854025797)
                  ·
                    refine ⟨390244270455787660129837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2081302775764200854025797 390244270455787660129837)
                    ·
                      rfl

theorem cell22_1139997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 3, 1, 2, 1, 4].length) (baseStart_1139997 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1139997 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1139997 prefixEnd_1139997 := by exact prefixLift 1139997
  have htrace : WordTrace (prefixWord ++ tailWord_1139997) baseStart_1139997 baseEnd_1139997 := by
    simpa [prefixWord, tailWord_1139997, baseEnd_1139997] using wordTrace_append hprefix tailTrace_1139997
  have hstable : (prefixWord ++ tailWord_1139997).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1139997).length < 2 ^ (prefixWord ++ tailWord_1139997).sum := by decide
  have hdescent : baseEnd_1139997 < baseStart_1139997 := by decide
  rcases family_descends (prefixWord ++ tailWord_1139997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1140010 : List Nat := [3, 1, 4, 2, 1, 2, 1, 2, 1, 5]
def baseStart_1140010 : Nat := 118140960795 + 1140010 * 2 ^ 59
def prefixEnd_1140010 : Nat := 4983230072969 + 3 ^ 40 * 1140010 * 2
def baseEnd_1140010 : Nat := 390248720621459959554797

theorem tailTrace_1140010 : CollatzResearch.WordTrace tailWord_1140010 prefixEnd_1140010 390248720621459959554797 := by
  unfold tailWord_1140010
  simp only [CollatzResearch.WordTrace]
  refine ⟨10394895149986485763098371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27719720399963962034928989 10394895149986485763098371)
  ·
    refine ⟨15592342724979728644647557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10394895149986485763098371 15592342724979728644647557)
    ·
      refine ⟨2923564260933699120871417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15592342724979728644647557 2923564260933699120871417)
      ·
        refine ⟨2192673195700274340653563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2923564260933699120871417 2192673195700274340653563)
        ·
          refine ⟨3289009793550411510980345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2192673195700274340653563 3289009793550411510980345)
          ·
            refine ⟨2466757345162808633235259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3289009793550411510980345 2466757345162808633235259)
            ·
              refine ⟨3700136017744212949852889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2466757345162808633235259 3700136017744212949852889)
              ·
                refine ⟨2775102013308159712389667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3700136017744212949852889 2775102013308159712389667)
                ·
                  refine ⟨4162653019962239568584501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2775102013308159712389667 4162653019962239568584501)
                  ·
                    refine ⟨390248720621459959554797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4162653019962239568584501 390248720621459959554797)
                    ·
                      rfl

theorem cell22_1140010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 1, 2, 1, 5].length) (baseStart_1140010 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1140010 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1140010 prefixEnd_1140010 := by exact prefixLift 1140010
  have htrace : WordTrace (prefixWord ++ tailWord_1140010) baseStart_1140010 baseEnd_1140010 := by
    simpa [prefixWord, tailWord_1140010, baseEnd_1140010] using wordTrace_append hprefix tailTrace_1140010
  have hstable : (prefixWord ++ tailWord_1140010).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1140010).length < 2 ^ (prefixWord ++ tailWord_1140010).sum := by decide
  have hdescent : baseEnd_1140010 < baseStart_1140010 := by decide
  rcases family_descends (prefixWord ++ tailWord_1140010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1140055 : List Nat := [1, 1, 3, 2, 3, 3, 1, 2, 3, 3]
def baseStart_1140055 : Nat := 118140960795 + 1140055 * 2 ^ 59
def prefixEnd_1140055 : Nat := 4983230072969 + 3 ^ 40 * 1140055 * 2
def baseEnd_1140055 : Nat := 390264125041094842179659

theorem tailTrace_1140055 : CollatzResearch.WordTrace tailWord_1140055 prefixEnd_1140055 390264125041094842179659 := by
  unfold tailWord_1140055
  simp only [CollatzResearch.WordTrace]
  refine ⟨41581221884782915737781619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27720814589855277158521079 41581221884782915737781619)
  ·
    refine ⟨62371832827174373606672429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41581221884782915737781619 62371832827174373606672429)
    ·
      refine ⟨23389437310190390102502161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62371832827174373606672429 23389437310190390102502161)
      ·
        refine ⟨17542077982642792576876621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23389437310190390102502161 17542077982642792576876621)
        ·
          refine ⟨6578279243491047216328733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17542077982642792576876621 6578279243491047216328733)
          ·
            refine ⟨2466854716309142706123275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6578279243491047216328733 2466854716309142706123275)
            ·
              refine ⟨3700282074463714059184913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2466854716309142706123275 3700282074463714059184913)
              ·
                refine ⟨2775211555847785544388685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3700282074463714059184913 2775211555847785544388685)
                ·
                  refine ⟨1040704333442919579145757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2775211555847785544388685 1040704333442919579145757)
                  ·
                    refine ⟨390264125041094842179659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1040704333442919579145757 390264125041094842179659)
                    ·
                      rfl

theorem cell22_1140055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 1, 2, 3, 3].length) (baseStart_1140055 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1140055 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1140055 prefixEnd_1140055 := by exact prefixLift 1140055
  have htrace : WordTrace (prefixWord ++ tailWord_1140055) baseStart_1140055 baseEnd_1140055 := by
    simpa [prefixWord, tailWord_1140055, baseEnd_1140055] using wordTrace_append hprefix tailTrace_1140055
  have hstable : (prefixWord ++ tailWord_1140055).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1140055).length < 2 ^ (prefixWord ++ tailWord_1140055).sum := by decide
  have hdescent : baseEnd_1140055 < baseStart_1140055 := by decide
  rcases family_descends (prefixWord ++ tailWord_1140055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1140085 : List Nat := [1, 3, 4, 1, 3, 1, 1, 1, 7]
def baseStart_1140085 : Nat := 118140960795 + 1140085 * 2 ^ 59
def prefixEnd_1140085 : Nat := 4983230072969 + 3 ^ 40 * 1140085 * 2
def baseEnd_1140085 : Nat := 130091464884728254643189

theorem tailTrace_1140085 : CollatzResearch.WordTrace tailWord_1140085 prefixEnd_1140085 130091464884728254643189 := by
  unfold tailWord_1140085
  simp only [CollatzResearch.WordTrace]
  refine ⟨41582316074674230861373709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27721544049782820574249139 41582316074674230861373709)
  ·
    refine ⟨15593368528002836573015141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41582316074674230861373709 15593368528002836573015141)
    ·
      refine ⟨2923756599000531857440339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15593368528002836573015141 2923756599000531857440339)
      ·
        refine ⟨4385634898500797786160509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2923756599000531857440339 4385634898500797786160509)
        ·
          refine ⟨1644613086937799169810191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4385634898500797786160509 1644613086937799169810191)
          ·
            refine ⟨2466919630406698754715287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1644613086937799169810191 2466919630406698754715287)
            ·
              refine ⟨3700379445610048132072931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2466919630406698754715287 3700379445610048132072931)
              ·
                refine ⟨5550569168415072198109397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3700379445610048132072931 5550569168415072198109397)
                ·
                  refine ⟨130091464884728254643189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5550569168415072198109397 130091464884728254643189)
                  ·
                    rfl

theorem cell22_1140085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 1, 1, 7].length) (baseStart_1140085 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1140085 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1140085 prefixEnd_1140085 := by exact prefixLift 1140085
  have htrace : WordTrace (prefixWord ++ tailWord_1140085) baseStart_1140085 baseEnd_1140085 := by
    simpa [prefixWord, tailWord_1140085, baseEnd_1140085] using wordTrace_append hprefix tailTrace_1140085
  have hstable : (prefixWord ++ tailWord_1140085).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1140085).length < 2 ^ (prefixWord ++ tailWord_1140085).sum := by decide
  have hdescent : baseEnd_1140085 < baseStart_1140085 := by decide
  rcases family_descends (prefixWord ++ tailWord_1140085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1140128 : List Nat := [2, 1, 1, 4, 1, 2, 2, 1, 3, 5]
def baseStart_1140128 : Nat := 118140960795 + 1140128 * 2 ^ 59
def prefixEnd_1140128 : Nat := 4983230072969 + 3 ^ 40 * 1140128 * 2
def baseEnd_1140128 : Nat := 390289114432946985104435

theorem tailTrace_1140128 : CollatzResearch.WordTrace tailWord_1140128 prefixEnd_1140128 390289114432946985104435 := by
  unfold tailWord_1140128
  simp only [CollatzResearch.WordTrace]
  refine ⟨20791942206759224602594519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27722589609012299470126025 20791942206759224602594519)
  ·
    refine ⟨31187913310138836903891779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20791942206759224602594519 31187913310138836903891779)
    ·
      refine ⟨46781869965208255355837669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31187913310138836903891779 46781869965208255355837669)
      ·
        refine ⟨8771600618476547879219563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 46781869965208255355837669 8771600618476547879219563)
        ·
          refine ⟨13157400927714821818829345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8771600618476547879219563 13157400927714821818829345)
          ·
            refine ⟨9868050695786116364122009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13157400927714821818829345 9868050695786116364122009)
            ·
              refine ⟨7401038021839587273091507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9868050695786116364122009 7401038021839587273091507)
              ·
                refine ⟨11101557032759380909637261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7401038021839587273091507 11101557032759380909637261)
                ·
                  refine ⟨4163083887284767841113973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11101557032759380909637261 4163083887284767841113973)
                  ·
                    refine ⟨390289114432946985104435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4163083887284767841113973 390289114432946985104435)
                    ·
                      rfl

theorem cell22_1140128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 2, 1, 3, 5].length) (baseStart_1140128 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1140128 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1140128 prefixEnd_1140128 := by exact prefixLift 1140128
  have htrace : WordTrace (prefixWord ++ tailWord_1140128) baseStart_1140128 baseEnd_1140128 := by
    simpa [prefixWord, tailWord_1140128, baseEnd_1140128] using wordTrace_append hprefix tailTrace_1140128
  have hstable : (prefixWord ++ tailWord_1140128).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1140128).length < 2 ^ (prefixWord ++ tailWord_1140128).sum := by decide
  have hdescent : baseEnd_1140128 < baseStart_1140128 := by decide
  rcases family_descends (prefixWord ++ tailWord_1140128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1140145 : List Nat := [1, 2, 2, 4, 1, 1, 1, 3, 4, 3]
def baseStart_1140145 : Nat := 118140960795 + 1140145 * 2 ^ 59
def prefixEnd_1140145 : Nat := 4983230072969 + 3 ^ 40 * 1140145 * 2
def baseEnd_1140145 : Nat := 390294933880364607429383

theorem tailTrace_1140145 : CollatzResearch.WordTrace tailWord_1140145 prefixEnd_1140145 390294933880364607429383 := by
  unfold tailWord_1140145
  simp only [CollatzResearch.WordTrace]
  refine ⟨41584504454456861108557889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27723002969637907405705259 41584504454456861108557889)
  ·
    refine ⟨31188378340842645831418417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41584504454456861108557889 31188378340842645831418417)
    ·
      refine ⟨23391283755631984373563813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31188378340842645831418417 23391283755631984373563813)
      ·
        refine ⟨4385865704180997070043215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23391283755631984373563813 4385865704180997070043215)
        ·
          refine ⟨6578798556271495605064823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4385865704180997070043215 6578798556271495605064823)
          ·
            refine ⟨9868197834407243407597235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6578798556271495605064823 9868197834407243407597235)
            ·
              refine ⟨14802296751610865111395853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9868197834407243407597235 14802296751610865111395853)
              ·
                refine ⟨5550861281854074416773445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14802296751610865111395853 5550861281854074416773445)
                ·
                  refine ⟨1040786490347638953145021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5550861281854074416773445 1040786490347638953145021)
                  ·
                    refine ⟨390294933880364607429383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1040786490347638953145021 390294933880364607429383)
                    ·
                      rfl

theorem cell22_1140145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 3, 4, 3].length) (baseStart_1140145 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1140145 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1140145 prefixEnd_1140145 := by exact prefixLift 1140145
  have htrace : WordTrace (prefixWord ++ tailWord_1140145) baseStart_1140145 baseEnd_1140145 := by
    simpa [prefixWord, tailWord_1140145, baseEnd_1140145] using wordTrace_append hprefix tailTrace_1140145
  have hstable : (prefixWord ++ tailWord_1140145).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1140145).length < 2 ^ (prefixWord ++ tailWord_1140145).sum := by decide
  have hdescent : baseEnd_1140145 < baseStart_1140145 := by decide
  rcases family_descends (prefixWord ++ tailWord_1140145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1140220 : List Nat := [2, 2, 2, 1, 2, 1, 4, 3, 5]
def baseStart_1140220 : Nat := 118140960795 + 1140220 * 2 ^ 59
def prefixEnd_1140220 : Nat := 4983230072969 + 3 ^ 40 * 1140220 * 2
def baseEnd_1140220 : Nat := 130106869304363137268051

theorem tailTrace_1140220 : CollatzResearch.WordTrace tailWord_1140220 prefixEnd_1140220 130106869304363137268051 := by
  unfold tailWord_1140220
  simp only [CollatzResearch.WordTrace]
  refine ⟨20793619964592574458769057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27724826619456765945025409 20793619964592574458769057)
  ·
    refine ⟨15595214973444430844076793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20793619964592574458769057 15595214973444430844076793)
    ·
      refine ⟨11696411230083323133057595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15595214973444430844076793 11696411230083323133057595)
      ·
        refine ⟨17544616845124984699586393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11696411230083323133057595 17544616845124984699586393)
        ·
          refine ⟨13158462633843738524689795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17544616845124984699586393 13158462633843738524689795)
          ·
            refine ⟨19737693950765607787034693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13158462633843738524689795 19737693950765607787034693)
            ·
              refine ⟨3700817615768551460069005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19737693950765607787034693 3700817615768551460069005)
              ·
                refine ⟨1387806605913206797525877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3700817615768551460069005 1387806605913206797525877)
                ·
                  refine ⟨130106869304363137268051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1387806605913206797525877 130106869304363137268051)
                  ·
                    rfl

theorem cell22_1140220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 4, 3, 5].length) (baseStart_1140220 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1140220 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1140220 prefixEnd_1140220 := by exact prefixLift 1140220
  have htrace : WordTrace (prefixWord ++ tailWord_1140220) baseStart_1140220 baseEnd_1140220 := by
    simpa [prefixWord, tailWord_1140220, baseEnd_1140220] using wordTrace_append hprefix tailTrace_1140220
  have hstable : (prefixWord ++ tailWord_1140220).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1140220).length < 2 ^ (prefixWord ++ tailWord_1140220).sum := by decide
  have hdescent : baseEnd_1140220 < baseStart_1140220 := by decide
  rcases family_descends (prefixWord ++ tailWord_1140220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1140284 : List Nat := [2, 2, 2, 2, 4, 1, 2, 2, 1, 4]
def baseStart_1140284 : Nat := 118140960795 + 1140284 * 2 ^ 59
def prefixEnd_1140284 : Nat := 4983230072969 + 3 ^ 40 * 1140284 * 2
def baseEnd_1140284 : Nat := 390342516421014578203957

theorem tailTrace_1140284 : CollatzResearch.WordTrace tailWord_1140284 prefixEnd_1140284 390342516421014578203957 := by
  unfold tailWord_1140284
  simp only [CollatzResearch.WordTrace]
  refine ⟨20794787100476643923933953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27726382800635525231911937 20794787100476643923933953)
  ·
    refine ⟨15596090325357482942950465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20794787100476643923933953 15596090325357482942950465)
    ·
      refine ⟨11697067744018112207212849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15596090325357482942950465 11697067744018112207212849)
      ·
        refine ⟨8772800808013584155409637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11697067744018112207212849 8772800808013584155409637)
        ·
          refine ⟨1644900151502547029139307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8772800808013584155409637 1644900151502547029139307)
          ·
            refine ⟨2467350227253820543708961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1644900151502547029139307 2467350227253820543708961)
            ·
              refine ⟨1850512670440365407781721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2467350227253820543708961 1850512670440365407781721)
              ·
                refine ⟨1387884502830274055836291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1850512670440365407781721 1387884502830274055836291)
                ·
                  refine ⟨2081826754245411083754437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1387884502830274055836291 2081826754245411083754437)
                  ·
                    refine ⟨390342516421014578203957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2081826754245411083754437 390342516421014578203957)
                    ·
                      rfl

theorem cell22_1140284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 2, 2, 1, 4].length) (baseStart_1140284 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1140284 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1140284 prefixEnd_1140284 := by exact prefixLift 1140284
  have htrace : WordTrace (prefixWord ++ tailWord_1140284) baseStart_1140284 baseEnd_1140284 := by
    simpa [prefixWord, tailWord_1140284, baseEnd_1140284] using wordTrace_append hprefix tailTrace_1140284
  have hstable : (prefixWord ++ tailWord_1140284).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1140284).length < 2 ^ (prefixWord ++ tailWord_1140284).sum := by decide
  have hdescent : baseEnd_1140284 < baseStart_1140284 := by decide
  rcases family_descends (prefixWord ++ tailWord_1140284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1140316 : List Nat := [2, 2, 4, 1, 2, 2, 3, 2, 4]
def baseStart_1140316 : Nat := 118140960795 + 1140316 * 2 ^ 59
def prefixEnd_1140316 : Nat := 4983230072969 + 3 ^ 40 * 1140316 * 2
def baseEnd_1140316 : Nat := 130117823558325720467953

theorem tailTrace_1140316 : CollatzResearch.WordTrace tailWord_1140316 prefixEnd_1140316 130117823558325720467953 := by
  unfold tailWord_1140316
  simp only [CollatzResearch.WordTrace]
  refine ⟨20795370668418678656516401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27727160891224904875355201 20795370668418678656516401)
  ·
    refine ⟨15596528001314008992387301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20795370668418678656516401 15596528001314008992387301)
    ·
      refine ⟨2924349000246376686072619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15596528001314008992387301 2924349000246376686072619)
      ·
        refine ⟨4386523500369565029108929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2924349000246376686072619 4386523500369565029108929)
        ·
          refine ⟨3289892625277173771831697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4386523500369565029108929 3289892625277173771831697)
          ·
            refine ⟨2467419468957880328873773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3289892625277173771831697 2467419468957880328873773)
            ·
              refine ⟨925282300859205123327665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2467419468957880328873773 925282300859205123327665)
              ·
                refine ⟨693961725644403842495749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 925282300859205123327665 693961725644403842495749)
                ·
                  refine ⟨130117823558325720467953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 693961725644403842495749 130117823558325720467953)
                  ·
                    rfl

theorem cell22_1140316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 3, 2, 4].length) (baseStart_1140316 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1140316 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1140316 prefixEnd_1140316 := by exact prefixLift 1140316
  have htrace : WordTrace (prefixWord ++ tailWord_1140316) baseStart_1140316 baseEnd_1140316 := by
    simpa [prefixWord, tailWord_1140316, baseEnd_1140316] using wordTrace_append hprefix tailTrace_1140316
  have hstable : (prefixWord ++ tailWord_1140316).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1140316).length < 2 ^ (prefixWord ++ tailWord_1140316).sum := by decide
  have hdescent : baseEnd_1140316 < baseStart_1140316 := by decide
  rcases family_descends (prefixWord ++ tailWord_1140316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1140376 : List Nat := [2, 1, 2, 4, 1, 3, 1, 4, 1, 3]
def baseStart_1140376 : Nat := 118140960795 + 1140376 * 2 ^ 59
def prefixEnd_1140376 : Nat := 4983230072969 + 3 ^ 40 * 1140376 * 2
def baseEnd_1140376 : Nat := 390374009901157004903675

theorem tailTrace_1140376 : CollatzResearch.WordTrace tailWord_1140376 prefixEnd_1140376 390374009901157004903675 := by
  unfold tailWord_1140376
  simp only [CollatzResearch.WordTrace]
  refine ⟨20796464858309993780108491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27728619811079991706811321 20796464858309993780108491)
  ·
    refine ⟨31194697287464990670162737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20796464858309993780108491 31194697287464990670162737)
    ·
      refine ⟨23396022965598743002622053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31194697287464990670162737 23396022965598743002622053)
      ·
        refine ⟨4386754306049764312991635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23396022965598743002622053 4386754306049764312991635)
        ·
          refine ⟨6580131459074646469487453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4386754306049764312991635 6580131459074646469487453)
          ·
            refine ⟨2467549297152992426057795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6580131459074646469487453 2467549297152992426057795)
            ·
              refine ⟨3701323945729488639086693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2467549297152992426057795 3701323945729488639086693)
              ·
                refine ⟨693998239824279119828755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3701323945729488639086693 693998239824279119828755)
                ·
                  refine ⟨1040997359736418679743133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 693998239824279119828755 1040997359736418679743133)
                  ·
                    refine ⟨390374009901157004903675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1040997359736418679743133 390374009901157004903675)
                    ·
                      rfl

theorem cell22_1140376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 1, 4, 1, 3].length) (baseStart_1140376 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1140376 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1140376 prefixEnd_1140376 := by exact prefixLift 1140376
  have htrace : WordTrace (prefixWord ++ tailWord_1140376) baseStart_1140376 baseEnd_1140376 := by
    simpa [prefixWord, tailWord_1140376, baseEnd_1140376] using wordTrace_append hprefix tailTrace_1140376
  have hstable : (prefixWord ++ tailWord_1140376).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1140376).length < 2 ^ (prefixWord ++ tailWord_1140376).sum := by decide
  have hdescent : baseEnd_1140376 < baseStart_1140376 := by decide
  rcases family_descends (prefixWord ++ tailWord_1140376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1140400 : List Nat := [2, 1, 1, 1, 2, 1, 5, 1, 8]
def baseStart_1140400 : Nat := 118140960795 + 1140400 * 2 ^ 59
def prefixEnd_1140400 : Nat := 4983230072969 + 3 ^ 40 * 1140400 * 2
def baseEnd_1140400 : Nat := 130127408530542980767867

theorem tailTrace_1140400 : CollatzResearch.WordTrace tailWord_1140400 prefixEnd_1140400 130127408530542980767867 := by
  unfold tailWord_1140400
  simp only [CollatzResearch.WordTrace]
  refine ⟨20796902534266519829545327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27729203379022026439393769 20796902534266519829545327)
  ·
    refine ⟨31195353801399779744317991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20796902534266519829545327 31195353801399779744317991)
    ·
      refine ⟨46793030702099669616476987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31195353801399779744317991 46793030702099669616476987)
      ·
        refine ⟨70189546053149504424715481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46793030702099669616476987 70189546053149504424715481)
        ·
          refine ⟨52642159539862128318536611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70189546053149504424715481 52642159539862128318536611)
          ·
            refine ⟨78963239309793192477804917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52642159539862128318536611 78963239309793192477804917)
            ·
              refine ⟨7402803685293111794794211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 78963239309793192477804917 7402803685293111794794211)
              ·
                refine ⟨11104205527939667692191317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7402803685293111794794211 11104205527939667692191317)
                ·
                  refine ⟨130127408530542980767867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 11104205527939667692191317 130127408530542980767867)
                  ·
                    rfl

theorem cell22_1140400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 5, 1, 8].length) (baseStart_1140400 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1140400 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1140400 prefixEnd_1140400 := by exact prefixLift 1140400
  have htrace : WordTrace (prefixWord ++ tailWord_1140400) baseStart_1140400 baseEnd_1140400 := by
    simpa [prefixWord, tailWord_1140400, baseEnd_1140400] using wordTrace_append hprefix tailTrace_1140400
  have hstable : (prefixWord ++ tailWord_1140400).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1140400).length < 2 ^ (prefixWord ++ tailWord_1140400).sum := by decide
  have hdescent : baseEnd_1140400 < baseStart_1140400 := by decide
  rcases family_descends (prefixWord ++ tailWord_1140400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1140402 : List Nat := [3, 2, 1, 1, 1, 2, 4, 1, 3, 4]
def baseStart_1140402 : Nat := 118140960795 + 1140402 * 2 ^ 59
def prefixEnd_1140402 : Nat := 4983230072969 + 3 ^ 40 * 1140402 * 2
def baseEnd_1140402 : Nat := 390382910232501603753595

theorem tailTrace_1140402 : CollatzResearch.WordTrace tailWord_1140402 prefixEnd_1140402 390382910232501603753595 := by
  unfold tailWord_1140402
  simp only [CollatzResearch.WordTrace]
  refine ⟨10398469503631448500165865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27729252009683862667108973 10398469503631448500165865)
  ·
    refine ⟨7798852127723586375124399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10398469503631448500165865 7798852127723586375124399)
    ·
      refine ⟨11698278191585379562686599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7798852127723586375124399 11698278191585379562686599)
      ·
        refine ⟨17547417287378069344029899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11698278191585379562686599 17547417287378069344029899)
        ·
          refine ⟨26321125931067104016044849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17547417287378069344029899 26321125931067104016044849)
          ·
            refine ⟨19740844448300328012033637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26321125931067104016044849 19740844448300328012033637)
            ·
              refine ⟨3701408334056311502256307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19740844448300328012033637 3701408334056311502256307)
              ·
                refine ⟨5552112501084467253384461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3701408334056311502256307 5552112501084467253384461)
                ·
                  refine ⟨2082042187906675220019173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5552112501084467253384461 2082042187906675220019173)
                  ·
                    refine ⟨390382910232501603753595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2082042187906675220019173 390382910232501603753595)
                    ·
                      rfl

theorem cell22_1140402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 4, 1, 3, 4].length) (baseStart_1140402 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1140402 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1140402 prefixEnd_1140402 := by exact prefixLift 1140402
  have htrace : WordTrace (prefixWord ++ tailWord_1140402) baseStart_1140402 baseEnd_1140402 := by
    simpa [prefixWord, tailWord_1140402, baseEnd_1140402] using wordTrace_append hprefix tailTrace_1140402
  have hstable : (prefixWord ++ tailWord_1140402).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1140402).length < 2 ^ (prefixWord ++ tailWord_1140402).sum := by decide
  have hdescent : baseEnd_1140402 < baseStart_1140402 := by decide
  rcases family_descends (prefixWord ++ tailWord_1140402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1140434 : List Nat := [3, 2, 2, 2, 2, 2, 2, 1, 6]
def baseStart_1140434 : Nat := 118140960795 + 1140434 * 2 ^ 59
def prefixEnd_1140434 : Nat := 4983230072969 + 3 ^ 40 * 1140434 * 2
def baseEnd_1140434 : Nat := 130131288162154728984499

theorem tailTrace_1140434 : CollatzResearch.WordTrace tailWord_1140434 prefixEnd_1140434 130131288162154728984499 := by
  unfold tailWord_1140434
  simp only [CollatzResearch.WordTrace]
  refine ⟨10398761287602465866457089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27730030100273242310552237 10398761287602465866457089)
  ·
    refine ⟨7799070965701849399842817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10398761287602465866457089 7799070965701849399842817)
    ·
      refine ⟨5849303224276387049882113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7799070965701849399842817 5849303224276387049882113)
      ·
        refine ⟨4386977418207290287411585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5849303224276387049882113 4386977418207290287411585)
        ·
          refine ⟨3290233063655467715558689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4386977418207290287411585 3290233063655467715558689)
          ·
            refine ⟨2467674797741600786669017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3290233063655467715558689 2467674797741600786669017)
            ·
              refine ⟨1850756098306200590001763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2467674797741600786669017 1850756098306200590001763)
              ·
                refine ⟨2776134147459300885002645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1850756098306200590001763 2776134147459300885002645)
                ·
                  refine ⟨130131288162154728984499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2776134147459300885002645 130131288162154728984499)
                  ·
                    rfl

theorem cell22_1140434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 2, 1, 6].length) (baseStart_1140434 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1140434 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1140434 prefixEnd_1140434 := by exact prefixLift 1140434
  have htrace : WordTrace (prefixWord ++ tailWord_1140434) baseStart_1140434 baseEnd_1140434 := by
    simpa [prefixWord, tailWord_1140434, baseEnd_1140434] using wordTrace_append hprefix tailTrace_1140434
  have hstable : (prefixWord ++ tailWord_1140434).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1140434).length < 2 ^ (prefixWord ++ tailWord_1140434).sum := by decide
  have hdescent : baseEnd_1140434 < baseStart_1140434 := by decide
  rcases family_descends (prefixWord ++ tailWord_1140434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1140462 : List Nat := [4, 1, 2, 1, 1, 2, 3, 8]
def baseStart_1140462 : Nat := 118140960795 + 1140462 * 2 ^ 59
def prefixEnd_1140462 : Nat := 4983230072969 + 3 ^ 40 * 1140462 * 2
def baseEnd_1140462 : Nat := 43378161050964605250379

theorem tailTrace_1140462 : CollatzResearch.WordTrace tailWord_1140462 prefixEnd_1140462 43378161050964605250379 := by
  unfold tailWord_1140462
  simp only [CollatzResearch.WordTrace]
  refine ⟨5199508299288553030980955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27730710929538949498565093 5199508299288553030980955)
  ·
    refine ⟨7799262448932829546471433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5199508299288553030980955 7799262448932829546471433)
    ·
      refine ⟨5849446836699622159853575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7799262448932829546471433 5849446836699622159853575)
      ·
        refine ⟨8774170255049433239780363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5849446836699622159853575 8774170255049433239780363)
        ·
          refine ⟨13161255382574149859670545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8774170255049433239780363 13161255382574149859670545)
          ·
            refine ⟨9870941536930612394752909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13161255382574149859670545 9870941536930612394752909)
            ·
              refine ⟨3701603076348979648032341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9870941536930612394752909 3701603076348979648032341)
              ·
                refine ⟨43378161050964605250379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3701603076348979648032341 43378161050964605250379)
                ·
                  rfl

theorem cell22_1140462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 3, 8].length) (baseStart_1140462 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1140462 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1140462 prefixEnd_1140462 := by exact prefixLift 1140462
  have htrace : WordTrace (prefixWord ++ tailWord_1140462) baseStart_1140462 baseEnd_1140462 := by
    simpa [prefixWord, tailWord_1140462, baseEnd_1140462] using wordTrace_append hprefix tailTrace_1140462
  have hstable : (prefixWord ++ tailWord_1140462).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1140462).length < 2 ^ (prefixWord ++ tailWord_1140462).sum := by decide
  have hdescent : baseEnd_1140462 < baseStart_1140462 := by decide
  rcases family_descends (prefixWord ++ tailWord_1140462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1140507 : List Nat := [1, 1, 1, 1, 1, 1, 4, 7, 5]
def baseStart_1140507 : Nat := 118140960795 + 1140507 * 2 ^ 59
def prefixEnd_1140507 : Nat := 4983230072969 + 3 ^ 40 * 1140507 * 2
def baseEnd_1140507 : Nat := 130139617959438776626091

theorem tailTrace_1140507 : CollatzResearch.WordTrace tailWord_1140507 prefixEnd_1140507 130139617959438776626091 := by
  unfold tailWord_1140507
  simp only [CollatzResearch.WordTrace]
  refine ⟨41597707679145396933235775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27731805119430264622157183 41597707679145396933235775)
  ·
    refine ⟨62396561518718095399853663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41597707679145396933235775 62396561518718095399853663)
    ·
      refine ⟨93594842278077143099780495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62396561518718095399853663 93594842278077143099780495)
      ·
        refine ⟨140392263417115714649670743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93594842278077143099780495 140392263417115714649670743)
        ·
          refine ⟨210588395125673571974506115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 140392263417115714649670743 210588395125673571974506115)
          ·
            refine ⟨315882592688510357961759173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 210588395125673571974506115 315882592688510357961759173)
            ·
              refine ⟨59227986129095692117829845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 315882592688510357961759173 59227986129095692117829845)
              ·
                refine ⟨1388155924900680284011637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 59227986129095692117829845 1388155924900680284011637)
                ·
                  refine ⟨130139617959438776626091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1388155924900680284011637 130139617959438776626091)
                  ·
                    rfl

theorem cell22_1140507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 7, 5].length) (baseStart_1140507 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1140507 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1140507 prefixEnd_1140507 := by exact prefixLift 1140507
  have htrace : WordTrace (prefixWord ++ tailWord_1140507) baseStart_1140507 baseEnd_1140507 := by
    simpa [prefixWord, tailWord_1140507, baseEnd_1140507] using wordTrace_append hprefix tailTrace_1140507
  have hstable : (prefixWord ++ tailWord_1140507).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1140507).length < 2 ^ (prefixWord ++ tailWord_1140507).sum := by decide
  have hdescent : baseEnd_1140507 < baseStart_1140507 := by decide
  rcases family_descends (prefixWord ++ tailWord_1140507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1140541 : List Nat := [1, 4, 1, 4, 1, 2, 2, 2, 5]
def baseStart_1140541 : Nat := 118140960795 + 1140541 * 2 ^ 59
def prefixEnd_1140541 : Nat := 4983230072969 + 3 ^ 40 * 1140541 * 2
def baseEnd_1140541 : Nat := 130143497591050524842723

theorem tailTrace_1140541 : CollatzResearch.WordTrace tailWord_1140541 prefixEnd_1140541 130143497591050524842723 := by
  unfold tailWord_1140541
  simp only [CollatzResearch.WordTrace]
  refine ⟨41598947761022220739973477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27732631840681480493315651 41598947761022220739973477)
  ·
    refine ⟨7799802705191666388745027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 41598947761022220739973477 7799802705191666388745027)
    ·
      refine ⟨11699704057787499583117541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7799802705191666388745027 11699704057787499583117541)
      ·
        refine ⟨2193694510835156171834539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11699704057787499583117541 2193694510835156171834539)
        ·
          refine ⟨3290541766252734257751809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2193694510835156171834539 3290541766252734257751809)
          ·
            refine ⟨2467906324689550693313857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3290541766252734257751809 2467906324689550693313857)
            ·
              refine ⟨1850929743517163019985393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2467906324689550693313857 1850929743517163019985393)
              ·
                refine ⟨1388197307637872264989045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1850929743517163019985393 1388197307637872264989045)
                ·
                  refine ⟨130143497591050524842723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1388197307637872264989045 130143497591050524842723)
                  ·
                    rfl

theorem cell22_1140541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 2, 2, 5].length) (baseStart_1140541 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1140541 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1140541 prefixEnd_1140541 := by exact prefixLift 1140541
  have htrace : WordTrace (prefixWord ++ tailWord_1140541) baseStart_1140541 baseEnd_1140541 := by
    simpa [prefixWord, tailWord_1140541, baseEnd_1140541] using wordTrace_append hprefix tailTrace_1140541
  have hstable : (prefixWord ++ tailWord_1140541).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1140541).length < 2 ^ (prefixWord ++ tailWord_1140541).sum := by decide
  have hdescent : baseEnd_1140541 < baseStart_1140541 := by decide
  rcases family_descends (prefixWord ++ tailWord_1140541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1140584 : List Nat := [2, 1, 4, 2, 1, 1, 1, 4, 1, 5]
def baseStart_1140584 : Nat := 118140960795 + 1140584 * 2 ^ 59
def prefixEnd_1140584 : Nat := 4983230072969 + 3 ^ 40 * 1140584 * 2
def baseEnd_1140584 : Nat := 390445212551913795703037

theorem tailTrace_1140584 : CollatzResearch.WordTrace tailWord_1140584 prefixEnd_1140584 390445212551913795703037 := by
  unfold tailWord_1140584
  simp only [CollatzResearch.WordTrace]
  refine ⟨20800258049933219541894403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27733677399910959389192537 20800258049933219541894403)
  ·
    refine ⟨31200387074899829312841605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20800258049933219541894403 31200387074899829312841605)
    ·
      refine ⟨5850072576543717996157801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31200387074899829312841605 5850072576543717996157801)
      ·
        refine ⟨4387554432407788497118351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5850072576543717996157801 4387554432407788497118351)
        ·
          refine ⟨6581331648611682745677527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4387554432407788497118351 6581331648611682745677527)
          ·
            refine ⟨9871997472917524118516291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6581331648611682745677527 9871997472917524118516291)
            ·
              refine ⟨14807996209376286177774437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9871997472917524118516291 14807996209376286177774437)
              ·
                refine ⟨2776499289258053658332707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14807996209376286177774437 2776499289258053658332707)
                ·
                  refine ⟨4164748933887080487499061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2776499289258053658332707 4164748933887080487499061)
                  ·
                    refine ⟨390445212551913795703037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4164748933887080487499061 390445212551913795703037)
                    ·
                      rfl

theorem cell22_1140584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 4, 1, 5].length) (baseStart_1140584 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1140584 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1140584 prefixEnd_1140584 := by exact prefixLift 1140584
  have htrace : WordTrace (prefixWord ++ tailWord_1140584) baseStart_1140584 baseEnd_1140584 := by
    simpa [prefixWord, tailWord_1140584, baseEnd_1140584] using wordTrace_append hprefix tailTrace_1140584
  have hstable : (prefixWord ++ tailWord_1140584).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1140584).length < 2 ^ (prefixWord ++ tailWord_1140584).sum := by decide
  have hdescent : baseEnd_1140584 < baseStart_1140584 := by decide
  rcases family_descends (prefixWord ++ tailWord_1140584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1140588 : List Nat := [2, 2, 1, 1, 4, 4, 2, 1, 1, 4]
def baseStart_1140588 : Nat := 118140960795 + 1140588 * 2 ^ 59
def prefixEnd_1140588 : Nat := 4983230072969 + 3 ^ 40 * 1140588 * 2
def baseEnd_1140588 : Nat := 390446581833659118603025

theorem tailTrace_1140588 : CollatzResearch.WordTrace tailWord_1140588 prefixEnd_1140588 390446581833659118603025 := by
  unfold tailWord_1140588
  simp only [CollatzResearch.WordTrace]
  refine ⟨20800330995925973883467209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27733774661234631844622945 20800330995925973883467209)
  ·
    refine ⟨15600248246944480412600407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20800330995925973883467209 15600248246944480412600407)
    ·
      refine ⟨23400372370416720618900611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15600248246944480412600407 23400372370416720618900611)
      ·
        refine ⟨35100558555625080928350917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23400372370416720618900611 35100558555625080928350917)
        ·
          refine ⟨6581354729179702674065797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 35100558555625080928350917 6581354729179702674065797)
          ·
            refine ⟨1234004011721194251387337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6581354729179702674065797 1234004011721194251387337)
            ·
              refine ⟨925503008790895688540503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1234004011721194251387337 925503008790895688540503)
              ·
                refine ⟨1388254513186343532810755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 925503008790895688540503 1388254513186343532810755)
                ·
                  refine ⟨2082381769779515299216133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1388254513186343532810755 2082381769779515299216133)
                  ·
                    refine ⟨390446581833659118603025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2082381769779515299216133 390446581833659118603025)
                    ·
                      rfl

theorem cell22_1140588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 4].length) (baseStart_1140588 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1140588 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1140588 prefixEnd_1140588 := by exact prefixLift 1140588
  have htrace : WordTrace (prefixWord ++ tailWord_1140588) baseStart_1140588 baseEnd_1140588 := by
    simpa [prefixWord, tailWord_1140588, baseEnd_1140588] using wordTrace_append hprefix tailTrace_1140588
  have hstable : (prefixWord ++ tailWord_1140588).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1140588).length < 2 ^ (prefixWord ++ tailWord_1140588).sum := by decide
  have hdescent : baseEnd_1140588 < baseStart_1140588 := by decide
  rcases family_descends (prefixWord ++ tailWord_1140588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1140618 : List Nat := [3, 1, 2, 4, 2, 2, 1, 1, 1, 5]
def baseStart_1140618 : Nat := 118140960795 + 1140618 * 2 ^ 59
def prefixEnd_1140618 : Nat := 4983230072969 + 3 ^ 40 * 1140618 * 2
def baseEnd_1140618 : Nat := 390456851446749040352933

theorem tailTrace_1140618 : CollatzResearch.WordTrace tailWord_1140618 prefixEnd_1140618 390456851446749040352933 := by
  unfold tailWord_1140618
  simp only [CollatzResearch.WordTrace]
  refine ⟨10400439045435815722631627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27734504121162175260351005 10400439045435815722631627)
  ·
    refine ⟨15600658568153723583947441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10400439045435815722631627 15600658568153723583947441)
    ·
      refine ⟨11700493926115292687960581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15600658568153723583947441 11700493926115292687960581)
      ·
        refine ⟨2193842611146617378992609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11700493926115292687960581 2193842611146617378992609)
        ·
          refine ⟨1645381958359963034244457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2193842611146617378992609 1645381958359963034244457)
          ·
            refine ⟨1234036468769972275683343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1645381958359963034244457 1234036468769972275683343)
            ·
              refine ⟨1851054703154958413525015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1234036468769972275683343 1851054703154958413525015)
              ·
                refine ⟨2776582054732437620287523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1851054703154958413525015 2776582054732437620287523)
                ·
                  refine ⟨4164873082098656430431285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2776582054732437620287523 4164873082098656430431285)
                  ·
                    refine ⟨390456851446749040352933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4164873082098656430431285 390456851446749040352933)
                    ·
                      rfl

theorem cell22_1140618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 2, 1, 1, 1, 5].length) (baseStart_1140618 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1140618 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1140618 prefixEnd_1140618 := by exact prefixLift 1140618
  have htrace : WordTrace (prefixWord ++ tailWord_1140618) baseStart_1140618 baseEnd_1140618 := by
    simpa [prefixWord, tailWord_1140618, baseEnd_1140618] using wordTrace_append hprefix tailTrace_1140618
  have hstable : (prefixWord ++ tailWord_1140618).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1140618).length < 2 ^ (prefixWord ++ tailWord_1140618).sum := by decide
  have hdescent : baseEnd_1140618 < baseStart_1140618 := by decide
  rcases family_descends (prefixWord ++ tailWord_1140618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1140627 : List Nat := [1, 1, 1, 2, 1, 2, 1, 2, 3, 8]
def baseStart_1140627 : Nat := 118140960795 + 1140627 * 2 ^ 59
def prefixEnd_1140627 : Nat := 4983230072969 + 3 ^ 40 * 1140627 * 2
def baseEnd_1140627 : Nat := 390459932330676016877905

theorem tailTrace_1140627 : CollatzResearch.WordTrace tailWord_1140627 prefixEnd_1140627 390459932330676016877905 := by
  unfold tailWord_1140627
  simp only [CollatzResearch.WordTrace]
  refine ⟨41602084438710657427604135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27734722959140438285069423 41602084438710657427604135)
  ·
    refine ⟨62403126658065986141406203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41602084438710657427604135 62403126658065986141406203)
    ·
      refine ⟨93604689987098979212109305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62403126658065986141406203 93604689987098979212109305)
      ·
        refine ⟨70203517490324234409081979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93604689987098979212109305 70203517490324234409081979)
        ·
          refine ⟨105305276235486351613622969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70203517490324234409081979 105305276235486351613622969)
          ·
            refine ⟨78978957176614763710217227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 105305276235486351613622969 78978957176614763710217227)
            ·
              refine ⟨118468435764922145565325841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78978957176614763710217227 118468435764922145565325841)
              ·
                refine ⟨88851326823691609173994381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 118468435764922145565325841 88851326823691609173994381)
                ·
                  refine ⟨33319247558884353440247893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 88851326823691609173994381 33319247558884353440247893)
                  ·
                    refine ⟨390459932330676016877905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 33319247558884353440247893 390459932330676016877905)
                    ·
                      rfl

theorem cell22_1140627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 2, 3, 8].length) (baseStart_1140627 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1140627 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1140627 prefixEnd_1140627 := by exact prefixLift 1140627
  have htrace : WordTrace (prefixWord ++ tailWord_1140627) baseStart_1140627 baseEnd_1140627 := by
    simpa [prefixWord, tailWord_1140627, baseEnd_1140627] using wordTrace_append hprefix tailTrace_1140627
  have hstable : (prefixWord ++ tailWord_1140627).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1140627).length < 2 ^ (prefixWord ++ tailWord_1140627).sum := by decide
  have hdescent : baseEnd_1140627 < baseStart_1140627 := by decide
  rcases family_descends (prefixWord ++ tailWord_1140627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1140631 : List Nat := [1, 1, 3, 3, 1, 5, 2, 6]
def baseStart_1140631 : Nat := 118140960795 + 1140631 * 2 ^ 59
def prefixEnd_1140631 : Nat := 4983230072969 + 3 ^ 40 * 1140631 * 2
def baseEnd_1140631 : Nat := 43384589068046815530877

theorem tailTrace_1140631 : CollatzResearch.WordTrace tailWord_1140631 prefixEnd_1140631 43384589068046815530877 := by
  unfold tailWord_1140631
  simp only [CollatzResearch.WordTrace]
  refine ⟨41602230330696166110749747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27734820220464110740499831 41602230330696166110749747)
  ·
    refine ⟨62403345496044249166124621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41602230330696166110749747 62403345496044249166124621)
    ·
      refine ⟨23401254561016593437296733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62403345496044249166124621 23401254561016593437296733)
      ·
        refine ⟨8775470460381222538986275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23401254561016593437296733 8775470460381222538986275)
        ·
          refine ⟨13163205690571833808479413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8775470460381222538986275 13163205690571833808479413)
          ·
            refine ⟨1234050533491109419544945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 13163205690571833808479413 1234050533491109419544945)
            ·
              refine ⟨925537900118332064658709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1234050533491109419544945 925537900118332064658709)
              ·
                refine ⟨43384589068046815530877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 925537900118332064658709 43384589068046815530877)
                ·
                  rfl

theorem cell22_1140631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 5, 2, 6].length) (baseStart_1140631 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1140631 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1140631 prefixEnd_1140631 := by exact prefixLift 1140631
  have htrace : WordTrace (prefixWord ++ tailWord_1140631) baseStart_1140631 baseEnd_1140631 := by
    simpa [prefixWord, tailWord_1140631, baseEnd_1140631] using wordTrace_append hprefix tailTrace_1140631
  have hstable : (prefixWord ++ tailWord_1140631).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1140631).length < 2 ^ (prefixWord ++ tailWord_1140631).sum := by decide
  have hdescent : baseEnd_1140631 < baseStart_1140631 := by decide
  rcases family_descends (prefixWord ++ tailWord_1140631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1140648 : List Nat := [2, 1, 6, 2, 1, 2, 8]
def baseStart_1140648 : Nat := 118140960795 + 1140648 * 2 ^ 59
def prefixEnd_1140648 : Nat := 4983230072969 + 3 ^ 40 * 1140648 * 2
def baseEnd_1140648 : Nat := 14461745224438480077883

theorem tailTrace_1140648 : CollatzResearch.WordTrace tailWord_1140648 prefixEnd_1140648 14461745224438480077883 := by
  unfold tailWord_1140648
  simp only [CollatzResearch.WordTrace]
  refine ⟨20801425185817289007059299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27735233581089718676079065 20801425185817289007059299)
  ·
    refine ⟨31202137778725933510588949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20801425185817289007059299 31202137778725933510588949)
    ·
      refine ⟨1462600208377778133308857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 31202137778725933510588949 1462600208377778133308857)
      ·
        refine ⟨1096950156283333599981643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1462600208377778133308857 1096950156283333599981643)
        ·
          refine ⟨1645425234425000399972465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1096950156283333599981643 1645425234425000399972465)
          ·
            refine ⟨1234068925818750299979349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1645425234425000399972465 1234068925818750299979349)
            ·
              refine ⟨14461745224438480077883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1234068925818750299979349 14461745224438480077883)
              ·
                rfl

theorem cell22_1140648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 2, 8].length) (baseStart_1140648 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1140648 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1140648 prefixEnd_1140648 := by exact prefixLift 1140648
  have htrace : WordTrace (prefixWord ++ tailWord_1140648) baseStart_1140648 baseEnd_1140648 := by
    simpa [prefixWord, tailWord_1140648, baseEnd_1140648] using wordTrace_append hprefix tailTrace_1140648
  have hstable : (prefixWord ++ tailWord_1140648).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1140648).length < 2 ^ (prefixWord ++ tailWord_1140648).sum := by decide
  have hdescent : baseEnd_1140648 < baseStart_1140648 := by decide
  rcases family_descends (prefixWord ++ tailWord_1140648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1140654 : List Nat := [4, 1, 5, 1, 1, 1, 3, 2, 4]
def baseStart_1140654 : Nat := 118140960795 + 1140654 * 2 ^ 59
def prefixEnd_1140654 : Nat := 4983230072969 + 3 ^ 40 * 1140654 * 2
def baseEnd_1140654 : Nat := 130156391660818982150941

theorem tailTrace_1140654 : CollatzResearch.WordTrace tailWord_1140654 prefixEnd_1140654 130156391660818982150941 := by
  unfold tailWord_1140654
  simp only [CollatzResearch.WordTrace]
  refine ⟨5200383651201605129854627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27735379473075227359224677 5200383651201605129854627)
  ·
    refine ⟨7800575476802407694781941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5200383651201605129854627 7800575476802407694781941)
    ·
      refine ⟨731303950950225721385807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 7800575476802407694781941 731303950950225721385807)
      ·
        refine ⟨1096955926425338582078711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 731303950950225721385807 1096955926425338582078711)
        ·
          refine ⟨1645433889638007873118067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1096955926425338582078711 1645433889638007873118067)
          ·
            refine ⟨2468150834457011809677101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1645433889638007873118067 2468150834457011809677101)
            ·
              refine ⟨925556562921379428628913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2468150834457011809677101 925556562921379428628913)
              ·
                refine ⟨694167422191034571471685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 925556562921379428628913 694167422191034571471685)
                ·
                  refine ⟨130156391660818982150941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 694167422191034571471685 130156391660818982150941)
                  ·
                    rfl

theorem cell22_1140654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 3, 2, 4].length) (baseStart_1140654 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1140654 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1140654 prefixEnd_1140654 := by exact prefixLift 1140654
  have htrace : WordTrace (prefixWord ++ tailWord_1140654) baseStart_1140654 baseEnd_1140654 := by
    simpa [prefixWord, tailWord_1140654, baseEnd_1140654] using wordTrace_append hprefix tailTrace_1140654
  have hstable : (prefixWord ++ tailWord_1140654).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1140654).length < 2 ^ (prefixWord ++ tailWord_1140654).sum := by decide
  have hdescent : baseEnd_1140654 < baseStart_1140654 := by decide
  rcases family_descends (prefixWord ++ tailWord_1140654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1140659 : List Nat := [1, 1, 1, 2, 3, 1, 4, 4, 5]
def baseStart_1140659 : Nat := 118140960795 + 1140659 * 2 ^ 59
def prefixEnd_1140659 : Nat := 4983230072969 + 3 ^ 40 * 1140659 * 2
def baseEnd_1140659 : Nat := 130156962194879533359269

theorem tailTrace_1140659 : CollatzResearch.WordTrace tailWord_1140659 prefixEnd_1140659 130156962194879533359269 := by
  unfold tailWord_1140659
  simp only [CollatzResearch.WordTrace]
  refine ⟨41603251574594726892769031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27735501049729817928512687 41603251574594726892769031)
  ·
    refine ⟨62404877361892090339153547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41603251574594726892769031 62404877361892090339153547)
    ·
      refine ⟨93607316042838135508730321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62404877361892090339153547 93607316042838135508730321)
      ·
        refine ⟨70205487032128601631547741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93607316042838135508730321 70205487032128601631547741)
        ·
          refine ⟨26327057637048225611830403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 70205487032128601631547741 26327057637048225611830403)
          ·
            refine ⟨39490586455572338417745605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26327057637048225611830403 39490586455572338417745605)
            ·
              refine ⟨7404484960419813453327301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 39490586455572338417745605 7404484960419813453327301)
              ·
                refine ⟨1388340930078715022498869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7404484960419813453327301 1388340930078715022498869)
                ·
                  refine ⟨130156962194879533359269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1388340930078715022498869 130156962194879533359269)
                  ·
                    rfl

theorem cell22_1140659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 4, 4, 5].length) (baseStart_1140659 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1140659 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1140659 prefixEnd_1140659 := by exact prefixLift 1140659
  have htrace : WordTrace (prefixWord ++ tailWord_1140659) baseStart_1140659 baseEnd_1140659 := by
    simpa [prefixWord, tailWord_1140659, baseEnd_1140659] using wordTrace_append hprefix tailTrace_1140659
  have hstable : (prefixWord ++ tailWord_1140659).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1140659).length < 2 ^ (prefixWord ++ tailWord_1140659).sum := by decide
  have hdescent : baseEnd_1140659 < baseStart_1140659 := by decide
  rcases family_descends (prefixWord ++ tailWord_1140659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1140719 : List Nat := [1, 1, 2, 1, 4, 2, 1, 2, 3, 5]
def baseStart_1140719 : Nat := 118140960795 + 1140719 * 2 ^ 59
def prefixEnd_1140719 : Nat := 4983230072969 + 3 ^ 40 * 1140719 * 2
def baseEnd_1140719 : Nat := 390491425810818443577623

theorem tailTrace_1140719 : CollatzResearch.WordTrace tailWord_1140719 prefixEnd_1140719 390491425810818443577623 := by
  unfold tailWord_1140719
  simp only [CollatzResearch.WordTrace]
  refine ⟨41605439954377357139953211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27736959969584904759968807 41605439954377357139953211)
  ·
    refine ⟨62408159931566035709929817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41605439954377357139953211 62408159931566035709929817)
    ·
      refine ⟨46806119948674526782447363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62408159931566035709929817 46806119948674526782447363)
      ·
        refine ⟨70209179923011790173671045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46806119948674526782447363 70209179923011790173671045)
        ·
          refine ⟨13164221235564710657563321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 70209179923011790173671045 13164221235564710657563321)
          ·
            refine ⟨9873165926673532993172491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13164221235564710657563321 9873165926673532993172491)
            ·
              refine ⟨14809748890010299489758737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9873165926673532993172491 14809748890010299489758737)
              ·
                refine ⟨11107311667507724617319053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14809748890010299489758737 11107311667507724617319053)
                ·
                  refine ⟨4165241875315396731494645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11107311667507724617319053 4165241875315396731494645)
                  ·
                    refine ⟨390491425810818443577623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4165241875315396731494645 390491425810818443577623)
                    ·
                      rfl

theorem cell22_1140719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 2, 3, 5].length) (baseStart_1140719 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1140719 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1140719 prefixEnd_1140719 := by exact prefixLift 1140719
  have htrace : WordTrace (prefixWord ++ tailWord_1140719) baseStart_1140719 baseEnd_1140719 := by
    simpa [prefixWord, tailWord_1140719, baseEnd_1140719] using wordTrace_append hprefix tailTrace_1140719
  have hstable : (prefixWord ++ tailWord_1140719).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1140719).length < 2 ^ (prefixWord ++ tailWord_1140719).sum := by decide
  have hdescent : baseEnd_1140719 < baseStart_1140719 := by decide
  rcases family_descends (prefixWord ++ tailWord_1140719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1140757 : List Nat := [1, 3, 2, 1, 6, 1, 2, 1, 1, 4]
def baseStart_1140757 : Nat := 118140960795 + 1140757 * 2 ^ 59
def prefixEnd_1140757 : Nat := 4983230072969 + 3 ^ 40 * 1140757 * 2
def baseEnd_1140757 : Nat := 390504433987399011127507

theorem tailTrace_1140757 : CollatzResearch.WordTrace tailWord_1140757 prefixEnd_1140757 390504433987399011127507 := by
  unfold tailWord_1140757
  simp only [CollatzResearch.WordTrace]
  refine ⟨41606825928239689629836525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27737883952159793086557683 41606825928239689629836525)
  ·
    refine ⟨15602559723089883611188697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41606825928239689629836525 15602559723089883611188697)
    ·
      refine ⟨11701919792317412708391523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15602559723089883611188697 11701919792317412708391523)
      ·
        refine ⟨17552879688476119062587285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11701919792317412708391523 17552879688476119062587285)
        ·
          refine ⟨822791235397318081058779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 17552879688476119062587285 822791235397318081058779)
          ·
            refine ⟨1234186853095977121588169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 822791235397318081058779 1234186853095977121588169)
            ·
              refine ⟨925640139821982841191127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1234186853095977121588169 925640139821982841191127)
              ·
                refine ⟨1388460209732974261786691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 925640139821982841191127 1388460209732974261786691)
                ·
                  refine ⟨2082690314599461392680037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1388460209732974261786691 2082690314599461392680037)
                  ·
                    refine ⟨390504433987399011127507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2082690314599461392680037 390504433987399011127507)
                    ·
                      rfl

theorem cell22_1140757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 6, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 6, 1, 2, 1, 1, 4].length) (baseStart_1140757 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1140757 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1140757 prefixEnd_1140757 := by exact prefixLift 1140757
  have htrace : WordTrace (prefixWord ++ tailWord_1140757) baseStart_1140757 baseEnd_1140757 := by
    simpa [prefixWord, tailWord_1140757, baseEnd_1140757] using wordTrace_append hprefix tailTrace_1140757
  have hstable : (prefixWord ++ tailWord_1140757).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1140757).length < 2 ^ (prefixWord ++ tailWord_1140757).sum := by decide
  have hdescent : baseEnd_1140757 < baseStart_1140757 := by decide
  rcases family_descends (prefixWord ++ tailWord_1140757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1140779 : List Nat := [1, 1, 1, 1, 2, 1, 4, 3, 2, 6]
def baseStart_1140779 : Nat := 118140960795 + 1140779 * 2 ^ 59
def prefixEnd_1140779 : Nat := 4983230072969 + 3 ^ 40 * 1140779 * 2
def baseEnd_1140779 : Nat := 390511965036998287077439

theorem tailTrace_1140779 : CollatzResearch.WordTrace tailWord_1140779 prefixEnd_1140779 390511965036998287077439 := by
  unfold tailWord_1140779
  simp only [CollatzResearch.WordTrace]
  refine ⟨41607628334159987387137391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27738418889439991591424927 41607628334159987387137391)
  ·
    refine ⟨62411442501239981080706087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41607628334159987387137391 62411442501239981080706087)
    ·
      refine ⟨93617163751859971621059131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62411442501239981080706087 93617163751859971621059131)
      ·
        refine ⟨140425745627789957431588697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93617163751859971621059131 140425745627789957431588697)
        ·
          refine ⟨105319309220842468073691523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 140425745627789957431588697 105319309220842468073691523)
          ·
            refine ⟨157978963831263702110537285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 105319309220842468073691523 157978963831263702110537285)
            ·
              refine ⟨29621055718361944145725741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 157978963831263702110537285 29621055718361944145725741)
              ·
                refine ⟨11107895894385729054647153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29621055718361944145725741 11107895894385729054647153)
                ·
                  refine ⟨8330921920789296790985365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11107895894385729054647153 8330921920789296790985365)
                  ·
                    refine ⟨390511965036998287077439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8330921920789296790985365 390511965036998287077439)
                    ·
                      rfl

theorem cell22_1140779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 3, 2, 6].length) (baseStart_1140779 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1140779 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1140779 prefixEnd_1140779 := by exact prefixLift 1140779
  have htrace : WordTrace (prefixWord ++ tailWord_1140779) baseStart_1140779 baseEnd_1140779 := by
    simpa [prefixWord, tailWord_1140779, baseEnd_1140779] using wordTrace_append hprefix tailTrace_1140779
  have hstable : (prefixWord ++ tailWord_1140779).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1140779).length < 2 ^ (prefixWord ++ tailWord_1140779).sum := by decide
  have hdescent : baseEnd_1140779 < baseStart_1140779 := by decide
  rcases family_descends (prefixWord ++ tailWord_1140779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1140832 : List Nat := [2, 1, 1, 3, 2, 4, 3, 2, 1, 3]
def baseStart_1140832 : Nat := 118140960795 + 1140832 * 2 ^ 59
def prefixEnd_1140832 : Nat := 4983230072969 + 3 ^ 40 * 1140832 * 2
def baseEnd_1140832 : Nat := 390530108020123815502277

theorem tailTrace_1140832 : CollatzResearch.WordTrace tailWord_1140832 prefixEnd_1140832 390530108020123815502277 := by
  unfold tailWord_1140832
  simp only [CollatzResearch.WordTrace]
  refine ⟨20804780701483988719408375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27739707601978651625877833 20804780701483988719408375)
  ·
    refine ⟨31207171052225983079112563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20804780701483988719408375 31207171052225983079112563)
    ·
      refine ⟨46810756578338974618668845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31207171052225983079112563 46810756578338974618668845)
      ·
        refine ⟨17554033716877115482000817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46810756578338974618668845 17554033716877115482000817)
        ·
          refine ⟨13165525287657836611500613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17554033716877115482000817 13165525287657836611500613)
          ·
            refine ⟨2468535991435844364656365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13165525287657836611500613 2468535991435844364656365)
            ·
              refine ⟨925700996788441636746137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2468535991435844364656365 925700996788441636746137)
              ·
                refine ⟨694275747591331227559603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 925700996788441636746137 694275747591331227559603)
                ·
                  refine ⟨1041413621386996841339405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 694275747591331227559603 1041413621386996841339405)
                  ·
                    refine ⟨390530108020123815502277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1041413621386996841339405 390530108020123815502277)
                    ·
                      rfl

theorem cell22_1140832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 3, 2, 1, 3].length) (baseStart_1140832 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1140832 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1140832 prefixEnd_1140832 := by exact prefixLift 1140832
  have htrace : WordTrace (prefixWord ++ tailWord_1140832) baseStart_1140832 baseEnd_1140832 := by
    simpa [prefixWord, tailWord_1140832, baseEnd_1140832] using wordTrace_append hprefix tailTrace_1140832
  have hstable : (prefixWord ++ tailWord_1140832).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1140832).length < 2 ^ (prefixWord ++ tailWord_1140832).sum := by decide
  have hdescent : baseEnd_1140832 < baseStart_1140832 := by decide
  rcases family_descends (prefixWord ++ tailWord_1140832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1140841 : List Nat := [1, 2, 1, 1, 1, 5, 2, 2, 3, 4]
def baseStart_1140841 : Nat := 118140960795 + 1140841 * 2 ^ 59
def prefixEnd_1140841 : Nat := 4983230072969 + 3 ^ 40 * 1140841 * 2
def baseEnd_1140841 : Nat := 390533188904050792027249

theorem tailTrace_1140841 : CollatzResearch.WordTrace tailWord_1140841 prefixEnd_1140841 390533188904050792027249 := by
  unfold tailWord_1140841
  simp only [CollatzResearch.WordTrace]
  refine ⟨41609889659935371975894377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27739926439956914650596251 41609889659935371975894377)
  ·
    refine ⟨31207417244951528981920783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41609889659935371975894377 31207417244951528981920783)
    ·
      refine ⟨46811125867427293472881175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31207417244951528981920783 46811125867427293472881175)
      ·
        refine ⟨70216688801140940209321763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46811125867427293472881175 70216688801140940209321763)
        ·
          refine ⟨105325033201711410313982645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70216688801140940209321763 105325033201711410313982645)
          ·
            refine ⟨9874221862660444716935873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 105325033201711410313982645 9874221862660444716935873)
            ·
              refine ⟨7405666396995333537701905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9874221862660444716935873 7405666396995333537701905)
              ·
                refine ⟨5554249797746500153276429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7405666396995333537701905 5554249797746500153276429)
                ·
                  refine ⟨2082843674154937557478661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5554249797746500153276429 2082843674154937557478661)
                  ·
                    refine ⟨390533188904050792027249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2082843674154937557478661 390533188904050792027249)
                    ·
                      rfl

theorem cell22_1140841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 2, 2, 3, 4].length) (baseStart_1140841 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1140841 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1140841 prefixEnd_1140841 := by exact prefixLift 1140841
  have htrace : WordTrace (prefixWord ++ tailWord_1140841) baseStart_1140841 baseEnd_1140841 := by
    simpa [prefixWord, tailWord_1140841, baseEnd_1140841] using wordTrace_append hprefix tailTrace_1140841
  have hstable : (prefixWord ++ tailWord_1140841).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1140841).length < 2 ^ (prefixWord ++ tailWord_1140841).sum := by decide
  have hdescent : baseEnd_1140841 < baseStart_1140841 := by decide
  rcases family_descends (prefixWord ++ tailWord_1140841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1140871 : List Nat := [1, 1, 4, 2, 1, 1, 3, 1, 3, 5]
def baseStart_1140871 : Nat := 118140960795 + 1140871 * 2 ^ 59
def prefixEnd_1140871 : Nat := 4983230072969 + 3 ^ 40 * 1140871 * 2
def baseEnd_1140871 : Nat := 390543458517140713777157

theorem tailTrace_1140871 : CollatzResearch.WordTrace tailWord_1140871 prefixEnd_1140871 390543458517140713777157 := by
  unfold tailWord_1140871
  simp only [CollatzResearch.WordTrace]
  refine ⟨41610983849826687099486467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27740655899884458066324311 41610983849826687099486467)
  ·
    refine ⟨62416475774740030649229701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41610983849826687099486467 62416475774740030649229701)
    ·
      refine ⟨11703089207763755746730569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 62416475774740030649229701 11703089207763755746730569)
      ·
        refine ⟨8777316905822816810047927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11703089207763755746730569 8777316905822816810047927)
        ·
          refine ⟨13165975358734225215071891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8777316905822816810047927 13165975358734225215071891)
          ·
            refine ⟨19748963038101337822607837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13165975358734225215071891 19748963038101337822607837)
            ·
              refine ⟨7405861139288001683477939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19748963038101337822607837 7405861139288001683477939)
              ·
                refine ⟨11108791708932002525216909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7405861139288001683477939 11108791708932002525216909)
                ·
                  refine ⟨4165796890849500946956341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11108791708932002525216909 4165796890849500946956341)
                  ·
                    refine ⟨390543458517140713777157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4165796890849500946956341 390543458517140713777157)
                    ·
                      rfl

theorem cell22_1140871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 3, 1, 3, 5].length) (baseStart_1140871 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1140871 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1140871 prefixEnd_1140871 := by exact prefixLift 1140871
  have htrace : WordTrace (prefixWord ++ tailWord_1140871) baseStart_1140871 baseEnd_1140871 := by
    simpa [prefixWord, tailWord_1140871, baseEnd_1140871] using wordTrace_append hprefix tailTrace_1140871
  have hstable : (prefixWord ++ tailWord_1140871).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1140871).length < 2 ^ (prefixWord ++ tailWord_1140871).sum := by decide
  have hdescent : baseEnd_1140871 < baseStart_1140871 := by decide
  rcases family_descends (prefixWord ++ tailWord_1140871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1140873 : List Nat := [1, 2, 1, 1, 4, 2, 2, 5, 4]
def baseStart_1140873 : Nat := 118140960795 + 1140873 * 2 ^ 59
def prefixEnd_1140873 : Nat := 4983230072969 + 3 ^ 40 * 1140873 * 2
def baseEnd_1140873 : Nat := 130181381052671125075717

theorem tailTrace_1140873 : CollatzResearch.WordTrace tailWord_1140873 prefixEnd_1140873 130181381052671125075717 := by
  unfold tailWord_1140873
  simp only [CollatzResearch.WordTrace]
  refine ⟨41611056795819441441059273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27740704530546294294039515 41611056795819441441059273)
  ·
    refine ⟨31208292596864581080794455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41611056795819441441059273 31208292596864581080794455)
    ·
      refine ⟨46812438895296871621191683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31208292596864581080794455 46812438895296871621191683)
      ·
        refine ⟨70218658342945307431787525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46812438895296871621191683 70218658342945307431787525)
        ·
          refine ⟨13165998439302245143460161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 70218658342945307431787525 13165998439302245143460161)
          ·
            refine ⟨9874498829476683857595121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13165998439302245143460161 9874498829476683857595121)
            ·
              refine ⟨7405874122107512893196341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9874498829476683857595121 7405874122107512893196341)
              ·
                refine ⟨694300698947579333737157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7405874122107512893196341 694300698947579333737157)
                ·
                  refine ⟨130181381052671125075717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 694300698947579333737157 130181381052671125075717)
                  ·
                    rfl

theorem cell22_1140873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 2, 5, 4].length) (baseStart_1140873 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1140873 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1140873 prefixEnd_1140873 := by exact prefixLift 1140873
  have htrace : WordTrace (prefixWord ++ tailWord_1140873) baseStart_1140873 baseEnd_1140873 := by
    simpa [prefixWord, tailWord_1140873, baseEnd_1140873] using wordTrace_append hprefix tailTrace_1140873
  have hstable : (prefixWord ++ tailWord_1140873).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1140873).length < 2 ^ (prefixWord ++ tailWord_1140873).sum := by decide
  have hdescent : baseEnd_1140873 < baseStart_1140873 := by decide
  rcases family_descends (prefixWord ++ tailWord_1140873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1140956 : List Nat := [2, 2, 5, 2, 1, 1, 3, 1, 2, 3]
def baseStart_1140956 : Nat := 118140960795 + 1140956 * 2 ^ 59
def prefixEnd_1140956 : Nat := 4983230072969 + 3 ^ 40 * 1140956 * 2
def baseEnd_1140956 : Nat := 390572555754228825401897

theorem tailTrace_1140956 : CollatzResearch.WordTrace tailWord_1140956 prefixEnd_1140956 390572555754228825401897 := by
  unfold tailWord_1140956
  simp only [CollatzResearch.WordTrace]
  refine ⟨20807042027259373308165361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27742722703012497744220481 20807042027259373308165361)
  ·
    refine ⟨15605281520444529981124021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20807042027259373308165361 15605281520444529981124021)
    ·
      refine ⟨1462995142541674685730377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 15605281520444529981124021 1462995142541674685730377)
      ·
        refine ⟨1097246356906256014297783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1462995142541674685730377 1097246356906256014297783)
        ·
          refine ⟨1645869535359384021446675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1097246356906256014297783 1645869535359384021446675)
          ·
            refine ⟨2468804303039076032170013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1645869535359384021446675 2468804303039076032170013)
            ·
              refine ⟨925801613639653512063755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2468804303039076032170013 925801613639653512063755)
              ·
                refine ⟨1388702420459480268095633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 925801613639653512063755 1388702420459480268095633)
                ·
                  refine ⟨1041526815344610201071725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1388702420459480268095633 1041526815344610201071725)
                  ·
                    refine ⟨390572555754228825401897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1041526815344610201071725 390572555754228825401897)
                    ·
                      rfl

theorem cell22_1140956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 3, 1, 2, 3].length) (baseStart_1140956 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1140956 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1140956 prefixEnd_1140956 := by exact prefixLift 1140956
  have htrace : WordTrace (prefixWord ++ tailWord_1140956) baseStart_1140956 baseEnd_1140956 := by
    simpa [prefixWord, tailWord_1140956, baseEnd_1140956] using wordTrace_append hprefix tailTrace_1140956
  have hstable : (prefixWord ++ tailWord_1140956).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1140956).length < 2 ^ (prefixWord ++ tailWord_1140956).sum := by decide
  have hdescent : baseEnd_1140956 < baseStart_1140956 := by decide
  rcases family_descends (prefixWord ++ tailWord_1140956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1140976 : List Nat := [2, 1, 1, 1, 3, 1, 1, 2, 2, 8]
def baseStart_1140976 : Nat := 118140960795 + 1140976 * 2 ^ 59
def prefixEnd_1140976 : Nat := 4983230072969 + 3 ^ 40 * 1140976 * 2
def baseEnd_1140976 : Nat := 390579402162955439901835

theorem tailTrace_1140976 : CollatzResearch.WordTrace tailWord_1140976 prefixEnd_1140976 390579402162955439901835 := by
  unfold tailWord_1140976
  simp only [CollatzResearch.WordTrace]
  refine ⟨20807406757223145016029391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27743209009630860021372521 20807406757223145016029391)
  ·
    refine ⟨31211110135834717524044087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20807406757223145016029391 31211110135834717524044087)
    ·
      refine ⟨46816665203752076286066131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31211110135834717524044087 46816665203752076286066131)
      ·
        refine ⟨70224997805628114429099197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46816665203752076286066131 70224997805628114429099197)
        ·
          refine ⟨26334374177110542910912199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 70224997805628114429099197 26334374177110542910912199)
          ·
            refine ⟨39501561265665814366368299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26334374177110542910912199 39501561265665814366368299)
            ·
              refine ⟨59252341898498721549552449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39501561265665814366368299 59252341898498721549552449)
              ·
                refine ⟨44439256423874041162164337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 59252341898498721549552449 44439256423874041162164337)
                ·
                  refine ⟨33329442317905530871623253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 44439256423874041162164337 33329442317905530871623253)
                  ·
                    refine ⟨390579402162955439901835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 33329442317905530871623253 390579402162955439901835)
                    ·
                      rfl

theorem cell22_1140976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 2, 2, 8].length) (baseStart_1140976 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1140976 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1140976 prefixEnd_1140976 := by exact prefixLift 1140976
  have htrace : WordTrace (prefixWord ++ tailWord_1140976) baseStart_1140976 baseEnd_1140976 := by
    simpa [prefixWord, tailWord_1140976, baseEnd_1140976] using wordTrace_append hprefix tailTrace_1140976
  have hstable : (prefixWord ++ tailWord_1140976).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1140976).length < 2 ^ (prefixWord ++ tailWord_1140976).sum := by decide
  have hdescent : baseEnd_1140976 < baseStart_1140976 := by decide
  rcases family_descends (prefixWord ++ tailWord_1140976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1141044 : List Nat := [2, 5, 1, 1, 1, 3, 3, 1, 1, 4]
def baseStart_1141044 : Nat := 118140960795 + 1141044 * 2 ^ 59
def prefixEnd_1141044 : Nat := 4983230072969 + 3 ^ 40 * 1141044 * 2
def baseEnd_1141044 : Nat := 390602679952625929201627

theorem tailTrace_1141044 : CollatzResearch.WordTrace tailWord_1141044 prefixEnd_1141044 390602679952625929201627 := by
  unfold tailWord_1141044
  simp only [CollatzResearch.WordTrace]
  refine ⟨20808646839099968822767093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27744862452133291763689457 20808646839099968822767093)
  ·
    refine ⟨1950810641165622077134415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 20808646839099968822767093 1950810641165622077134415)
    ·
      refine ⟨2926215961748433115701623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1950810641165622077134415 2926215961748433115701623)
      ·
        refine ⟨4389323942622649673552435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2926215961748433115701623 4389323942622649673552435)
        ·
          refine ⟨6583985913933974510328653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4389323942622649673552435 6583985913933974510328653)
          ·
            refine ⟨2468994717725240441373245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6583985913933974510328653 2468994717725240441373245)
            ·
              refine ⟨925873019146965165514967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2468994717725240441373245 925873019146965165514967)
              ·
                refine ⟨1388809528720447748272451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 925873019146965165514967 1388809528720447748272451)
                ·
                  refine ⟨2083214293080671622408677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1388809528720447748272451 2083214293080671622408677)
                  ·
                    refine ⟨390602679952625929201627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2083214293080671622408677 390602679952625929201627)
                    ·
                      rfl

theorem cell22_1141044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 3, 1, 1, 4].length) (baseStart_1141044 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1141044 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1141044 prefixEnd_1141044 := by exact prefixLift 1141044
  have htrace : WordTrace (prefixWord ++ tailWord_1141044) baseStart_1141044 baseEnd_1141044 := by
    simpa [prefixWord, tailWord_1141044, baseEnd_1141044] using wordTrace_append hprefix tailTrace_1141044
  have hstable : (prefixWord ++ tailWord_1141044).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1141044).length < 2 ^ (prefixWord ++ tailWord_1141044).sum := by decide
  have hdescent : baseEnd_1141044 < baseStart_1141044 := by decide
  rcases family_descends (prefixWord ++ tailWord_1141044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1141115 : List Nat := [1, 1, 1, 1, 1, 7, 3, 2, 5]
def baseStart_1141115 : Nat := 118140960795 + 1141115 * 2 ^ 59
def prefixEnd_1141115 : Nat := 4983230072969 + 3 ^ 40 * 1141115 * 2
def baseEnd_1141115 : Nat := 130208994901201803558803

theorem tailTrace_1141115 : CollatzResearch.WordTrace tailWord_1141115 prefixEnd_1141115 130208994901201803558803 := by
  unfold tailWord_1141115
  simp only [CollatzResearch.WordTrace]
  refine ⟨41619883260942716771368799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27746588840628477847579199 41619883260942716771368799)
  ·
    refine ⟨62429824891414075157053199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41619883260942716771368799 62429824891414075157053199)
    ·
      refine ⟨93644737337121112735579799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62429824891414075157053199 93644737337121112735579799)
      ·
        refine ⟨140467106005681669103369699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93644737337121112735579799 140467106005681669103369699)
        ·
          refine ⟨210700659008522503655054549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 140467106005681669103369699 210700659008522503655054549)
          ·
            refine ⟨4938296695512246179415341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 210700659008522503655054549 4938296695512246179415341)
            ·
              refine ⟨1851861260817092317280753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4938296695512246179415341 1851861260817092317280753)
              ·
                refine ⟨1388895945612819237960565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1851861260817092317280753 1388895945612819237960565)
                ·
                  refine ⟨130208994901201803558803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1388895945612819237960565 130208994901201803558803)
                  ·
                    rfl

theorem cell22_1141115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 3, 2, 5].length) (baseStart_1141115 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1141115 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1141115 prefixEnd_1141115 := by exact prefixLift 1141115
  have htrace : WordTrace (prefixWord ++ tailWord_1141115) baseStart_1141115 baseEnd_1141115 := by
    simpa [prefixWord, tailWord_1141115, baseEnd_1141115] using wordTrace_append hprefix tailTrace_1141115
  have hstable : (prefixWord ++ tailWord_1141115).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1141115).length < 2 ^ (prefixWord ++ tailWord_1141115).sum := by decide
  have hdescent : baseEnd_1141115 < baseStart_1141115 := by decide
  rcases family_descends (prefixWord ++ tailWord_1141115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1141132 : List Nat := [2, 2, 1, 2, 1, 5, 3, 1, 5]
def baseStart_1141132 : Nat := 118140960795 + 1141132 * 2 ^ 59
def prefixEnd_1141132 : Nat := 4983230072969 + 3 ^ 40 * 1141132 * 2
def baseEnd_1141132 : Nat := 130210934717007677667119

theorem tailTrace_1141132 : CollatzResearch.WordTrace tailWord_1141132 prefixEnd_1141132 130210934717007677667119 := by
  unfold tailWord_1141132
  simp only [CollatzResearch.WordTrace]
  refine ⟨20810251650940564337368825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27747002201254085783158433 20810251650940564337368825)
  ·
    refine ⟨15607688738205423253026619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20810251650940564337368825 15607688738205423253026619)
    ·
      refine ⟨23411533107308134879539929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15607688738205423253026619 23411533107308134879539929)
      ·
        refine ⟨17558649830481101159654947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23411533107308134879539929 17558649830481101159654947)
        ·
          refine ⟨26337974745721651739482421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17558649830481101159654947 26337974745721651739482421)
          ·
            refine ⟨2469185132411404850576477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 26337974745721651739482421 2469185132411404850576477)
            ·
              refine ⟨925944424654276818966179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2469185132411404850576477 925944424654276818966179)
              ·
                refine ⟨1388916636981415228449269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 925944424654276818966179 1388916636981415228449269)
                ·
                  refine ⟨130210934717007677667119, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1388916636981415228449269 130210934717007677667119)
                  ·
                    rfl

theorem cell22_1141132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 3, 1, 5].length) (baseStart_1141132 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1141132 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1141132 prefixEnd_1141132 := by exact prefixLift 1141132
  have htrace : WordTrace (prefixWord ++ tailWord_1141132) baseStart_1141132 baseEnd_1141132 := by
    simpa [prefixWord, tailWord_1141132, baseEnd_1141132] using wordTrace_append hprefix tailTrace_1141132
  have hstable : (prefixWord ++ tailWord_1141132).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1141132).length < 2 ^ (prefixWord ++ tailWord_1141132).sum := by decide
  have hdescent : baseEnd_1141132 < baseStart_1141132 := by decide
  rcases family_descends (prefixWord ++ tailWord_1141132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1141153 : List Nat := [1, 2, 3, 5, 1, 2, 1, 3, 1, 3]
def baseStart_1141153 : Nat := 118140960795 + 1141153 * 2 ^ 59
def prefixEnd_1141153 : Nat := 4983230072969 + 3 ^ 40 * 1141153 * 2
def baseEnd_1141153 : Nat := 390639992880185978226293

theorem tailTrace_1141153 : CollatzResearch.WordTrace tailWord_1141153 prefixEnd_1141153 390639992880185978226293 := by
  unfold tailWord_1141153
  simp only [CollatzResearch.WordTrace]
  refine ⟨41621269234805049261252113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27747512823203366174168075 41621269234805049261252113)
  ·
    refine ⟨31215951926103786945939085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41621269234805049261252113 31215951926103786945939085)
    ·
      refine ⟨11705981972288920104727157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31215951926103786945939085 11705981972288920104727157)
      ·
        refine ⟨1097435809902086259818171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 11705981972288920104727157 1097435809902086259818171)
        ·
          refine ⟨1646153714853129389727257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1097435809902086259818171 1646153714853129389727257)
          ·
            refine ⟨1234615286139847042295443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1646153714853129389727257 1234615286139847042295443)
            ·
              refine ⟨1851922929209770563443165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1234615286139847042295443 1851922929209770563443165)
              ·
                refine ⟨694471098453663961291187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1851922929209770563443165 694471098453663961291187)
                ·
                  refine ⟨1041706647680495941936781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 694471098453663961291187 1041706647680495941936781)
                  ·
                    refine ⟨390639992880185978226293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1041706647680495941936781 390639992880185978226293)
                    ·
                      rfl

theorem cell22_1141153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 2, 1, 3, 1, 3].length) (baseStart_1141153 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1141153 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1141153 prefixEnd_1141153 := by exact prefixLift 1141153
  have htrace : WordTrace (prefixWord ++ tailWord_1141153) baseStart_1141153 baseEnd_1141153 := by
    simpa [prefixWord, tailWord_1141153, baseEnd_1141153] using wordTrace_append hprefix tailTrace_1141153
  have hstable : (prefixWord ++ tailWord_1141153).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1141153).length < 2 ^ (prefixWord ++ tailWord_1141153).sum := by decide
  have hdescent : baseEnd_1141153 < baseStart_1141153 := by decide
  rcases family_descends (prefixWord ++ tailWord_1141153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1141177 : List Nat := [1, 2, 1, 4, 3, 3, 1, 1, 6]
def baseStart_1141177 : Nat := 118140960795 + 1141177 * 2 ^ 59
def prefixEnd_1141177 : Nat := 4983230072969 + 3 ^ 40 * 1141177 * 2
def baseEnd_1141177 : Nat := 130216069523552638542073

theorem tailTrace_1141177 : CollatzResearch.WordTrace tailWord_1141177 prefixEnd_1141177 130216069523552638542073 := by
  unfold tailWord_1141177
  simp only [CollatzResearch.WordTrace]
  refine ⟨41622144586718101360125785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27748096391145400906750523 41622144586718101360125785)
  ·
    refine ⟨31216608440038576020094339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41622144586718101360125785 31216608440038576020094339)
    ·
      refine ⟨46824912660057864030141509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31216608440038576020094339 46824912660057864030141509)
      ·
        refine ⟨8779671123760849505651533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 46824912660057864030141509 8779671123760849505651533)
        ·
          refine ⟨3292376671410318564619325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8779671123760849505651533 3292376671410318564619325)
          ·
            refine ⟨1234641251778869461732247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3292376671410318564619325 1234641251778869461732247)
            ·
              refine ⟨1851961877668304192598371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1234641251778869461732247 1851961877668304192598371)
              ·
                refine ⟨2777942816502456288897557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1851961877668304192598371 2777942816502456288897557)
                ·
                  refine ⟨130216069523552638542073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2777942816502456288897557 130216069523552638542073)
                  ·
                    rfl

theorem cell22_1141177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 3, 1, 1, 6].length) (baseStart_1141177 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1141177 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1141177 prefixEnd_1141177 := by exact prefixLift 1141177
  have htrace : WordTrace (prefixWord ++ tailWord_1141177) baseStart_1141177 baseEnd_1141177 := by
    simpa [prefixWord, tailWord_1141177, baseEnd_1141177] using wordTrace_append hprefix tailTrace_1141177
  have hstable : (prefixWord ++ tailWord_1141177).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1141177).length < 2 ^ (prefixWord ++ tailWord_1141177).sum := by decide
  have hdescent : baseEnd_1141177 < baseStart_1141177 := by decide
  rcases family_descends (prefixWord ++ tailWord_1141177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1141196 : List Nat := [2, 2, 1, 4, 4, 1, 1, 2, 1, 4]
def baseStart_1141196 : Nat := 118140960795 + 1141196 * 2 ^ 59
def prefixEnd_1141196 : Nat := 4983230072969 + 3 ^ 40 * 1141196 * 2
def baseEnd_1141196 : Nat := 390654712658948199401161

theorem tailTrace_1141196 : CollatzResearch.WordTrace tailWord_1141196 prefixEnd_1141196 390654712658948199401161 := by
  unfold tailWord_1141196
  simp only [CollatzResearch.WordTrace]
  refine ⟨20811418786824633802533721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27748558382432845070044961 20811418786824633802533721)
  ·
    refine ⟨15608564090118475351900291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20811418786824633802533721 15608564090118475351900291)
    ·
      refine ⟨23412846135177713027850437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15608564090118475351900291 23412846135177713027850437)
      ·
        refine ⟨4389908650345821192721957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23412846135177713027850437 4389908650345821192721957)
        ·
          refine ⟨823107871939841473635367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4389908650345821192721957 823107871939841473635367)
          ·
            refine ⟨1234661807909762210453051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 823107871939841473635367 1234661807909762210453051)
            ·
              refine ⟨1851992711864643315679577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1234661807909762210453051 1851992711864643315679577)
              ·
                refine ⟨1388994533898482486759683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1851992711864643315679577 1388994533898482486759683)
                ·
                  refine ⟨2083491800847723730139525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1388994533898482486759683 2083491800847723730139525)
                  ·
                    refine ⟨390654712658948199401161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2083491800847723730139525 390654712658948199401161)
                    ·
                      rfl

theorem cell22_1141196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 4, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 4, 1, 1, 2, 1, 4].length) (baseStart_1141196 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1141196 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1141196 prefixEnd_1141196 := by exact prefixLift 1141196
  have htrace : WordTrace (prefixWord ++ tailWord_1141196) baseStart_1141196 baseEnd_1141196 := by
    simpa [prefixWord, tailWord_1141196, baseEnd_1141196] using wordTrace_append hprefix tailTrace_1141196
  have hstable : (prefixWord ++ tailWord_1141196).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1141196).length < 2 ^ (prefixWord ++ tailWord_1141196).sum := by decide
  have hdescent : baseEnd_1141196 < baseStart_1141196 := by decide
  rcases family_descends (prefixWord ++ tailWord_1141196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1141205 : List Nat := [1, 3, 2, 3, 1, 2, 2, 8]
def baseStart_1141205 : Nat := 118140960795 + 1141205 * 2 ^ 59
def prefixEnd_1141205 : Nat := 4983230072969 + 3 ^ 40 * 1141205 * 2
def baseEnd_1141205 : Nat := 43406421504763908436237

theorem tailTrace_1141205 : CollatzResearch.WordTrace tailWord_1141205 prefixEnd_1141205 43406421504763908436237 := by
  unfold tailWord_1141205
  simp only [CollatzResearch.WordTrace]
  refine ⟨41623165830616662142145069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27748777220411108094763379 41623165830616662142145069)
  ·
    refine ⟨15608687186481248303304401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41623165830616662142145069 15608687186481248303304401)
    ·
      refine ⟨11706515389860936227478301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15608687186481248303304401 11706515389860936227478301)
      ·
        refine ⟨4389943271197851085304363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11706515389860936227478301 4389943271197851085304363)
        ·
          refine ⟨6584914906796776627956545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4389943271197851085304363 6584914906796776627956545)
          ·
            refine ⟨4938686180097582470967409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6584914906796776627956545 4938686180097582470967409)
            ·
              refine ⟨3704014635073186853225557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4938686180097582470967409 3704014635073186853225557)
              ·
                refine ⟨43406421504763908436237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3704014635073186853225557 43406421504763908436237)
                ·
                  rfl

theorem cell22_1141205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 2, 8].length) (baseStart_1141205 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1141205 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1141205 prefixEnd_1141205 := by exact prefixLift 1141205
  have htrace : WordTrace (prefixWord ++ tailWord_1141205) baseStart_1141205 baseEnd_1141205 := by
    simpa [prefixWord, tailWord_1141205, baseEnd_1141205] using wordTrace_append hprefix tailTrace_1141205
  have hstable : (prefixWord ++ tailWord_1141205).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1141205).length < 2 ^ (prefixWord ++ tailWord_1141205).sum := by decide
  have hdescent : baseEnd_1141205 < baseStart_1141205 := by decide
  rcases family_descends (prefixWord ++ tailWord_1141205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1141284 : List Nat := [2, 3, 1, 5, 1, 1, 1, 1, 7]
def baseStart_1141284 : Nat := 118140960795 + 1141284 * 2 ^ 59
def prefixEnd_1141284 : Nat := 4983230072969 + 3 ^ 40 * 1141284 * 2
def baseEnd_1141284 : Nat := 130228278952448434400297

theorem tailTrace_1141284 : CollatzResearch.WordTrace tailWord_1141284 prefixEnd_1141284 130228278952448434400297 := by
  unfold tailWord_1141284
  simp only [CollatzResearch.WordTrace]
  refine ⟨20813023598665229317135453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27750698131553639089513937 20813023598665229317135453)
  ·
    refine ⟨7804883849499460993925795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20813023598665229317135453 7804883849499460993925795)
    ·
      refine ⟨11707325774249191490888693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7804883849499460993925795 11707325774249191490888693)
      ·
        refine ⟨1097561791335861702270815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 11707325774249191490888693 1097561791335861702270815)
        ·
          refine ⟨1646342687003792553406223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1097561791335861702270815 1646342687003792553406223)
          ·
            refine ⟨2469514030505688830109335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1646342687003792553406223 2469514030505688830109335)
            ·
              refine ⟨3704271045758533245164003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2469514030505688830109335 3704271045758533245164003)
              ·
                refine ⟨5556406568637799867746005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3704271045758533245164003 5556406568637799867746005)
                ·
                  refine ⟨130228278952448434400297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5556406568637799867746005 130228278952448434400297)
                  ·
                    rfl

theorem cell22_1141284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 1, 1, 7].length) (baseStart_1141284 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1141284 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1141284 prefixEnd_1141284 := by exact prefixLift 1141284
  have htrace : WordTrace (prefixWord ++ tailWord_1141284) baseStart_1141284 baseEnd_1141284 := by
    simpa [prefixWord, tailWord_1141284, baseEnd_1141284] using wordTrace_append hprefix tailTrace_1141284
  have hstable : (prefixWord ++ tailWord_1141284).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1141284).length < 2 ^ (prefixWord ++ tailWord_1141284).sum := by decide
  have hdescent : baseEnd_1141284 < baseStart_1141284 := by decide
  rcases family_descends (prefixWord ++ tailWord_1141284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1141327 : List Nat := [1, 1, 2, 1, 1, 2, 5, 2, 4, 3]
def baseStart_1141327 : Nat := 118140960795 + 1141327 * 2 ^ 59
def prefixEnd_1141327 : Nat := 4983230072969 + 3 ^ 40 * 1141327 * 2
def baseEnd_1141327 : Nat := 390699556636107524375759

theorem tailTrace_1141327 : CollatzResearch.WordTrace tailWord_1141327 prefixEnd_1141327 390699556636107524375759 := by
  unfold tailWord_1141327
  simp only [CollatzResearch.WordTrace]
  refine ⟨41627615536174676978086235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27751743690783117985390823 41627615536174676978086235)
  ·
    refine ⟨62441423304262015467129353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41627615536174676978086235 62441423304262015467129353)
    ·
      refine ⟨46831067478196511600347015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62441423304262015467129353 46831067478196511600347015)
      ·
        refine ⟨70246601217294767400520523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46831067478196511600347015 70246601217294767400520523)
        ·
          refine ⟨105369901825942151100780785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70246601217294767400520523 105369901825942151100780785)
          ·
            refine ⟨79027426369456613325585589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 105369901825942151100780785 79027426369456613325585589)
            ·
              refine ⟨7408821222136557499273649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 79027426369456613325585589 7408821222136557499273649)
              ·
                refine ⟨5556615916602418124455237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7408821222136557499273649 5556615916602418124455237)
                ·
                  refine ⟨1041865484362953398335357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5556615916602418124455237 1041865484362953398335357)
                  ·
                    refine ⟨390699556636107524375759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1041865484362953398335357 390699556636107524375759)
                    ·
                      rfl

theorem cell22_1141327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 5, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 5, 2, 4, 3].length) (baseStart_1141327 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1141327 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1141327 prefixEnd_1141327 := by exact prefixLift 1141327
  have htrace : WordTrace (prefixWord ++ tailWord_1141327) baseStart_1141327 baseEnd_1141327 := by
    simpa [prefixWord, tailWord_1141327, baseEnd_1141327] using wordTrace_append hprefix tailTrace_1141327
  have hstable : (prefixWord ++ tailWord_1141327).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1141327).length < 2 ^ (prefixWord ++ tailWord_1141327).sum := by decide
  have hdescent : baseEnd_1141327 < baseStart_1141327 := by decide
  rcases family_descends (prefixWord ++ tailWord_1141327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1141329 : List Nat := [1, 2, 2, 1, 3, 3, 3, 3, 4]
def baseStart_1141329 : Nat := 118140960795 + 1141329 * 2 ^ 59
def prefixEnd_1141329 : Nat := 4983230072969 + 3 ^ 40 * 1141329 * 2
def baseEnd_1141329 : Nat := 130233413758993395275251

theorem tailTrace_1141329 : CollatzResearch.WordTrace tailWord_1141329 prefixEnd_1141329 130233413758993395275251 := by
  unfold tailWord_1141329
  simp only [CollatzResearch.WordTrace]
  refine ⟨41627688482167431319659041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27751792321444954213106027 41627688482167431319659041)
  ·
    refine ⟨31220766361625573489744281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41627688482167431319659041 31220766361625573489744281)
    ·
      refine ⟨23415574771219180117308211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31220766361625573489744281 23415574771219180117308211)
      ·
        refine ⟨35123362156828770175962317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23415574771219180117308211 35123362156828770175962317)
        ·
          refine ⟨13171260808810788815985869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35123362156828770175962317 13171260808810788815985869)
          ·
            refine ⟨4939222803304045805994701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13171260808810788815985869 4939222803304045805994701)
            ·
              refine ⟨1852208551239017177248013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4939222803304045805994701 1852208551239017177248013)
              ·
                refine ⟨694578206714631441468005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1852208551239017177248013 694578206714631441468005)
                ·
                  refine ⟨130233413758993395275251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 694578206714631441468005 130233413758993395275251)
                  ·
                    rfl

theorem cell22_1141329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 3, 3, 4].length) (baseStart_1141329 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1141329 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1141329 prefixEnd_1141329 := by exact prefixLift 1141329
  have htrace : WordTrace (prefixWord ++ tailWord_1141329) baseStart_1141329 baseEnd_1141329 := by
    simpa [prefixWord, tailWord_1141329, baseEnd_1141329] using wordTrace_append hprefix tailTrace_1141329
  have hstable : (prefixWord ++ tailWord_1141329).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1141329).length < 2 ^ (prefixWord ++ tailWord_1141329).sum := by decide
  have hdescent : baseEnd_1141329 < baseStart_1141329 := by decide
  rcases family_descends (prefixWord ++ tailWord_1141329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1141355 : List Nat := [1, 1, 1, 1, 2, 2, 1, 4, 2, 7]
def baseStart_1141355 : Nat := 118140960795 + 1141355 * 2 ^ 59
def prefixEnd_1141355 : Nat := 4983230072969 + 3 ^ 40 * 1141355 * 2
def baseEnd_1141355 : Nat := 390709141608324784675673

theorem tailTrace_1141355 : CollatzResearch.WordTrace tailWord_1141355 prefixEnd_1141355 390709141608324784675673 := by
  unfold tailWord_1141355
  simp only [CollatzResearch.WordTrace]
  refine ⟨41628636780073237760105519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27752424520048825173403679 41628636780073237760105519)
  ·
    refine ⟨62442955170109856640158279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41628636780073237760105519 62442955170109856640158279)
    ·
      refine ⟨93664432755164784960237419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62442955170109856640158279 93664432755164784960237419)
      ·
        refine ⟨140496649132747177440356129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93664432755164784960237419 140496649132747177440356129)
        ·
          refine ⟨105372486849560383080267097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 140496649132747177440356129 105372486849560383080267097)
          ·
            refine ⟨79029365137170287310200323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 105372486849560383080267097 79029365137170287310200323)
            ·
              refine ⟨118544047705755430965300485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79029365137170287310200323 118544047705755430965300485)
              ·
                refine ⟨22227008944829143305993841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 118544047705755430965300485 22227008944829143305993841)
                ·
                  refine ⟨16670256708621857479495381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22227008944829143305993841 16670256708621857479495381)
                  ·
                    refine ⟨390709141608324784675673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 16670256708621857479495381 390709141608324784675673)
                    ·
                      rfl

theorem cell22_1141355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 4, 2, 7].length) (baseStart_1141355 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1141355 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1141355 prefixEnd_1141355 := by exact prefixLift 1141355
  have htrace : WordTrace (prefixWord ++ tailWord_1141355) baseStart_1141355 baseEnd_1141355 := by
    simpa [prefixWord, tailWord_1141355, baseEnd_1141355] using wordTrace_append hprefix tailTrace_1141355
  have hstable : (prefixWord ++ tailWord_1141355).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1141355).length < 2 ^ (prefixWord ++ tailWord_1141355).sum := by decide
  have hdescent : baseEnd_1141355 < baseStart_1141355 := by decide
  rcases family_descends (prefixWord ++ tailWord_1141355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1141357 : List Nat := [1, 5, 1, 1, 3, 1, 1, 9]
def baseStart_1141357 : Nat := 118140960795 + 1141357 * 2 ^ 59
def prefixEnd_1141357 : Nat := 4983230072969 + 3 ^ 40 * 1141357 * 2
def baseEnd_1141357 : Nat := 43412202916577494013963

theorem tailTrace_1141357 : CollatzResearch.WordTrace tailWord_1141357 prefixEnd_1141357 43412202916577494013963 := by
  unfold tailWord_1141357
  simp only [CollatzResearch.WordTrace]
  refine ⟨41628709726065992101678325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27752473150710661401118883 41628709726065992101678325)
  ·
    refine ⟨3902691536818686759532343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 41628709726065992101678325 3902691536818686759532343)
    ·
      refine ⟨5854037305228030139298515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3902691536818686759532343 5854037305228030139298515)
      ·
        refine ⟨8781055957842045208947773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5854037305228030139298515 8781055957842045208947773)
        ·
          refine ⟨3292895984190766953355415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8781055957842045208947773 3292895984190766953355415)
          ·
            refine ⟨4939343976286150430033123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3292895984190766953355415 4939343976286150430033123)
            ·
              refine ⟨7409015964429225645049685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4939343976286150430033123 7409015964429225645049685)
              ·
                refine ⟨43412202916577494013963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 7409015964429225645049685 43412202916577494013963)
                ·
                  rfl

theorem cell22_1141357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 1, 9].length) (baseStart_1141357 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1141357 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1141357 prefixEnd_1141357 := by exact prefixLift 1141357
  have htrace : WordTrace (prefixWord ++ tailWord_1141357) baseStart_1141357 baseEnd_1141357 := by
    simpa [prefixWord, tailWord_1141357, baseEnd_1141357] using wordTrace_append hprefix tailTrace_1141357
  have hstable : (prefixWord ++ tailWord_1141357).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1141357).length < 2 ^ (prefixWord ++ tailWord_1141357).sum := by decide
  have hdescent : baseEnd_1141357 < baseStart_1141357 := by decide
  rcases family_descends (prefixWord ++ tailWord_1141357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1141406 : List Nat := [4, 3, 1, 1, 1, 1, 2, 3, 3, 3]
def baseStart_1141406 : Nat := 118140960795 + 1141406 * 2 ^ 59
def prefixEnd_1141406 : Nat := 4983230072969 + 3 ^ 40 * 1141406 * 2
def baseEnd_1141406 : Nat := 390726599950577651650517

theorem tailTrace_1141406 : CollatzResearch.WordTrace tailWord_1141406 prefixEnd_1141406 390726599950577651650517 := by
  unfold tailWord_1141406
  simp only [CollatzResearch.WordTrace]
  refine ⟨5203812112861059183776509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27753664601925648980141381 5203812112861059183776509)
  ·
    refine ⟨1951429542322897193916191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5203812112861059183776509 1951429542322897193916191)
    ·
      refine ⟨2927144313484345790874287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1951429542322897193916191 2927144313484345790874287)
      ·
        refine ⟨4390716470226518686311431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2927144313484345790874287 4390716470226518686311431)
        ·
          refine ⟨6586074705339778029467147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4390716470226518686311431 6586074705339778029467147)
          ·
            refine ⟨9879112058009667044200721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6586074705339778029467147 9879112058009667044200721)
            ·
              refine ⟨7409334043507250283150541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9879112058009667044200721 7409334043507250283150541)
              ·
                refine ⟨2778500266315218856181453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7409334043507250283150541 2778500266315218856181453)
                ·
                  refine ⟨1041937599868207071068045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2778500266315218856181453 1041937599868207071068045)
                  ·
                    refine ⟨390726599950577651650517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1041937599868207071068045 390726599950577651650517)
                    ·
                      rfl

theorem cell22_1141406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 2, 3, 3, 3].length) (baseStart_1141406 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1141406 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1141406 prefixEnd_1141406 := by exact prefixLift 1141406
  have htrace : WordTrace (prefixWord ++ tailWord_1141406) baseStart_1141406 baseEnd_1141406 := by
    simpa [prefixWord, tailWord_1141406, baseEnd_1141406] using wordTrace_append hprefix tailTrace_1141406
  have hstable : (prefixWord ++ tailWord_1141406).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1141406).length < 2 ^ (prefixWord ++ tailWord_1141406).sum := by decide
  have hdescent : baseEnd_1141406 < baseStart_1141406 := by decide
  rcases family_descends (prefixWord ++ tailWord_1141406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1141464 : List Nat := [2, 1, 2, 2, 3, 3, 2, 1, 6]
def baseStart_1141464 : Nat := 118140960795 + 1141464 * 2 ^ 59
def prefixEnd_1141464 : Nat := 4983230072969 + 3 ^ 40 * 1141464 * 2
def baseEnd_1141464 : Nat := 130248818178628277900113

theorem tailTrace_1141464 : CollatzResearch.WordTrace tailWord_1141464 prefixEnd_1141464 130248818178628277900113 := by
  unfold tailWord_1141464
  simp only [CollatzResearch.WordTrace]
  refine ⟨20816306168339174687911723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27755074891118899583882297 20816306168339174687911723)
  ·
    refine ⟨31224459252508762031867585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20816306168339174687911723 31224459252508762031867585)
    ·
      refine ⟨23418344439381571523900689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31224459252508762031867585 23418344439381571523900689)
      ·
        refine ⟨17563758329536178642925517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23418344439381571523900689 17563758329536178642925517)
        ·
          refine ⟨6586409373576066991097069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17563758329536178642925517 6586409373576066991097069)
          ·
            refine ⟨2469903515091025121661401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6586409373576066991097069 2469903515091025121661401)
            ·
              refine ⟨1852427636318268841246051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2469903515091025121661401 1852427636318268841246051)
              ·
                refine ⟨2778641454477403261869077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1852427636318268841246051 2778641454477403261869077)
                ·
                  refine ⟨130248818178628277900113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2778641454477403261869077 130248818178628277900113)
                  ·
                    rfl

theorem cell22_1141464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 2, 1, 6].length) (baseStart_1141464 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1141464 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1141464 prefixEnd_1141464 := by exact prefixLift 1141464
  have htrace : WordTrace (prefixWord ++ tailWord_1141464) baseStart_1141464 baseEnd_1141464 := by
    simpa [prefixWord, tailWord_1141464, baseEnd_1141464] using wordTrace_append hprefix tailTrace_1141464
  have hstable : (prefixWord ++ tailWord_1141464).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1141464).length < 2 ^ (prefixWord ++ tailWord_1141464).sum := by decide
  have hdescent : baseEnd_1141464 < baseStart_1141464 := by decide
  rcases family_descends (prefixWord ++ tailWord_1141464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1141494 : List Nat := [5, 1, 1, 1, 1, 2, 1, 3, 1, 6]
def baseStart_1141494 : Nat := 118140960795 + 1141494 * 2 ^ 59
def prefixEnd_1141494 : Nat := 4983230072969 + 3 ^ 40 * 1141494 * 2
def baseEnd_1141494 : Nat := 390756724148974755450247

theorem tailTrace_1141494 : CollatzResearch.WordTrace tailWord_1141494 prefixEnd_1141494 390756724148974755450247 := by
  unfold tailWord_1141494
  simp only [CollatzResearch.WordTrace]
  refine ⟨2602106657910604031213471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 27755804351046442999610357 2602106657910604031213471)
  ·
    refine ⟨3903159986865906046820207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2602106657910604031213471 3903159986865906046820207)
    ·
      refine ⟨5854739980298859070230311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3903159986865906046820207 5854739980298859070230311)
      ·
        refine ⟨8782109970448288605345467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5854739980298859070230311 8782109970448288605345467)
        ·
          refine ⟨13173164955672432908018201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8782109970448288605345467 13173164955672432908018201)
          ·
            refine ⟨9879873716754324681013651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13173164955672432908018201 9879873716754324681013651)
            ·
              refine ⟨14819810575131487021520477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9879873716754324681013651 14819810575131487021520477)
              ·
                refine ⟨5557428965674307633070179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14819810575131487021520477 5557428965674307633070179)
                ·
                  refine ⟨8336143448511461449605269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5557428965674307633070179 8336143448511461449605269)
                  ·
                    refine ⟨390756724148974755450247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8336143448511461449605269 390756724148974755450247)
                    ·
                      rfl

theorem cell22_1141494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 3, 1, 6].length) (baseStart_1141494 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1141494 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1141494 prefixEnd_1141494 := by exact prefixLift 1141494
  have htrace : WordTrace (prefixWord ++ tailWord_1141494) baseStart_1141494 baseEnd_1141494 := by
    simpa [prefixWord, tailWord_1141494, baseEnd_1141494] using wordTrace_append hprefix tailTrace_1141494
  have hstable : (prefixWord ++ tailWord_1141494).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1141494).length < 2 ^ (prefixWord ++ tailWord_1141494).sum := by decide
  have hdescent : baseEnd_1141494 < baseStart_1141494 := by decide
  rcases family_descends (prefixWord ++ tailWord_1141494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1141511 : List Nat := [1, 1, 4, 4, 1, 2, 1, 2, 2, 4]
def baseStart_1141511 : Nat := 118140960795 + 1141511 * 2 ^ 59
def prefixEnd_1141511 : Nat := 4983230072969 + 3 ^ 40 * 1141511 * 2
def baseEnd_1141511 : Nat := 390762543596392377775195

theorem tailTrace_1141511 : CollatzResearch.WordTrace tailWord_1141511 prefixEnd_1141511 390762543596392377775195 := by
  unfold tailWord_1141511
  simp only [CollatzResearch.WordTrace]
  refine ⟨41634326567508076402784387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27756217711672050935189591 41634326567508076402784387)
  ·
    refine ⟨62451489851262114604176581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41634326567508076402784387 62451489851262114604176581)
    ·
      refine ⟨11709654347111646488283109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 62451489851262114604176581 11709654347111646488283109)
      ·
        refine ⟨2195560190083433716553083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11709654347111646488283109 2195560190083433716553083)
        ·
          refine ⟨3293340285125150574829625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2195560190083433716553083 3293340285125150574829625)
          ·
            refine ⟨2470005213843862931122219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3293340285125150574829625 2470005213843862931122219)
            ·
              refine ⟨3705007820765794396683329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2470005213843862931122219 3705007820765794396683329)
              ·
                refine ⟨2778755865574345797512497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3705007820765794396683329 2778755865574345797512497)
                ·
                  refine ⟨2084066899180759348134373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2778755865574345797512497 2084066899180759348134373)
                  ·
                    refine ⟨390762543596392377775195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2084066899180759348134373 390762543596392377775195)
                    ·
                      rfl

theorem cell22_1141511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 1, 2, 2, 4].length) (baseStart_1141511 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1141511 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1141511 prefixEnd_1141511 := by exact prefixLift 1141511
  have htrace : WordTrace (prefixWord ++ tailWord_1141511) baseStart_1141511 baseEnd_1141511 := by
    simpa [prefixWord, tailWord_1141511, baseEnd_1141511] using wordTrace_append hprefix tailTrace_1141511
  have hstable : (prefixWord ++ tailWord_1141511).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1141511).length < 2 ^ (prefixWord ++ tailWord_1141511).sum := by decide
  have hdescent : baseEnd_1141511 < baseStart_1141511 := by decide
  rcases family_descends (prefixWord ++ tailWord_1141511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1141584 : List Nat := [2, 1, 1, 1, 1, 4, 3, 2, 3, 4]
def baseStart_1141584 : Nat := 118140960795 + 1141584 * 2 ^ 59
def prefixEnd_1141584 : Nat := 4983230072969 + 3 ^ 40 * 1141584 * 2
def baseEnd_1141584 : Nat := 390787532988244520699971

theorem tailTrace_1141584 : CollatzResearch.WordTrace tailWord_1141584 prefixEnd_1141584 390787532988244520699971 := by
  unfold tailWord_1141584
  simp only [CollatzResearch.WordTrace]
  refine ⟨20818494548121804935095903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27757992730829073246794537 20818494548121804935095903)
  ·
    refine ⟨31227741822182707402643855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20818494548121804935095903 31227741822182707402643855)
    ·
      refine ⟨46841612733274061103965783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31227741822182707402643855 46841612733274061103965783)
      ·
        refine ⟨70262419099911091655948675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46841612733274061103965783 70262419099911091655948675)
        ·
          refine ⟨105393628649866637483923013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70262419099911091655948675 105393628649866637483923013)
          ·
            refine ⟨19761305371849994528235565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 105393628649866637483923013 19761305371849994528235565)
            ·
              refine ⟨7410489514443747948088337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19761305371849994528235565 7410489514443747948088337)
              ·
                refine ⟨5557867135832810961066253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7410489514443747948088337 5557867135832810961066253)
                ·
                  refine ⟨2084200175937304110399845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5557867135832810961066253 2084200175937304110399845)
                  ·
                    refine ⟨390787532988244520699971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2084200175937304110399845 390787532988244520699971)
                    ·
                      rfl

theorem cell22_1141584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 3, 2, 3, 4].length) (baseStart_1141584 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1141584 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1141584 prefixEnd_1141584 := by exact prefixLift 1141584
  have htrace : WordTrace (prefixWord ++ tailWord_1141584) baseStart_1141584 baseEnd_1141584 := by
    simpa [prefixWord, tailWord_1141584, baseEnd_1141584] using wordTrace_append hprefix tailTrace_1141584
  have hstable : (prefixWord ++ tailWord_1141584).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1141584).length < 2 ^ (prefixWord ++ tailWord_1141584).sum := by decide
  have hdescent : baseEnd_1141584 < baseStart_1141584 := by decide
  rcases family_descends (prefixWord ++ tailWord_1141584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1141599 : List Nat := [1, 1, 2, 3, 1, 3, 3, 2, 6]
def baseStart_1141599 : Nat := 118140960795 + 1141599 * 2 ^ 59
def prefixEnd_1141599 : Nat := 4983230072969 + 3 ^ 40 * 1141599 * 2
def baseEnd_1141599 : Nat := 130264222598263160524975

theorem tailTrace_1141599 : CollatzResearch.WordTrace tailWord_1141599 prefixEnd_1141599 130264222598263160524975 := by
  unfold tailWord_1141599
  simp only [CollatzResearch.WordTrace]
  refine ⟨41637536191189267431987851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27758357460792844954658567 41637536191189267431987851)
  ·
    refine ⟨62456304286783901147981777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41637536191189267431987851 62456304286783901147981777)
    ·
      refine ⟨46842228215087925860986333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62456304286783901147981777 46842228215087925860986333)
      ·
        refine ⟨17565835580657972197869875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46842228215087925860986333 17565835580657972197869875)
        ·
          refine ⟨26348753370986958296804813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17565835580657972197869875 26348753370986958296804813)
          ·
            refine ⟨9880782514120109361301805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26348753370986958296804813 9880782514120109361301805)
            ·
              refine ⟨3705293442795041010488177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9880782514120109361301805 3705293442795041010488177)
              ·
                refine ⟨2778970082096280757866133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3705293442795041010488177 2778970082096280757866133)
                ·
                  refine ⟨130264222598263160524975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2778970082096280757866133 130264222598263160524975)
                  ·
                    rfl

theorem cell22_1141599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 3, 2, 6].length) (baseStart_1141599 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1141599 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1141599 prefixEnd_1141599 := by exact prefixLift 1141599
  have htrace : WordTrace (prefixWord ++ tailWord_1141599) baseStart_1141599 baseEnd_1141599 := by
    simpa [prefixWord, tailWord_1141599, baseEnd_1141599] using wordTrace_append hprefix tailTrace_1141599
  have hstable : (prefixWord ++ tailWord_1141599).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1141599).length < 2 ^ (prefixWord ++ tailWord_1141599).sum := by decide
  have hdescent : baseEnd_1141599 < baseStart_1141599 := by decide
  rcases family_descends (prefixWord ++ tailWord_1141599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1141616 : List Nat := [2, 1, 1, 1, 4, 1, 3, 5, 4]
def baseStart_1141616 : Nat := 118140960795 + 1141616 * 2 ^ 59
def prefixEnd_1141616 : Nat := 4983230072969 + 3 ^ 40 * 1141616 * 2
def baseEnd_1141616 : Nat := 130266162414069034633291

theorem tailTrace_1141616 : CollatzResearch.WordTrace tailWord_1141616 prefixEnd_1141616 130266162414069034633291 := by
  unfold tailWord_1141616
  simp only [CollatzResearch.WordTrace]
  refine ⟨20819078116063839667678351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27758770821418452890237801 20819078116063839667678351)
  ·
    refine ⟨31228617174095759501517527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20819078116063839667678351 31228617174095759501517527)
    ·
      refine ⟨46842925761143639252276291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31228617174095759501517527 46842925761143639252276291)
      ·
        refine ⟨70264388641715458878414437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46842925761143639252276291 70264388641715458878414437)
        ·
          refine ⟨13174572870321648539702707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 70264388641715458878414437 13174572870321648539702707)
          ·
            refine ⟨19761859305482472809554061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13174572870321648539702707 19761859305482472809554061)
            ·
              refine ⟨7410697239555927303582773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19761859305482472809554061 7410697239555927303582773)
              ·
                refine ⟨694752866208368184710885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7410697239555927303582773 694752866208368184710885)
                ·
                  refine ⟨130266162414069034633291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 694752866208368184710885 130266162414069034633291)
                  ·
                    rfl

theorem cell22_1141616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 3, 5, 4].length) (baseStart_1141616 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1141616 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1141616 prefixEnd_1141616 := by exact prefixLift 1141616
  have htrace : WordTrace (prefixWord ++ tailWord_1141616) baseStart_1141616 baseEnd_1141616 := by
    simpa [prefixWord, tailWord_1141616, baseEnd_1141616] using wordTrace_append hprefix tailTrace_1141616
  have hstable : (prefixWord ++ tailWord_1141616).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1141616).length < 2 ^ (prefixWord ++ tailWord_1141616).sum := by decide
  have hdescent : baseEnd_1141616 < baseStart_1141616 := by decide
  rcases family_descends (prefixWord ++ tailWord_1141616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1141618 : List Nat := [3, 2, 1, 2, 1, 1, 6, 1, 1, 4]
def baseStart_1141618 : Nat := 118140960795 + 1141618 * 2 ^ 59
def prefixEnd_1141618 : Nat := 4983230072969 + 3 ^ 40 * 1141618 * 2
def baseEnd_1141618 : Nat := 390799171883079765349867

theorem tailTrace_1141618 : CollatzResearch.WordTrace tailWord_1141618 prefixEnd_1141618 390799171883079765349867 := by
  unfold tailWord_1141618
  simp only [CollatzResearch.WordTrace]
  refine ⟨10409557294530108419232377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27758819452080289117953005 10409557294530108419232377)
  ·
    refine ⟨7807167970897581314424283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10409557294530108419232377 7807167970897581314424283)
    ·
      refine ⟨11710751956346371971636425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7807167970897581314424283 11710751956346371971636425)
      ·
        refine ⟨8783063967259778978727319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11710751956346371971636425 8783063967259778978727319)
        ·
          refine ⟨13174595950889668468090979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8783063967259778978727319 13174595950889668468090979)
          ·
            refine ⟨19761893926334502702136469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13174595950889668468090979 19761893926334502702136469)
            ·
              refine ⟨926338777796929814162647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 19761893926334502702136469 926338777796929814162647)
              ·
                refine ⟨1389508166695394721243971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 926338777796929814162647 1389508166695394721243971)
                ·
                  refine ⟨2084262250043092081865957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1389508166695394721243971 2084262250043092081865957)
                  ·
                    refine ⟨390799171883079765349867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2084262250043092081865957 390799171883079765349867)
                    ·
                      rfl

theorem cell22_1141618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 6, 1, 1, 4].length) (baseStart_1141618 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1141618 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1141618 prefixEnd_1141618 := by exact prefixLift 1141618
  have htrace : WordTrace (prefixWord ++ tailWord_1141618) baseStart_1141618 baseEnd_1141618 := by
    simpa [prefixWord, tailWord_1141618, baseEnd_1141618] using wordTrace_append hprefix tailTrace_1141618
  have hstable : (prefixWord ++ tailWord_1141618).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1141618).length < 2 ^ (prefixWord ++ tailWord_1141618).sum := by decide
  have hdescent : baseEnd_1141618 < baseStart_1141618 := by decide
  rcases family_descends (prefixWord ++ tailWord_1141618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1141783 : List Nat := [1, 1, 3, 5, 1, 1, 2, 2, 1, 5]
def baseStart_1141783 : Nat := 118140960795 + 1141783 * 2 ^ 59
def prefixEnd_1141783 : Nat := 4983230072969 + 3 ^ 40 * 1141783 * 2
def baseEnd_1141783 : Nat := 390855654755074334974361

theorem tailTrace_1141783 : CollatzResearch.WordTrace tailWord_1141783 prefixEnd_1141783 390855654755074334974361 := by
  unfold tailWord_1141783
  simp only [CollatzResearch.WordTrace]
  refine ⟨41644247222522666856686003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27762831481681777904457335 41644247222522666856686003)
  ·
    refine ⟨62466370833784000285029005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41644247222522666856686003 62466370833784000285029005)
    ·
      refine ⟨23424889062669000106885877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62466370833784000285029005 23424889062669000106885877)
      ·
        refine ⟨2196083349625218760020551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 23424889062669000106885877 2196083349625218760020551)
        ·
          refine ⟨3294125024437828140030827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2196083349625218760020551 3294125024437828140030827)
          ·
            refine ⟨4941187536656742210046241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3294125024437828140030827 4941187536656742210046241)
            ·
              refine ⟨3705890652492556657534681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4941187536656742210046241 3705890652492556657534681)
              ·
                refine ⟨2779417989369417493151011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3705890652492556657534681 2779417989369417493151011)
                ·
                  refine ⟨4169126984054126239726517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2779417989369417493151011 4169126984054126239726517)
                  ·
                    refine ⟨390855654755074334974361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4169126984054126239726517 390855654755074334974361)
                    ·
                      rfl

theorem cell22_1141783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 2, 2, 1, 5].length) (baseStart_1141783 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1141783 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1141783 prefixEnd_1141783 := by exact prefixLift 1141783
  have htrace : WordTrace (prefixWord ++ tailWord_1141783) baseStart_1141783 baseEnd_1141783 := by
    simpa [prefixWord, tailWord_1141783, baseEnd_1141783] using wordTrace_append hprefix tailTrace_1141783
  have hstable : (prefixWord ++ tailWord_1141783).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1141783).length < 2 ^ (prefixWord ++ tailWord_1141783).sum := by decide
  have hdescent : baseEnd_1141783 < baseStart_1141783 := by decide
  rcases family_descends (prefixWord ++ tailWord_1141783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1141817 : List Nat := [1, 2, 1, 5, 2, 2, 3, 1, 2, 3]
def baseStart_1141817 : Nat := 118140960795 + 1141817 * 2 ^ 59
def prefixEnd_1141817 : Nat := 4983230072969 + 3 ^ 40 * 1141817 * 2
def baseEnd_1141817 : Nat := 390867293649909579624257

theorem tailTrace_1141817 : CollatzResearch.WordTrace tailWord_1141817 prefixEnd_1141817 390867293649909579624257 := by
  unfold tailWord_1141817
  simp only [CollatzResearch.WordTrace]
  refine ⟨41645487304399490663423705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27763658202932993775615803 41645487304399490663423705)
  ·
    refine ⟨31234115478299617997567779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41645487304399490663423705 31234115478299617997567779)
    ·
      refine ⟨46851173217449426996351669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31234115478299617997567779 46851173217449426996351669)
      ·
        refine ⟨4392297489135883780907969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 46851173217449426996351669 4392297489135883780907969)
        ·
          refine ⟨3294223116851912835680977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4392297489135883780907969 3294223116851912835680977)
          ·
            refine ⟨2470667337638934626760733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3294223116851912835680977 2470667337638934626760733)
            ·
              refine ⟨926500251614600485035275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2470667337638934626760733 926500251614600485035275)
              ·
                refine ⟨1389750377421900727552913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 926500251614600485035275 1389750377421900727552913)
                ·
                  refine ⟨1042312783066425545664685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1389750377421900727552913 1042312783066425545664685)
                  ·
                    refine ⟨390867293649909579624257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1042312783066425545664685 390867293649909579624257)
                    ·
                      rfl

theorem cell22_1141817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 3, 1, 2, 3].length) (baseStart_1141817 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1141817 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1141817 prefixEnd_1141817 := by exact prefixLift 1141817
  have htrace : WordTrace (prefixWord ++ tailWord_1141817) baseStart_1141817 baseEnd_1141817 := by
    simpa [prefixWord, tailWord_1141817, baseEnd_1141817] using wordTrace_append hprefix tailTrace_1141817
  have hstable : (prefixWord ++ tailWord_1141817).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1141817).length < 2 ^ (prefixWord ++ tailWord_1141817).sum := by decide
  have hdescent : baseEnd_1141817 < baseStart_1141817 := by decide
  rcases family_descends (prefixWord ++ tailWord_1141817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1141830 : List Nat := [6, 1, 1, 1, 1, 3, 1, 8]
def baseStart_1141830 : Nat := 118140960795 + 1141830 * 2 ^ 59
def prefixEnd_1141830 : Nat := 4983230072969 + 3 ^ 40 * 1141830 * 2
def baseEnd_1141830 : Nat := 43430193757286875449913

theorem tailTrace_1141830 : CollatzResearch.WordTrace tailWord_1141830 prefixEnd_1141830 43430193757286875449913 := by
  unfold tailWord_1141830
  simp only [CollatzResearch.WordTrace]
  refine ⟨1301436295417262308863967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 27763974302234929255764629 1301436295417262308863967)
  ·
    refine ⟨1952154443125893463295951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1301436295417262308863967 1952154443125893463295951)
    ·
      refine ⟨2928231664688840194943927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1952154443125893463295951 2928231664688840194943927)
      ·
        refine ⟨4392347497033260292415891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2928231664688840194943927 4392347497033260292415891)
        ·
          refine ⟨6588521245549890438623837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4392347497033260292415891 6588521245549890438623837)
          ·
            refine ⟨2470695467081208914483939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6588521245549890438623837 2470695467081208914483939)
            ·
              refine ⟨3706043200621813371725909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2470695467081208914483939 3706043200621813371725909)
              ·
                refine ⟨43430193757286875449913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3706043200621813371725909 43430193757286875449913)
                ·
                  rfl

theorem cell22_1141830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 1, 8].length) (baseStart_1141830 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1141830 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1141830 prefixEnd_1141830 := by exact prefixLift 1141830
  have htrace : WordTrace (prefixWord ++ tailWord_1141830) baseStart_1141830 baseEnd_1141830 := by
    simpa [prefixWord, tailWord_1141830, baseEnd_1141830] using wordTrace_append hprefix tailTrace_1141830
  have hstable : (prefixWord ++ tailWord_1141830).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1141830).length < 2 ^ (prefixWord ++ tailWord_1141830).sum := by decide
  have hdescent : baseEnd_1141830 < baseStart_1141830 := by decide
  rcases family_descends (prefixWord ++ tailWord_1141830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1141841 : List Nat := [1, 2, 2, 1, 3, 1, 3, 2, 7]
def baseStart_1141841 : Nat := 118140960795 + 1141841 * 2 ^ 59
def prefixEnd_1141841 : Nat := 4983230072969 + 3 ^ 40 * 1141841 * 2
def baseEnd_1141841 : Nat := 130291836446793839008061

theorem tailTrace_1141841 : CollatzResearch.WordTrace tailWord_1141841 prefixEnd_1141841 130291836446793839008061 := by
  unfold tailWord_1141841
  simp only [CollatzResearch.WordTrace]
  refine ⟨41646362656312542762297377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27764241770875028508198251 41646362656312542762297377)
  ·
    refine ⟨31234771992234407071723033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41646362656312542762297377 31234771992234407071723033)
    ·
      refine ⟨23426078994175805303792275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31234771992234407071723033 23426078994175805303792275)
      ·
        refine ⟨35139118491263707955688413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23426078994175805303792275 35139118491263707955688413)
        ·
          refine ⟨13177169434223890483383155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35139118491263707955688413 13177169434223890483383155)
          ·
            refine ⟨19765754151335835725074733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13177169434223890483383155 19765754151335835725074733)
            ·
              refine ⟨7412157806750938396903025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19765754151335835725074733 7412157806750938396903025)
              ·
                refine ⟨5559118355063203797677269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7412157806750938396903025 5559118355063203797677269)
                ·
                  refine ⟨130291836446793839008061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5559118355063203797677269 130291836446793839008061)
                  ·
                    rfl

theorem cell22_1141841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 3, 2, 7].length) (baseStart_1141841 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1141841 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1141841 prefixEnd_1141841 := by exact prefixLift 1141841
  have htrace : WordTrace (prefixWord ++ tailWord_1141841) baseStart_1141841 baseEnd_1141841 := by
    simpa [prefixWord, tailWord_1141841, baseEnd_1141841] using wordTrace_append hprefix tailTrace_1141841
  have hstable : (prefixWord ++ tailWord_1141841).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1141841).length < 2 ^ (prefixWord ++ tailWord_1141841).sum := by decide
  have hdescent : baseEnd_1141841 < baseStart_1141841 := by decide
  rcases family_descends (prefixWord ++ tailWord_1141841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1141920 : List Nat := [2, 1, 1, 4, 2, 1, 3, 4, 4]
def baseStart_1141920 : Nat := 118140960795 + 1141920 * 2 ^ 59
def prefixEnd_1141920 : Nat := 4983230072969 + 3 ^ 40 * 1141920 * 2
def baseEnd_1141920 : Nat := 130300850884950548099647

theorem tailTrace_1141920 : CollatzResearch.WordTrace tailWord_1141920 prefixEnd_1141920 130300850884950548099647 := by
  unfold tailWord_1141920
  simp only [CollatzResearch.WordTrace]
  refine ⟨20824622011513169627211607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27766162682017559502948809 20824622011513169627211607)
  ·
    refine ⟨31236933017269754440817411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20824622011513169627211607 31236933017269754440817411)
    ·
      refine ⟨46855399525904631661226117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31236933017269754440817411 46855399525904631661226117)
      ·
        refine ⟨8785387411107118436479897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 46855399525904631661226117 8785387411107118436479897)
        ·
          refine ⟨6589040558330338827359923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8785387411107118436479897 6589040558330338827359923)
          ·
            refine ⟨9883560837495508241039885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6589040558330338827359923 9883560837495508241039885)
            ·
              refine ⟨3706335314060815590389957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9883560837495508241039885 3706335314060815590389957)
              ·
                refine ⟨694937871386402923198117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3706335314060815590389957 694937871386402923198117)
                ·
                  refine ⟨130300850884950548099647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 694937871386402923198117 130300850884950548099647)
                  ·
                    rfl

theorem cell22_1141920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 3, 4, 4].length) (baseStart_1141920 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1141920 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1141920 prefixEnd_1141920 := by exact prefixLift 1141920
  have htrace : WordTrace (prefixWord ++ tailWord_1141920) baseStart_1141920 baseEnd_1141920 := by
    simpa [prefixWord, tailWord_1141920, baseEnd_1141920] using wordTrace_append hprefix tailTrace_1141920
  have hstable : (prefixWord ++ tailWord_1141920).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1141920).length < 2 ^ (prefixWord ++ tailWord_1141920).sum := by decide
  have hdescent : baseEnd_1141920 < baseStart_1141920 := by decide
  rcases family_descends (prefixWord ++ tailWord_1141920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1141935 : List Nat := [1, 1, 2, 1, 2, 3, 4, 3, 2, 3]
def baseStart_1141935 : Nat := 118140960795 + 1141935 * 2 ^ 59
def prefixEnd_1141935 : Nat := 4983230072969 + 3 ^ 40 * 1141935 * 2
def baseEnd_1141935 : Nat := 390907687461396605173895

theorem tailTrace_1141935 : CollatzResearch.WordTrace tailWord_1141935 prefixEnd_1141935 390907687461396605173895 := by
  unfold tailWord_1141935
  simp only [CollatzResearch.WordTrace]
  refine ⟨41649791117971996816219259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27766527411981331210812839 41649791117971996816219259)
  ·
    refine ⟨62474686676957995224328889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41649791117971996816219259 62474686676957995224328889)
    ·
      refine ⟨46856015007718496418246667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62474686676957995224328889 46856015007718496418246667)
      ·
        refine ⟨70284022511577744627370001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46856015007718496418246667 70284022511577744627370001)
        ·
          refine ⟨52713016883683308470527501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70284022511577744627370001 52713016883683308470527501)
          ·
            refine ⟨19767381331381240676447813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52713016883683308470527501 19767381331381240676447813)
            ·
              refine ⟨3706383999633982626833965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19767381331381240676447813 3706383999633982626833965)
              ·
                refine ⟨1389893999862743485062737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3706383999633982626833965 1389893999862743485062737)
                ·
                  refine ⟨1042420499897057613797053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1389893999862743485062737 1042420499897057613797053)
                  ·
                    refine ⟨390907687461396605173895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1042420499897057613797053 390907687461396605173895)
                    ·
                      rfl

theorem cell22_1141935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 4, 3, 2, 3].length) (baseStart_1141935 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1141935 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1141935 prefixEnd_1141935 := by exact prefixLift 1141935
  have htrace : WordTrace (prefixWord ++ tailWord_1141935) baseStart_1141935 baseEnd_1141935 := by
    simpa [prefixWord, tailWord_1141935, baseEnd_1141935] using wordTrace_append hprefix tailTrace_1141935
  have hstable : (prefixWord ++ tailWord_1141935).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1141935).length < 2 ^ (prefixWord ++ tailWord_1141935).sum := by decide
  have hdescent : baseEnd_1141935 < baseStart_1141935 := by decide
  rcases family_descends (prefixWord ++ tailWord_1141935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1141950 : List Nat := [4, 2, 1, 1, 3, 2, 1, 1, 1, 6]
def baseStart_1141950 : Nat := 118140960795 + 1141950 * 2 ^ 59
def prefixEnd_1141950 : Nat := 4983230072969 + 3 ^ 40 * 1141950 * 2
def baseEnd_1141950 : Nat := 390912822267941566048849

theorem tailTrace_1141950 : CollatzResearch.WordTrace tailWord_1141950 prefixEnd_1141950 390912822267941566048849 := by
  unfold tailWord_1141950
  simp only [CollatzResearch.WordTrace]
  refine ⟨5206292276614706797251913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27766892141945102918676869 5206292276614706797251913)
  ·
    refine ⟨3904719207461030097938935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5206292276614706797251913 3904719207461030097938935)
    ·
      refine ⟨5857078811191545146908403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3904719207461030097938935 5857078811191545146908403)
      ·
        refine ⟨8785618216787317720362605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5857078811191545146908403 8785618216787317720362605)
        ·
          refine ⟨3294606831295244145135977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8785618216787317720362605 3294606831295244145135977)
          ·
            refine ⟨2470955123471433108851983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3294606831295244145135977 2470955123471433108851983)
            ·
              refine ⟨3706432685207149663277975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2470955123471433108851983 3706432685207149663277975)
              ·
                refine ⟨5559649027810724494916963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3706432685207149663277975 5559649027810724494916963)
                ·
                  refine ⟨8339473541716086742375445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5559649027810724494916963 8339473541716086742375445)
                  ·
                    refine ⟨390912822267941566048849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8339473541716086742375445 390912822267941566048849)
                    ·
                      rfl

theorem cell22_1141950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 1, 1, 1, 6].length) (baseStart_1141950 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1141950 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1141950 prefixEnd_1141950 := by exact prefixLift 1141950
  have htrace : WordTrace (prefixWord ++ tailWord_1141950) baseStart_1141950 baseEnd_1141950 := by
    simpa [prefixWord, tailWord_1141950, baseEnd_1141950] using wordTrace_append hprefix tailTrace_1141950
  have hstable : (prefixWord ++ tailWord_1141950).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1141950).length < 2 ^ (prefixWord ++ tailWord_1141950).sum := by decide
  have hdescent : baseEnd_1141950 < baseStart_1141950 := by decide
  rcases family_descends (prefixWord ++ tailWord_1141950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1141956 : List Nat := [2, 3, 3, 1, 4, 1, 2, 1, 1, 4]
def baseStart_1141956 : Nat := 118140960795 + 1141956 * 2 ^ 59
def prefixEnd_1141956 : Nat := 4983230072969 + 3 ^ 40 * 1141956 * 2
def baseEnd_1141956 : Nat := 390914876190559550398831

theorem tailTrace_1141956 : CollatzResearch.WordTrace tailWord_1141956 prefixEnd_1141956 390914876190559550398831 := by
  unfold tailWord_1141956
  simp only [CollatzResearch.WordTrace]
  refine ⟨20825278525447958701366861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27767038033930611601822481 20825278525447958701366861)
  ·
    refine ⟨7809479447042984513012573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20825278525447958701366861 7809479447042984513012573)
    ·
      refine ⟨2928554792641119192379715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7809479447042984513012573 2928554792641119192379715)
      ·
        refine ⟨4392832188961678788569573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2928554792641119192379715 4392832188961678788569573)
        ·
          refine ⟨823656035430314772856795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4392832188961678788569573 823656035430314772856795)
          ·
            refine ⟨1235484053145472159285193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 823656035430314772856795 1235484053145472159285193)
            ·
              refine ⟨926613039859104119463895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1235484053145472159285193 926613039859104119463895)
              ·
                refine ⟨1389919559788656179195843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 926613039859104119463895 1389919559788656179195843)
                ·
                  refine ⟨2084879339682984268793765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1389919559788656179195843 2084879339682984268793765)
                  ·
                    refine ⟨390914876190559550398831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2084879339682984268793765 390914876190559550398831)
                    ·
                      rfl

theorem cell22_1141956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 4, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 4, 1, 2, 1, 1, 4].length) (baseStart_1141956 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1141956 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1141956 prefixEnd_1141956 := by exact prefixLift 1141956
  have htrace : WordTrace (prefixWord ++ tailWord_1141956) baseStart_1141956 baseEnd_1141956 := by
    simpa [prefixWord, tailWord_1141956, baseEnd_1141956] using wordTrace_append hprefix tailTrace_1141956
  have hstable : (prefixWord ++ tailWord_1141956).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1141956).length < 2 ^ (prefixWord ++ tailWord_1141956).sum := by decide
  have hdescent : baseEnd_1141956 < baseStart_1141956 := by decide
  rcases family_descends (prefixWord ++ tailWord_1141956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1141997 : List Nat := [1, 5, 1, 2, 2, 1, 2, 2, 3, 3]
def baseStart_1141997 : Nat := 118140960795 + 1141997 * 2 ^ 59
def prefixEnd_1141997 : Nat := 4983230072969 + 3 ^ 40 * 1141997 * 2
def baseEnd_1141997 : Nat := 390928911328449110123705

theorem tailTrace_1141997 : CollatzResearch.WordTrace tailWord_1141997 prefixEnd_1141997 390928911328449110123705 := by
  unfold tailWord_1141997
  simp only [CollatzResearch.WordTrace]
  refine ⟨41652052443747381404976245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27768034962498254269984163 41652052443747381404976245)
  ·
    refine ⟨3904879916601317006716523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 41652052443747381404976245 3904879916601317006716523)
    ·
      refine ⟨5857319874901975510074785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3904879916601317006716523 5857319874901975510074785)
      ·
        refine ⟨4392989906176481632556089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5857319874901975510074785 4392989906176481632556089)
        ·
          refine ⟨3294742429632361224417067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4392989906176481632556089 3294742429632361224417067)
          ·
            refine ⟨4942113644448541836625601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3294742429632361224417067 4942113644448541836625601)
            ·
              refine ⟨3706585233336406377469201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4942113644448541836625601 3706585233336406377469201)
              ·
                refine ⟨2779938925002304783101901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3706585233336406377469201 2779938925002304783101901)
                ·
                  refine ⟨1042477096875864293663213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2779938925002304783101901 1042477096875864293663213)
                  ·
                    refine ⟨390928911328449110123705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1042477096875864293663213 390928911328449110123705)
                    ·
                      rfl

theorem cell22_1141997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 2, 2, 3, 3].length) (baseStart_1141997 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1141997 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1141997 prefixEnd_1141997 := by exact prefixLift 1141997
  have htrace : WordTrace (prefixWord ++ tailWord_1141997) baseStart_1141997 baseEnd_1141997 := by
    simpa [prefixWord, tailWord_1141997, baseEnd_1141997] using wordTrace_append hprefix tailTrace_1141997
  have hstable : (prefixWord ++ tailWord_1141997).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1141997).length < 2 ^ (prefixWord ++ tailWord_1141997).sum := by decide
  have hdescent : baseEnd_1141997 < baseStart_1141997 := by decide
  rcases family_descends (prefixWord ++ tailWord_1141997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1142087 : List Nat := [1, 1, 4, 1, 2, 3, 1, 4, 2, 3]
def baseStart_1142087 : Nat := 118140960795 + 1142087 * 2 ^ 59
def prefixEnd_1142087 : Nat := 4983230072969 + 3 ^ 40 * 1142087 * 2
def baseEnd_1142087 : Nat := 390959720167718875373429

theorem tailTrace_1142087 : CollatzResearch.WordTrace tailWord_1142087 prefixEnd_1142087 390959720167718875373429 := by
  unfold tailWord_1142087
  simp only [CollatzResearch.WordTrace]
  refine ⟨41655335013421326775752515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27770223342280884517168343 41655335013421326775752515)
  ·
    refine ⟨62483002520131990163628773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41655335013421326775752515 62483002520131990163628773)
    ·
      refine ⟨11715562972524748155680395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 62483002520131990163628773 11715562972524748155680395)
      ·
        refine ⟨17573344458787122233520593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11715562972524748155680395 17573344458787122233520593)
        ·
          refine ⟨13180008344090341675140445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17573344458787122233520593 13180008344090341675140445)
          ·
            refine ⟨4942503129033878128177667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13180008344090341675140445 4942503129033878128177667)
            ·
              refine ⟨7413754693550817192266501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4942503129033878128177667 7413754693550817192266501)
              ·
                refine ⟨1390079005040778223549969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7413754693550817192266501 1390079005040778223549969)
                ·
                  refine ⟨1042559253780583667662477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1390079005040778223549969 1042559253780583667662477)
                  ·
                    refine ⟨390959720167718875373429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1042559253780583667662477 390959720167718875373429)
                    ·
                      rfl

theorem cell22_1142087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 1, 4, 2, 3].length) (baseStart_1142087 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1142087 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1142087 prefixEnd_1142087 := by exact prefixLift 1142087
  have htrace : WordTrace (prefixWord ++ tailWord_1142087) baseStart_1142087 baseEnd_1142087 := by
    simpa [prefixWord, tailWord_1142087, baseEnd_1142087] using wordTrace_append hprefix tailTrace_1142087
  have hstable : (prefixWord ++ tailWord_1142087).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1142087).length < 2 ^ (prefixWord ++ tailWord_1142087).sum := by decide
  have hdescent : baseEnd_1142087 < baseStart_1142087 := by decide
  rcases family_descends (prefixWord ++ tailWord_1142087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1142119 : List Nat := [1, 1, 5, 1, 4, 2, 1, 1, 2, 4]
def baseStart_1142119 : Nat := 118140960795 + 1142119 * 2 ^ 59
def prefixEnd_1142119 : Nat := 4983230072969 + 3 ^ 40 * 1142119 * 2
def baseEnd_1142119 : Nat := 390970674421681458573331

theorem tailTrace_1142119 : CollatzResearch.WordTrace tailWord_1142119 prefixEnd_1142119 390970674421681458573331 := by
  unfold tailWord_1142119
  simp only [CollatzResearch.WordTrace]
  refine ⟨41656502149305396240917411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27771001432870264160611607 41656502149305396240917411)
  ·
    refine ⟨62484753223958094361376117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41656502149305396240917411 62484753223958094361376117)
    ·
      refine ⟨5857945614746071346379011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 62484753223958094361376117 5857945614746071346379011)
      ·
        refine ⟨8786918422119107019568517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5857945614746071346379011 8786918422119107019568517)
        ·
          refine ⟨1647547204147332566169097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8786918422119107019568517 1647547204147332566169097)
          ·
            refine ⟨1235660403110499424626823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1647547204147332566169097 1235660403110499424626823)
            ·
              refine ⟨1853490604665749136940235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1235660403110499424626823 1853490604665749136940235)
              ·
                refine ⟨2780235906998623705410353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1853490604665749136940235 2780235906998623705410353)
                ·
                  refine ⟨2085176930248967779057765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2780235906998623705410353 2085176930248967779057765)
                  ·
                    refine ⟨390970674421681458573331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2085176930248967779057765 390970674421681458573331)
                    ·
                      rfl

theorem cell22_1142119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 2, 1, 1, 2, 4].length) (baseStart_1142119 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1142119 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1142119 prefixEnd_1142119 := by exact prefixLift 1142119
  have htrace : WordTrace (prefixWord ++ tailWord_1142119) baseStart_1142119 baseEnd_1142119 := by
    simpa [prefixWord, tailWord_1142119, baseEnd_1142119] using wordTrace_append hprefix tailTrace_1142119
  have hstable : (prefixWord ++ tailWord_1142119).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1142119).length < 2 ^ (prefixWord ++ tailWord_1142119).sum := by decide
  have hdescent : baseEnd_1142119 < baseStart_1142119 := by decide
  rcases family_descends (prefixWord ++ tailWord_1142119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1142149 : List Nat := [1, 3, 1, 1, 3, 1, 4, 4, 1, 3]
def baseStart_1142149 : Nat := 118140960795 + 1142149 * 2 ^ 59
def prefixEnd_1142149 : Nat := 4983230072969 + 3 ^ 40 * 1142149 * 2
def baseEnd_1142149 : Nat := 390980944034771380323239

theorem tailTrace_1142149 : CollatzResearch.WordTrace tailWord_1142149 prefixEnd_1142149 390980944034771380323239 := by
  unfold tailWord_1142149
  simp only [CollatzResearch.WordTrace]
  refine ⟨41657596339196711364509501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27771730892797807576339667 41657596339196711364509501)
  ·
    refine ⟨15621598627198766761691063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41657596339196711364509501 15621598627198766761691063)
    ·
      refine ⟨23432397940798150142536595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15621598627198766761691063 23432397940798150142536595)
      ·
        refine ⟨35148596911197225213804893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23432397940798150142536595 35148596911197225213804893)
        ·
          refine ⟨13180723841698959455176835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35148596911197225213804893 13180723841698959455176835)
          ·
            refine ⟨19771085762548439182765253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13180723841698959455176835 19771085762548439182765253)
            ·
              refine ⟨3707078580477832346768485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19771085762548439182765253 3707078580477832346768485)
              ·
                refine ⟨695077233839593565019091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3707078580477832346768485 695077233839593565019091)
                ·
                  refine ⟨1042615850759390347528637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 695077233839593565019091 1042615850759390347528637)
                  ·
                    refine ⟨390980944034771380323239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1042615850759390347528637 390980944034771380323239)
                    ·
                      rfl

theorem cell22_1142149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 4, 4, 1, 3].length) (baseStart_1142149 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1142149 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1142149 prefixEnd_1142149 := by exact prefixLift 1142149
  have htrace : WordTrace (prefixWord ++ tailWord_1142149) baseStart_1142149 baseEnd_1142149 := by
    simpa [prefixWord, tailWord_1142149, baseEnd_1142149] using wordTrace_append hprefix tailTrace_1142149
  have hstable : (prefixWord ++ tailWord_1142149).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1142149).length < 2 ^ (prefixWord ++ tailWord_1142149).sum := by decide
  have hdescent : baseEnd_1142149 < baseStart_1142149 := by decide
  rcases family_descends (prefixWord ++ tailWord_1142149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1142207 : List Nat := [1, 1, 2, 2, 2, 1, 1, 8, 4]
def baseStart_1142207 : Nat := 118140960795 + 1142207 * 2 ^ 59
def prefixEnd_1142207 : Nat := 4983230072969 + 3 ^ 40 * 1142207 * 2
def baseEnd_1142207 : Nat := 130333599540026187457687

theorem tailTrace_1142207 : CollatzResearch.WordTrace tailWord_1142207 prefixEnd_1142207 130333599540026187457687 := by
  unfold tailWord_1142207
  simp only [CollatzResearch.WordTrace]
  refine ⟨41659711772986587270120875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27773141181991058180080583 41659711772986587270120875)
  ·
    refine ⟨62489567659479880905181313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41659711772986587270120875 62489567659479880905181313)
    ·
      refine ⟨46867175744609910678885985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62489567659479880905181313 46867175744609910678885985)
      ·
        refine ⟨35150381808457433009164489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46867175744609910678885985 35150381808457433009164489)
        ·
          refine ⟨26362786356343074756873367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35150381808457433009164489 26362786356343074756873367)
          ·
            refine ⟨39544179534514612135310051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26362786356343074756873367 39544179534514612135310051)
            ·
              refine ⟨59316269301771918202965077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39544179534514612135310051 59316269301771918202965077)
              ·
                refine ⟨695112530880139666440997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 59316269301771918202965077 695112530880139666440997)
                ·
                  refine ⟨130333599540026187457687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 695112530880139666440997 130333599540026187457687)
                  ·
                    rfl

theorem cell22_1142207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 8, 4].length) (baseStart_1142207 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1142207 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1142207 prefixEnd_1142207 := by exact prefixLift 1142207
  have htrace : WordTrace (prefixWord ++ tailWord_1142207) baseStart_1142207 baseEnd_1142207 := by
    simpa [prefixWord, tailWord_1142207, baseEnd_1142207] using wordTrace_append hprefix tailTrace_1142207
  have hstable : (prefixWord ++ tailWord_1142207).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1142207).length < 2 ^ (prefixWord ++ tailWord_1142207).sum := by decide
  have hdescent : baseEnd_1142207 < baseStart_1142207 := by decide
  rcases family_descends (prefixWord ++ tailWord_1142207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1142258 : List Nat := [3, 2, 1, 4, 1, 3, 2, 2, 4]
def baseStart_1142258 : Nat := 118140960795 + 1142258 * 2 ^ 59
def prefixEnd_1142258 : Nat := 4983230072969 + 3 ^ 40 * 1142258 * 2
def baseEnd_1142258 : Nat := 130339418987443809782635

theorem tailTrace_1142258 : CollatzResearch.WordTrace tailWord_1142258 prefixEnd_1142258 130339418987443809782635 := by
  unfold tailWord_1142258
  simp only [CollatzResearch.WordTrace]
  refine ⟨10415392973950455745056857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27774381263867881986818285 10415392973950455745056857)
  ·
    refine ⟨7811544730462841808792643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10415392973950455745056857 7811544730462841808792643)
    ·
      refine ⟨11717317095694262713188965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7811544730462841808792643 11717317095694262713188965)
      ·
        refine ⟨2196996955442674258722931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11717317095694262713188965 2196996955442674258722931)
        ·
          refine ⟨3295495433164011388084397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2196996955442674258722931 3295495433164011388084397)
          ·
            refine ⟨1235810787436504270531649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3295495433164011388084397 1235810787436504270531649)
            ·
              refine ⟨926858090577378202898737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1235810787436504270531649 926858090577378202898737)
              ·
                refine ⟨695143567933033652174053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 926858090577378202898737 695143567933033652174053)
                ·
                  refine ⟨130339418987443809782635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 695143567933033652174053 130339418987443809782635)
                  ·
                    rfl

theorem cell22_1142258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 3, 2, 2, 4].length) (baseStart_1142258 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1142258 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1142258 prefixEnd_1142258 := by exact prefixLift 1142258
  have htrace : WordTrace (prefixWord ++ tailWord_1142258) baseStart_1142258 baseEnd_1142258 := by
    simpa [prefixWord, tailWord_1142258, baseEnd_1142258] using wordTrace_append hprefix tailTrace_1142258
  have hstable : (prefixWord ++ tailWord_1142258).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1142258).length < 2 ^ (prefixWord ++ tailWord_1142258).sum := by decide
  have hdescent : baseEnd_1142258 < baseStart_1142258 := by decide
  rcases family_descends (prefixWord ++ tailWord_1142258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1142318 : List Nat := [4, 1, 3, 1, 2, 1, 2, 4, 1, 3]
def baseStart_1142318 : Nat := 118140960795 + 1142318 * 2 ^ 59
def prefixEnd_1142318 : Nat := 4983230072969 + 3 ^ 40 * 1142318 * 2
def baseEnd_1142318 : Nat := 391038796188511272847721

theorem tailTrace_1142318 : CollatzResearch.WordTrace tailWord_1142318 prefixEnd_1142318 391038796188511272847721 := by
  unfold tailWord_1142318
  simp only [CollatzResearch.WordTrace]
  refine ⟨5207970034448056653426451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27775840183722968818274405 5207970034448056653426451)
  ·
    refine ⟨7811955051672084980139677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5207970034448056653426451 7811955051672084980139677)
    ·
      refine ⟨2929483144377031867552379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7811955051672084980139677 2929483144377031867552379)
      ·
        refine ⟨4394224716565547801328569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2929483144377031867552379 4394224716565547801328569)
        ·
          refine ⟨3295668537424160850996427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4394224716565547801328569 3295668537424160850996427)
          ·
            refine ⟨4943502806136241276494641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3295668537424160850996427 4943502806136241276494641)
            ·
              refine ⟨3707627104602180957370981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4943502806136241276494641 3707627104602180957370981)
              ·
                refine ⟨695180082112908929507059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3707627104602180957370981 695180082112908929507059)
                ·
                  refine ⟨1042770123169363394260589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 695180082112908929507059 1042770123169363394260589)
                  ·
                    refine ⟨391038796188511272847721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1042770123169363394260589 391038796188511272847721)
                    ·
                      rfl

theorem cell22_1142318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 2, 4, 1, 3].length) (baseStart_1142318 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1142318 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1142318 prefixEnd_1142318 := by exact prefixLift 1142318
  have htrace : WordTrace (prefixWord ++ tailWord_1142318) baseStart_1142318 baseEnd_1142318 := by
    simpa [prefixWord, tailWord_1142318, baseEnd_1142318] using wordTrace_append hprefix tailTrace_1142318
  have hstable : (prefixWord ++ tailWord_1142318).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1142318).length < 2 ^ (prefixWord ++ tailWord_1142318).sum := by decide
  have hdescent : baseEnd_1142318 < baseStart_1142318 := by decide
  rcases family_descends (prefixWord ++ tailWord_1142318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1142357 : List Nat := [1, 3, 2, 2, 1, 1, 1, 3, 3, 5]
def baseStart_1142357 : Nat := 118140960795 + 1142357 * 2 ^ 59
def prefixEnd_1142357 : Nat := 4983230072969 + 3 ^ 40 * 1142357 * 2
def baseEnd_1142357 : Nat := 391052146685528171122601

theorem tailTrace_1142357 : CollatzResearch.WordTrace tailWord_1142357 prefixEnd_1142357 391052146685528171122601 := by
  unfold tailWord_1142357
  simp only [CollatzResearch.WordTrace]
  refine ⟨41665182722443162888081325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27776788481628775258720883 41665182722443162888081325)
  ·
    refine ⟨15624443520916186083030497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41665182722443162888081325 15624443520916186083030497)
    ·
      refine ⟨11718332640687139562272873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15624443520916186083030497 11718332640687139562272873)
      ·
        refine ⟨8788749480515354671704655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11718332640687139562272873 8788749480515354671704655)
        ·
          refine ⟨13183124220773032007556983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8788749480515354671704655 13183124220773032007556983)
          ·
            refine ⟨19774686331159548011335475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13183124220773032007556983 19774686331159548011335475)
            ·
              refine ⟨29662029496739322017003213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19774686331159548011335475 29662029496739322017003213)
              ·
                refine ⟨11123261061277245756376205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29662029496739322017003213 11123261061277245756376205)
                ·
                  refine ⟨4171222897978967158641077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11123261061277245756376205 4171222897978967158641077)
                  ·
                    refine ⟨391052146685528171122601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4171222897978967158641077 391052146685528171122601)
                    ·
                      rfl

theorem cell22_1142357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 3, 3, 5].length) (baseStart_1142357 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1142357 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1142357 prefixEnd_1142357 := by exact prefixLift 1142357
  have htrace : WordTrace (prefixWord ++ tailWord_1142357) baseStart_1142357 baseEnd_1142357 := by
    simpa [prefixWord, tailWord_1142357, baseEnd_1142357] using wordTrace_append hprefix tailTrace_1142357
  have hstable : (prefixWord ++ tailWord_1142357).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1142357).length < 2 ^ (prefixWord ++ tailWord_1142357).sum := by decide
  have hdescent : baseEnd_1142357 < baseStart_1142357 := by decide
  rcases family_descends (prefixWord ++ tailWord_1142357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1142376 : List Nat := [2, 1, 4, 3, 1, 3, 1, 1, 6]
def baseStart_1142376 : Nat := 118140960795 + 1142376 * 2 ^ 59
def prefixEnd_1142376 : Nat := 4983230072969 + 3 ^ 40 * 1142376 * 2
def baseEnd_1142376 : Nat := 130352883591272818299181

theorem tailTrace_1142376 : CollatzResearch.WordTrace tailWord_1142376 prefixEnd_1142376 130352883591272818299181 := by
  unfold tailWord_1142376
  simp only [CollatzResearch.WordTrace]
  refine ⟨20832937854687164566511491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27777250472916219422015321 20832937854687164566511491)
  ·
    refine ⟨31249406782030746849767237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20832937854687164566511491 31249406782030746849767237)
    ·
      refine ⟨5859263771630765034331357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31249406782030746849767237 5859263771630765034331357)
      ·
        refine ⟨2197223914361536887874259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5859263771630765034331357 2197223914361536887874259)
        ·
          refine ⟨3295835871542305331811389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2197223914361536887874259 3295835871542305331811389)
          ·
            refine ⟨1235938451828364499429271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3295835871542305331811389 1235938451828364499429271)
            ·
              refine ⟨1853907677742546749143907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1235938451828364499429271 1853907677742546749143907)
              ·
                refine ⟨2780861516613820123715861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1853907677742546749143907 2780861516613820123715861)
                ·
                  refine ⟨130352883591272818299181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2780861516613820123715861 130352883591272818299181)
                  ·
                    rfl

theorem cell22_1142376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 3, 1, 1, 6].length) (baseStart_1142376 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1142376 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1142376 prefixEnd_1142376 := by exact prefixLift 1142376
  have htrace : WordTrace (prefixWord ++ tailWord_1142376) baseStart_1142376 baseEnd_1142376 := by
    simpa [prefixWord, tailWord_1142376, baseEnd_1142376] using wordTrace_append hprefix tailTrace_1142376
  have hstable : (prefixWord ++ tailWord_1142376).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1142376).length < 2 ^ (prefixWord ++ tailWord_1142376).sum := by decide
  have hdescent : baseEnd_1142376 < baseStart_1142376 := by decide
  rcases family_descends (prefixWord ++ tailWord_1142376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1142453 : List Nat := [1, 3, 3, 3, 2, 1, 1, 2, 3, 3]
def baseStart_1142453 : Nat := 118140960795 + 1142453 * 2 ^ 59
def prefixEnd_1142453 : Nat := 4983230072969 + 3 ^ 40 * 1142453 * 2
def baseEnd_1142453 : Nat := 391085009447415920722307

theorem tailTrace_1142453 : CollatzResearch.WordTrace tailWord_1142453 prefixEnd_1142453 391085009447415920722307 := by
  unfold tailWord_1142453
  simp only [CollatzResearch.WordTrace]
  refine ⟨41668684130095371283576013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27779122753396914189050675 41668684130095371283576013)
  ·
    refine ⟨15625756548785764231341005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41668684130095371283576013 15625756548785764231341005)
    ·
      refine ⟨5859658705794661586752877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15625756548785764231341005 5859658705794661586752877)
      ·
        refine ⟨2197372014672998095032329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5859658705794661586752877 2197372014672998095032329)
        ·
          refine ⟨1648029011004748571274247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2197372014672998095032329 1648029011004748571274247)
          ·
            refine ⟨2472043516507122856911371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1648029011004748571274247 2472043516507122856911371)
            ·
              refine ⟨3708065274760684285367057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2472043516507122856911371 3708065274760684285367057)
              ·
                refine ⟨2781048956070513214025293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3708065274760684285367057 2781048956070513214025293)
                ·
                  refine ⟨1042893358526442455259485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2781048956070513214025293 1042893358526442455259485)
                  ·
                    refine ⟨391085009447415920722307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1042893358526442455259485 391085009447415920722307)
                    ·
                      rfl

theorem cell22_1142453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 1, 2, 3, 3].length) (baseStart_1142453 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1142453 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1142453 prefixEnd_1142453 := by exact prefixLift 1142453
  have htrace : WordTrace (prefixWord ++ tailWord_1142453) baseStart_1142453 baseEnd_1142453 := by
    simpa [prefixWord, tailWord_1142453, baseEnd_1142453] using wordTrace_append hprefix tailTrace_1142453
  have hstable : (prefixWord ++ tailWord_1142453).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1142453).length < 2 ^ (prefixWord ++ tailWord_1142453).sum := by decide
  have hdescent : baseEnd_1142453 < baseStart_1142453 := by decide
  rcases family_descends (prefixWord ++ tailWord_1142453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1142524 : List Nat := [2, 2, 2, 1, 3, 1, 1, 3, 1, 6]
def baseStart_1142524 : Nat := 118140960795 + 1142524 * 2 ^ 59
def prefixEnd_1142524 : Nat := 4983230072969 + 3 ^ 40 * 1142524 * 2
def baseEnd_1142524 : Nat := 391109314198395402197089

theorem tailTrace_1142524 : CollatzResearch.WordTrace tailWord_1142524 prefixEnd_1142524 391109314198395402197089 := by
  unfold tailWord_1142524
  simp only [CollatzResearch.WordTrace]
  refine ⟨20835636856419075204705313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27780849141892100272940417 20835636856419075204705313)
  ·
    refine ⟨15626727642314306403528985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20835636856419075204705313 15626727642314306403528985)
    ·
      refine ⟨11720045731735729802646739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15626727642314306403528985 11720045731735729802646739)
      ·
        refine ⟨17580068597603594703970109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11720045731735729802646739 17580068597603594703970109)
        ·
          refine ⟨6592525724101348013988791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17580068597603594703970109 6592525724101348013988791)
          ·
            refine ⟨9888788586152022020983187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6592525724101348013988791 9888788586152022020983187)
            ·
              refine ⟨14833182879228033031474781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9888788586152022020983187 14833182879228033031474781)
              ·
                refine ⟨5562443579710512386803043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14833182879228033031474781 5562443579710512386803043)
                ·
                  refine ⟨8343665369565768580204565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5562443579710512386803043 8343665369565768580204565)
                  ·
                    refine ⟨391109314198395402197089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8343665369565768580204565 391109314198395402197089)
                    ·
                      rfl

theorem cell22_1142524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 3, 1, 6].length) (baseStart_1142524 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1142524 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1142524 prefixEnd_1142524 := by exact prefixLift 1142524
  have htrace : WordTrace (prefixWord ++ tailWord_1142524) baseStart_1142524 baseEnd_1142524 := by
    simpa [prefixWord, tailWord_1142524, baseEnd_1142524] using wordTrace_append hprefix tailTrace_1142524
  have hstable : (prefixWord ++ tailWord_1142524).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1142524).length < 2 ^ (prefixWord ++ tailWord_1142524).sum := by decide
  have hdescent : baseEnd_1142524 < baseStart_1142524 := by decide
  rcases family_descends (prefixWord ++ tailWord_1142524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1142601 : List Nat := [1, 2, 1, 1, 2, 4, 4, 2, 5]
def baseStart_1142601 : Nat := 118140960795 + 1142601 * 2 ^ 59
def prefixEnd_1142601 : Nat := 4983230072969 + 3 ^ 40 * 1142601 * 2
def baseEnd_1142601 : Nat := 130378557623997622673951

theorem tailTrace_1142601 : CollatzResearch.WordTrace tailWord_1142601 prefixEnd_1142601 130378557623997622673951 := by
  unfold tailWord_1142601
  simp only [CollatzResearch.WordTrace]
  refine ⟨41674082133559192559963657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27782721422372795039975771 41674082133559192559963657)
  ·
    refine ⟨31255561600169394419972743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41674082133559192559963657 31255561600169394419972743)
    ·
      refine ⟨46883342400254091629959115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31255561600169394419972743 46883342400254091629959115)
      ·
        refine ⟨70325013600381137444938673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46883342400254091629959115 70325013600381137444938673)
        ·
          refine ⟨52743760200285853083704005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70325013600381137444938673 52743760200285853083704005)
          ·
            refine ⟨9889455037553597453194501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 52743760200285853083704005 9889455037553597453194501)
            ·
              refine ⟨1854272819541299522473969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9889455037553597453194501 1854272819541299522473969)
              ·
                refine ⟨1390704614655974641855477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1854272819541299522473969 1390704614655974641855477)
                ·
                  refine ⟨130378557623997622673951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1390704614655974641855477 130378557623997622673951)
                  ·
                    rfl

theorem cell22_1142601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 4, 2, 5].length) (baseStart_1142601 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1142601 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1142601 prefixEnd_1142601 := by exact prefixLift 1142601
  have htrace : WordTrace (prefixWord ++ tailWord_1142601) baseStart_1142601 baseEnd_1142601 := by
    simpa [prefixWord, tailWord_1142601, baseEnd_1142601] using wordTrace_append hprefix tailTrace_1142601
  have hstable : (prefixWord ++ tailWord_1142601).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1142601).length < 2 ^ (prefixWord ++ tailWord_1142601).sum := by decide
  have hdescent : baseEnd_1142601 < baseStart_1142601 := by decide
  rcases family_descends (prefixWord ++ tailWord_1142601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1142631 : List Nat := [1, 1, 5, 1, 2, 1, 1, 3, 3, 4]
def baseStart_1142631 : Nat := 118140960795 + 1142631 * 2 ^ 59
def prefixEnd_1142631 : Nat := 4983230072969 + 3 ^ 40 * 1142631 * 2
def baseEnd_1142631 : Nat := 391145942485082789771761

theorem tailTrace_1142631 : CollatzResearch.WordTrace tailWord_1142631 prefixEnd_1142631 391145942485082789771761 := by
  unfold tailWord_1142631
  simp only [CollatzResearch.WordTrace]
  refine ⟨41675176323450507683555747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27783450882300338455703831 41675176323450507683555747)
  ·
    refine ⟨62512764485175761525333621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41675176323450507683555747 62512764485175761525333621)
    ·
      refine ⟨5860571670485227643000027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 62512764485175761525333621 5860571670485227643000027)
      ·
        refine ⟨8790857505727841464500041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5860571670485227643000027 8790857505727841464500041)
        ·
          refine ⟨6593143129295881098375031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8790857505727841464500041 6593143129295881098375031)
          ·
            refine ⟨9889714693943821647562547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6593143129295881098375031 9889714693943821647562547)
            ·
              refine ⟨14834572040915732471343821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9889714693943821647562547 14834572040915732471343821)
              ·
                refine ⟨5562964515343399676753933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14834572040915732471343821 5562964515343399676753933)
                ·
                  refine ⟨2086111693253774878782725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5562964515343399676753933 2086111693253774878782725)
                  ·
                    refine ⟨391145942485082789771761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2086111693253774878782725 391145942485082789771761)
                    ·
                      rfl

theorem cell22_1142631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 3, 3, 4].length) (baseStart_1142631 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1142631 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1142631 prefixEnd_1142631 := by exact prefixLift 1142631
  have htrace : WordTrace (prefixWord ++ tailWord_1142631) baseStart_1142631 baseEnd_1142631 := by
    simpa [prefixWord, tailWord_1142631, baseEnd_1142631] using wordTrace_append hprefix tailTrace_1142631
  have hstable : (prefixWord ++ tailWord_1142631).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1142631).length < 2 ^ (prefixWord ++ tailWord_1142631).sum := by decide
  have hdescent : baseEnd_1142631 < baseStart_1142631 := by decide
  rcases family_descends (prefixWord ++ tailWord_1142631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1142663 : List Nat := [1, 1, 4, 2, 4, 1, 2, 1, 6]
def baseStart_1142663 : Nat := 118140960795 + 1142663 * 2 ^ 59
def prefixEnd_1142663 : Nat := 4983230072969 + 3 ^ 40 * 1142663 * 2
def baseEnd_1142663 : Nat := 130385632246348457657221

theorem tailTrace_1142663 : CollatzResearch.WordTrace tailWord_1142663 prefixEnd_1142663 130385632246348457657221 := by
  unfold tailWord_1142663
  simp only [CollatzResearch.WordTrace]
  refine ⟨41676343459334577148720643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27784228972889718099147095 41676343459334577148720643)
  ·
    refine ⟨62514515189001865723080965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41676343459334577148720643 62514515189001865723080965)
    ·
      refine ⟨11721471597937849823077681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 62514515189001865723080965 11721471597937849823077681)
      ·
        refine ⟨8791103698453387367308261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11721471597937849823077681 8791103698453387367308261)
        ·
          refine ⟨1648331943460010131370299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8791103698453387367308261 1648331943460010131370299)
          ·
            refine ⟨2472497915190015197055449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1648331943460010131370299 2472497915190015197055449)
            ·
              refine ⟨1854373436392511397791587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2472497915190015197055449 1854373436392511397791587)
              ·
                refine ⟨2781560154588767096687381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1854373436392511397791587 2781560154588767096687381)
                ·
                  refine ⟨130385632246348457657221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2781560154588767096687381 130385632246348457657221)
                  ·
                    rfl

theorem cell22_1142663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 2, 1, 6].length) (baseStart_1142663 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1142663 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1142663 prefixEnd_1142663 := by exact prefixLift 1142663
  have htrace : WordTrace (prefixWord ++ tailWord_1142663) baseStart_1142663 baseEnd_1142663 := by
    simpa [prefixWord, tailWord_1142663, baseEnd_1142663] using wordTrace_append hprefix tailTrace_1142663
  have hstable : (prefixWord ++ tailWord_1142663).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1142663).length < 2 ^ (prefixWord ++ tailWord_1142663).sum := by decide
  have hdescent : baseEnd_1142663 < baseStart_1142663 := by decide
  rcases family_descends (prefixWord ++ tailWord_1142663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1142774 : List Nat := [5, 1, 1, 1, 4, 1, 1, 4, 1, 3]
def baseStart_1142774 : Nat := 118140960795 + 1142774 * 2 ^ 59
def prefixEnd_1142774 : Nat := 4983230072969 + 3 ^ 40 * 1142774 * 2
def baseEnd_1142774 : Nat := 391194894307478083446323

theorem tailTrace_1142774 : CollatzResearch.WordTrace tailWord_1142774 prefixEnd_1142774 391194894307478083446323 := by
  unfold tailWord_1142774
  simp only [CollatzResearch.WordTrace]
  refine ⟨2605024497620777694125711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 27786927974621628737340917 2605024497620777694125711)
  ·
    refine ⟨3907536746431166541188567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2605024497620777694125711 3907536746431166541188567)
    ·
      refine ⟨5861305119646749811782851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3907536746431166541188567 5861305119646749811782851)
      ·
        refine ⟨8791957679470124717674277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5861305119646749811782851 8791957679470124717674277)
        ·
          refine ⟨1648492064900648384563927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8791957679470124717674277 1648492064900648384563927)
          ·
            refine ⟨2472738097350972576845891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1648492064900648384563927 2472738097350972576845891)
            ·
              refine ⟨3709107146026458865268837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2472738097350972576845891 3709107146026458865268837)
              ·
                refine ⟨695457589879961037237907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3709107146026458865268837 695457589879961037237907)
                ·
                  refine ⟨1043186384819941555856861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 695457589879961037237907 1043186384819941555856861)
                  ·
                    refine ⟨391194894307478083446323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1043186384819941555856861 391194894307478083446323)
                    ·
                      rfl

theorem cell22_1142774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 1, 4, 1, 3].length) (baseStart_1142774 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1142774 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1142774 prefixEnd_1142774 := by exact prefixLift 1142774
  have htrace : WordTrace (prefixWord ++ tailWord_1142774) baseStart_1142774 baseEnd_1142774 := by
    simpa [prefixWord, tailWord_1142774, baseEnd_1142774] using wordTrace_append hprefix tailTrace_1142774
  have hstable : (prefixWord ++ tailWord_1142774).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1142774).length < 2 ^ (prefixWord ++ tailWord_1142774).sum := by decide
  have hdescent : baseEnd_1142774 < baseStart_1142774 := by decide
  rcases family_descends (prefixWord ++ tailWord_1142774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1142798 : List Nat := [4, 1, 1, 2, 2, 1, 3, 2, 6]
def baseStart_1142798 : Nat := 118140960795 + 1142798 * 2 ^ 59
def prefixEnd_1142798 : Nat := 4983230072969 + 3 ^ 40 * 1142798 * 2
def baseEnd_1142798 : Nat := 130401036665983340282083

theorem tailTrace_1142798 : CollatzResearch.WordTrace tailWord_1142798 prefixEnd_1142798 130401036665983340282083 := by
  unfold tailWord_1142798
  simp only [CollatzResearch.WordTrace]
  refine ⟨5210158414230686900610631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27787511542563663469923365 5210158414230686900610631)
  ·
    refine ⟨7815237621346030350915947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5210158414230686900610631 7815237621346030350915947)
    ·
      refine ⟨11722856432019045526373921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7815237621346030350915947 11722856432019045526373921)
      ·
        refine ⟨8792142324014284144780441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11722856432019045526373921 8792142324014284144780441)
        ·
          refine ⟨6594106743010713108585331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8792142324014284144780441 6594106743010713108585331)
          ·
            refine ⟨9891160114516069662877997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6594106743010713108585331 9891160114516069662877997)
            ·
              refine ⟨3709185042943526123579249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9891160114516069662877997 3709185042943526123579249)
              ·
                refine ⟨2781888782207644592684437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3709185042943526123579249 2781888782207644592684437)
                ·
                  refine ⟨130401036665983340282083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2781888782207644592684437 130401036665983340282083)
                  ·
                    rfl

theorem cell22_1142798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 3, 2, 6].length) (baseStart_1142798 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1142798 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1142798 prefixEnd_1142798 := by exact prefixLift 1142798
  have htrace : WordTrace (prefixWord ++ tailWord_1142798) baseStart_1142798 baseEnd_1142798 := by
    simpa [prefixWord, tailWord_1142798, baseEnd_1142798] using wordTrace_append hprefix tailTrace_1142798
  have hstable : (prefixWord ++ tailWord_1142798).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1142798).length < 2 ^ (prefixWord ++ tailWord_1142798).sum := by decide
  have hdescent : baseEnd_1142798 < baseStart_1142798 := by decide
  rcases family_descends (prefixWord ++ tailWord_1142798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1142815 : List Nat := [1, 1, 2, 4, 1, 2, 4, 3, 4]
def baseStart_1142815 : Nat := 118140960795 + 1142815 * 2 ^ 59
def prefixEnd_1142815 : Nat := 4983230072969 + 3 ^ 40 * 1142815 * 2
def baseEnd_1142815 : Nat := 130402976481789214390399

theorem tailTrace_1142815 : CollatzResearch.WordTrace tailWord_1142815 prefixEnd_1142815 130402976481789214390399 := by
  unfold tailWord_1142815
  simp only [CollatzResearch.WordTrace]
  refine ⟨41681887354783907108253899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27787924903189271405502599 41681887354783907108253899)
  ·
    refine ⟨62522831032175860662380849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41681887354783907108253899 62522831032175860662380849)
    ·
      refine ⟨46892123274131895496785637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62522831032175860662380849 46892123274131895496785637)
      ·
        refine ⟨8792273113899730405647307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 46892123274131895496785637 8792273113899730405647307)
        ·
          refine ⟨13188409670849595608470961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8792273113899730405647307 13188409670849595608470961)
          ·
            refine ⟨9891307253137196706353221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13188409670849595608470961 9891307253137196706353221)
            ·
              refine ⟨1854620109963224382441229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9891307253137196706353221 1854620109963224382441229)
              ·
                refine ⟨695482541236209143415461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1854620109963224382441229 695482541236209143415461)
                ·
                  refine ⟨130402976481789214390399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 695482541236209143415461 130402976481789214390399)
                  ·
                    rfl

theorem cell22_1142815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 4, 3, 4].length) (baseStart_1142815 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1142815 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1142815 prefixEnd_1142815 := by exact prefixLift 1142815
  have htrace : WordTrace (prefixWord ++ tailWord_1142815) baseStart_1142815 baseEnd_1142815 := by
    simpa [prefixWord, tailWord_1142815, baseEnd_1142815] using wordTrace_append hprefix tailTrace_1142815
  have hstable : (prefixWord ++ tailWord_1142815).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1142815).length < 2 ^ (prefixWord ++ tailWord_1142815).sum := by decide
  have hdescent : baseEnd_1142815 < baseStart_1142815 := by decide
  rcases family_descends (prefixWord ++ tailWord_1142815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1142892 : List Nat := [2, 2, 1, 1, 3, 5, 1, 1, 3, 3]
def baseStart_1142892 : Nat := 118140960795 + 1142892 * 2 ^ 59
def prefixEnd_1142892 : Nat := 4983230072969 + 3 ^ 40 * 1142892 * 2
def baseEnd_1142892 : Nat := 391235288118965108995961

theorem tailTrace_1142892 : CollatzResearch.WordTrace tailWord_1142892 prefixEnd_1142892 391235288118965108995961 := by
  unfold tailWord_1142892
  simp only [CollatzResearch.WordTrace]
  refine ⟨20842347887752474629403465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27789797183669966172537953 20842347887752474629403465)
  ·
    refine ⟨15631760915814355972052599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20842347887752474629403465 15631760915814355972052599)
    ·
      refine ⟨23447641373721533958078899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15631760915814355972052599 23447641373721533958078899)
      ·
        refine ⟨35171462060582300937118349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23447641373721533958078899 35171462060582300937118349)
        ·
          refine ⟨13189298272718362851419381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35171462060582300937118349 13189298272718362851419381)
          ·
            refine ⟨1236496713067346517320567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 13189298272718362851419381 1236496713067346517320567)
            ·
              refine ⟨1854745069601019775980851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1236496713067346517320567 1854745069601019775980851)
              ·
                refine ⟨2782117604401529663971277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1854745069601019775980851 2782117604401529663971277)
                ·
                  refine ⟨1043294101650573623989229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2782117604401529663971277 1043294101650573623989229)
                  ·
                    refine ⟨391235288118965108995961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1043294101650573623989229 391235288118965108995961)
                    ·
                      rfl

theorem cell22_1142892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 3, 3].length) (baseStart_1142892 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1142892 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1142892 prefixEnd_1142892 := by exact prefixLift 1142892
  have htrace : WordTrace (prefixWord ++ tailWord_1142892) baseStart_1142892 baseEnd_1142892 := by
    simpa [prefixWord, tailWord_1142892, baseEnd_1142892] using wordTrace_append hprefix tailTrace_1142892
  have hstable : (prefixWord ++ tailWord_1142892).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1142892).length < 2 ^ (prefixWord ++ tailWord_1142892).sum := by decide
  have hdescent : baseEnd_1142892 < baseStart_1142892 := by decide
  rcases family_descends (prefixWord ++ tailWord_1142892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1142905 : List Nat := [1, 2, 1, 3, 4, 2, 1, 3, 5]
def baseStart_1142905 : Nat := 118140960795 + 1142905 * 2 ^ 59
def prefixEnd_1142905 : Nat := 4983230072969 + 3 ^ 40 * 1142905 * 2
def baseEnd_1142905 : Nat := 130413246094879136140307

theorem tailTrace_1142905 : CollatzResearch.WordTrace tailWord_1142905 prefixEnd_1142905 130413246094879136140307 := by
  unfold tailWord_1142905
  simp only [CollatzResearch.WordTrace]
  refine ⟨41685169924457852479030169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27790113282971901652686779 41685169924457852479030169)
  ·
    refine ⟨31263877443343389359272627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41685169924457852479030169 31263877443343389359272627)
    ·
      refine ⟨46895816165015084038908941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31263877443343389359272627 46895816165015084038908941)
      ·
        refine ⟨17585931061880656514590853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46895816165015084038908941 17585931061880656514590853)
        ·
          refine ⟨3297362074102623096485785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17585931061880656514590853 3297362074102623096485785)
          ·
            refine ⟨2473021555576967322364339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3297362074102623096485785 2473021555576967322364339)
            ·
              refine ⟨3709532333365450983546509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2473021555576967322364339 3709532333365450983546509)
              ·
                refine ⟨1391074625012044118829941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3709532333365450983546509 1391074625012044118829941)
                ·
                  refine ⟨130413246094879136140307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1391074625012044118829941 130413246094879136140307)
                  ·
                    rfl

theorem cell22_1142905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 1, 3, 5].length) (baseStart_1142905 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1142905 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1142905 prefixEnd_1142905 := by exact prefixLift 1142905
  have htrace : WordTrace (prefixWord ++ tailWord_1142905) baseStart_1142905 baseEnd_1142905 := by
    simpa [prefixWord, tailWord_1142905, baseEnd_1142905] using wordTrace_append hprefix tailTrace_1142905
  have hstable : (prefixWord ++ tailWord_1142905).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1142905).length < 2 ^ (prefixWord ++ tailWord_1142905).sum := by decide
  have hdescent : baseEnd_1142905 < baseStart_1142905 := by decide
  rcases family_descends (prefixWord ++ tailWord_1142905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1142963 : List Nat := [1, 1, 1, 2, 3, 2, 1, 4, 1, 6]
def baseStart_1142963 : Nat := 118140960795 + 1142963 * 2 ^ 59
def prefixEnd_1142963 : Nat := 4983230072969 + 3 ^ 40 * 1142963 * 2
def baseEnd_1142963 : Nat := 391259592869944590470743

theorem tailTrace_1142963 : CollatzResearch.WordTrace tailWord_1142963 prefixEnd_1142963 391259592869944590470743 := by
  unfold tailWord_1142963
  simp only [CollatzResearch.WordTrace]
  refine ⟨41687285358247728384641543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27791523572165152256427695 41687285358247728384641543)
  ·
    refine ⟨62530928037371592576962315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41687285358247728384641543 62530928037371592576962315)
    ·
      refine ⟨93796392056057388865443473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62530928037371592576962315 93796392056057388865443473)
      ·
        refine ⟨70347294042043041649082605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93796392056057388865443473 70347294042043041649082605)
        ·
          refine ⟨26380235265766140618405977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 70347294042043041649082605 26380235265766140618405977)
          ·
            refine ⟨19785176449324605463804483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26380235265766140618405977 19785176449324605463804483)
            ·
              refine ⟨29677764673986908195706725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19785176449324605463804483 29677764673986908195706725)
              ·
                refine ⟨5564580876372545286695011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29677764673986908195706725 5564580876372545286695011)
                ·
                  refine ⟨8346871314558817930042517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5564580876372545286695011 8346871314558817930042517)
                  ·
                    refine ⟨391259592869944590470743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8346871314558817930042517 391259592869944590470743)
                    ·
                      rfl

theorem cell22_1142963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 4, 1, 6].length) (baseStart_1142963 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1142963 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1142963 prefixEnd_1142963 := by exact prefixLift 1142963
  have htrace : WordTrace (prefixWord ++ tailWord_1142963) baseStart_1142963 baseEnd_1142963 := by
    simpa [prefixWord, tailWord_1142963, baseEnd_1142963] using wordTrace_append hprefix tailTrace_1142963
  have hstable : (prefixWord ++ tailWord_1142963).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1142963).length < 2 ^ (prefixWord ++ tailWord_1142963).sum := by decide
  have hdescent : baseEnd_1142963 < baseStart_1142963 := by decide
  rcases family_descends (prefixWord ++ tailWord_1142963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1143074 : List Nat := [3, 3, 1, 1, 3, 1, 4, 1, 5]
def baseStart_1143074 : Nat := 118140960795 + 1143074 * 2 ^ 59
def prefixEnd_1143074 : Nat := 4983230072969 + 3 ^ 40 * 1143074 * 2
def baseEnd_1143074 : Nat := 130432530146125766981801

theorem tailTrace_1143074 : CollatzResearch.WordTrace tailWord_1143074 prefixEnd_1143074 130432530146125766981801 := by
  unfold tailWord_1143074
  simp only [CollatzResearch.WordTrace]
  refine ⟨10422833465211398585483069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27794222573897062894621517 10422833465211398585483069)
  ·
    refine ⟨3908562549454274469556151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10422833465211398585483069 3908562549454274469556151)
    ·
      refine ⟨5862843824181411704334227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3908562549454274469556151 5862843824181411704334227)
      ·
        refine ⟨8794265736272117556501341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5862843824181411704334227 8794265736272117556501341)
        ·
          refine ⟨3297849651102044083688003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8794265736272117556501341 3297849651102044083688003)
          ·
            refine ⟨4946774476653066125532005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3297849651102044083688003 4946774476653066125532005)
            ·
              refine ⟨927520214372449898537251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4946774476653066125532005 927520214372449898537251)
              ·
                refine ⟨1391280321558674847805877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 927520214372449898537251 1391280321558674847805877)
                ·
                  refine ⟨130432530146125766981801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1391280321558674847805877 130432530146125766981801)
                  ·
                    rfl

theorem cell22_1143074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 4, 1, 5].length) (baseStart_1143074 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1143074 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1143074 prefixEnd_1143074 := by exact prefixLift 1143074
  have htrace : WordTrace (prefixWord ++ tailWord_1143074) baseStart_1143074 baseEnd_1143074 := by
    simpa [prefixWord, tailWord_1143074, baseEnd_1143074] using wordTrace_append hprefix tailTrace_1143074
  have hstable : (prefixWord ++ tailWord_1143074).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1143074).length < 2 ^ (prefixWord ++ tailWord_1143074).sum := by decide
  have hdescent : baseEnd_1143074 < baseStart_1143074 := by decide
  rcases family_descends (prefixWord ++ tailWord_1143074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1143087 : List Nat := [1, 1, 2, 1, 2, 1, 7, 2, 1, 4]
def baseStart_1143087 : Nat := 118140960795 + 1143087 * 2 ^ 59
def prefixEnd_1143087 : Nat := 4983230072969 + 3 ^ 40 * 1143087 * 2
def baseEnd_1143087 : Nat := 391302040604049600370363

theorem tailTrace_1143087 : CollatzResearch.WordTrace tailWord_1143087 prefixEnd_1143087 391302040604049600370363 := by
  unfold tailWord_1143087
  simp only [CollatzResearch.WordTrace]
  refine ⟨41691808009798497562155515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27794538673198998374770343 41691808009798497562155515)
  ·
    refine ⟨62537712014697746343233273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41691808009798497562155515 62537712014697746343233273)
    ·
      refine ⟨46903284011023309757424955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62537712014697746343233273 46903284011023309757424955)
      ·
        refine ⟨70354926016534964636137433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46903284011023309757424955 70354926016534964636137433)
        ·
          refine ⟨52766194512401223477103075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70354926016534964636137433 52766194512401223477103075)
          ·
            refine ⟨79149291768601835215654613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52766194512401223477103075 79149291768601835215654613)
            ·
              refine ⟨1855061525826605512866905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 79149291768601835215654613 1855061525826605512866905)
              ·
                refine ⟨1391296144369954134650179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1855061525826605512866905 1391296144369954134650179)
                ·
                  refine ⟨2086944216554931201975269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1391296144369954134650179 2086944216554931201975269)
                  ·
                    refine ⟨391302040604049600370363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2086944216554931201975269 391302040604049600370363)
                    ·
                      rfl

theorem cell22_1143087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 7, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 7, 2, 1, 4].length) (baseStart_1143087 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1143087 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1143087 prefixEnd_1143087 := by exact prefixLift 1143087
  have htrace : WordTrace (prefixWord ++ tailWord_1143087) baseStart_1143087 baseEnd_1143087 := by
    simpa [prefixWord, tailWord_1143087, baseEnd_1143087] using wordTrace_append hprefix tailTrace_1143087
  have hstable : (prefixWord ++ tailWord_1143087).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1143087).length < 2 ^ (prefixWord ++ tailWord_1143087).sum := by decide
  have hdescent : baseEnd_1143087 < baseStart_1143087 := by decide
  rcases family_descends (prefixWord ++ tailWord_1143087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1143115 : List Nat := [1, 1, 1, 1, 3, 1, 1, 5, 4, 4]
def baseStart_1143115 : Nat := 118140960795 + 1143115 * 2 ^ 59
def prefixEnd_1143115 : Nat := 4983230072969 + 3 ^ 40 * 1143115 * 2
def baseEnd_1143115 : Nat := 391311625576266860670277

theorem tailTrace_1143115 : CollatzResearch.WordTrace tailWord_1143115 prefixEnd_1143115 391311625576266860670277 := by
  unfold tailWord_1143115
  simp only [CollatzResearch.WordTrace]
  refine ⟨41692829253697058344174799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27795219502464705562783199 41692829253697058344174799)
  ·
    refine ⟨62539243880545587516262199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41692829253697058344174799 62539243880545587516262199)
    ·
      refine ⟨93808865820818381274393299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62539243880545587516262199 93808865820818381274393299)
      ·
        refine ⟨140713298731227571911589949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93808865820818381274393299 140713298731227571911589949)
        ·
          refine ⟨52767487024210339466846231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 140713298731227571911589949 52767487024210339466846231)
          ·
            refine ⟨79151230536315509200269347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52767487024210339466846231 79151230536315509200269347)
            ·
              refine ⟨118726845804473263800404021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79151230536315509200269347 118726845804473263800404021)
              ·
                refine ⟨11130641794169368481287877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 118726845804473263800404021 11130641794169368481287877)
                ·
                  refine ⟨2086995336406756590241477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11130641794169368481287877 2086995336406756590241477)
                  ·
                    refine ⟨391311625576266860670277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2086995336406756590241477 391311625576266860670277)
                    ·
                      rfl

theorem cell22_1143115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 5, 4, 4].length) (baseStart_1143115 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1143115 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1143115 prefixEnd_1143115 := by exact prefixLift 1143115
  have htrace : WordTrace (prefixWord ++ tailWord_1143115) baseStart_1143115 baseEnd_1143115 := by
    simpa [prefixWord, tailWord_1143115, baseEnd_1143115] using wordTrace_append hprefix tailTrace_1143115
  have hstable : (prefixWord ++ tailWord_1143115).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1143115).length < 2 ^ (prefixWord ++ tailWord_1143115).sum := by decide
  have hdescent : baseEnd_1143115 < baseStart_1143115 := by decide
  rcases family_descends (prefixWord ++ tailWord_1143115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1143179 : List Nat := [1, 1, 1, 1, 4, 5, 2, 1, 3, 3]
def baseStart_1143179 : Nat := 118140960795 + 1143179 * 2 ^ 59
def prefixEnd_1143179 : Nat := 4983230072969 + 3 ^ 40 * 1143179 * 2
def baseEnd_1143179 : Nat := 391333534084192027070081

theorem tailTrace_1143179 : CollatzResearch.WordTrace tailWord_1143179 prefixEnd_1143179 391333534084192027070081 := by
  unfold tailWord_1143179
  simp only [CollatzResearch.WordTrace]
  refine ⟨41695163525465197274504591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27796775683643464849669727 41695163525465197274504591)
  ·
    refine ⟨62542745288197795911756887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41695163525465197274504591 62542745288197795911756887)
    ·
      refine ⟨93814117932296693867635331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62542745288197795911756887 93814117932296693867635331)
      ·
        refine ⟨140721176898445040801452997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93814117932296693867635331 140721176898445040801452997)
        ·
          refine ⟨26385220668458445150272437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 140721176898445040801452997 26385220668458445150272437)
          ·
            refine ⟨2473614437667979232838041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 26385220668458445150272437 2473614437667979232838041)
            ·
              refine ⟨1855210828250984424628531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2473614437667979232838041 1855210828250984424628531)
              ·
                refine ⟨2782816242376476636942797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1855210828250984424628531 2782816242376476636942797)
                ·
                  refine ⟨1043556090891178738853549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2782816242376476636942797 1043556090891178738853549)
                  ·
                    refine ⟨391333534084192027070081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1043556090891178738853549 391333534084192027070081)
                    ·
                      rfl

theorem cell22_1143179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 2, 1, 3, 3].length) (baseStart_1143179 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1143179 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1143179 prefixEnd_1143179 := by exact prefixLift 1143179
  have htrace : WordTrace (prefixWord ++ tailWord_1143179) baseStart_1143179 baseEnd_1143179 := by
    simpa [prefixWord, tailWord_1143179, baseEnd_1143179] using wordTrace_append hprefix tailTrace_1143179
  have hstable : (prefixWord ++ tailWord_1143179).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1143179).length < 2 ^ (prefixWord ++ tailWord_1143179).sum := by decide
  have hdescent : baseEnd_1143179 < baseStart_1143179 := by decide
  rcases family_descends (prefixWord ++ tailWord_1143179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1143254 : List Nat := [5, 2, 1, 1, 1, 1, 2, 1, 8]
def baseStart_1143254 : Nat := 118140960795 + 1143254 * 2 ^ 59
def prefixEnd_1143254 : Nat := 4983230072969 + 3 ^ 40 * 1143254 * 2
def baseEnd_1143254 : Nat := 130453069372305610481617

theorem tailTrace_1143254 : CollatzResearch.WordTrace tailWord_1143254 prefixEnd_1143254 130453069372305610481617 := by
  unfold tailWord_1143254
  simp only [CollatzResearch.WordTrace]
  refine ⟨2606118687512092817717801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 27798599333462323388989877 2606118687512092817717801)
  ·
    refine ⟨1954589015634069613288351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2606118687512092817717801 1954589015634069613288351)
    ·
      refine ⟨2931883523451104419932527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1954589015634069613288351 2931883523451104419932527)
      ·
        refine ⟨4397825285176656629898791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2931883523451104419932527 4397825285176656629898791)
        ·
          refine ⟨6596737927764984944848187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4397825285176656629898791 6596737927764984944848187)
          ·
            refine ⟨9895106891647477417272281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6596737927764984944848187 9895106891647477417272281)
            ·
              refine ⟨7421330168735608062954211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9895106891647477417272281 7421330168735608062954211)
              ·
                refine ⟨11131995253103412094431317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7421330168735608062954211 11131995253103412094431317)
                ·
                  refine ⟨130453069372305610481617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 11131995253103412094431317 130453069372305610481617)
                  ·
                    rfl

theorem cell22_1143254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 2, 1, 8].length) (baseStart_1143254 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1143254 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1143254 prefixEnd_1143254 := by exact prefixLift 1143254
  have htrace : WordTrace (prefixWord ++ tailWord_1143254) baseStart_1143254 baseEnd_1143254 := by
    simpa [prefixWord, tailWord_1143254, baseEnd_1143254] using wordTrace_append hprefix tailTrace_1143254
  have hstable : (prefixWord ++ tailWord_1143254).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1143254).length < 2 ^ (prefixWord ++ tailWord_1143254).sum := by decide
  have hdescent : baseEnd_1143254 < baseStart_1143254 := by decide
  rcases family_descends (prefixWord ++ tailWord_1143254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1143282 : List Nat := [3, 2, 1, 4, 12]
def baseStart_1143282 : Nat := 118140960795 + 1143282 * 2 ^ 59
def prefixEnd_1143282 : Nat := 4983230072969 + 3 ^ 40 * 1143282 * 2
def baseEnd_1143282 : Nat := 1610571164975860459855

theorem tailTrace_1143282 : CollatzResearch.WordTrace tailWord_1143282 prefixEnd_1143282 1610571164975860459855 := by
  unfold tailWord_1143282
  simp only [CollatzResearch.WordTrace]
  refine ⟨10424730061023011466376025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27799280162728030577002733 10424730061023011466376025)
  ·
    refine ⟨7818547545767258599782019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10424730061023011466376025 7818547545767258599782019)
    ·
      refine ⟨11727821318650887899673029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7818547545767258599782019 11727821318650887899673029)
      ·
        refine ⟨2198966497247041481188693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11727821318650887899673029 2198966497247041481188693)
        ·
          refine ⟨1610571164975860459855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 2198966497247041481188693 1610571164975860459855)
          ·
            rfl

theorem cell22_1143282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 12].length) (baseStart_1143282 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1143282 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1143282 prefixEnd_1143282 := by exact prefixLift 1143282
  have htrace : WordTrace (prefixWord ++ tailWord_1143282) baseStart_1143282 baseEnd_1143282 := by
    simpa [prefixWord, tailWord_1143282, baseEnd_1143282] using wordTrace_append hprefix tailTrace_1143282
  have hstable : (prefixWord ++ tailWord_1143282).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1143282).length < 2 ^ (prefixWord ++ tailWord_1143282).sum := by decide
  have hdescent : baseEnd_1143282 < baseStart_1143282 := by decide
  rcases family_descends (prefixWord ++ tailWord_1143282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1143327 : List Nat := [1, 1, 2, 4, 1, 1, 1, 4, 7]
def baseStart_1143327 : Nat := 118140960795 + 1143327 * 2 ^ 59
def prefixEnd_1143327 : Nat := 4983230072969 + 3 ^ 40 * 1143327 * 2
def baseEnd_1143327 : Nat := 130461399169589658123209

theorem tailTrace_1143327 : CollatzResearch.WordTrace tailWord_1143327 prefixEnd_1143327 130461399169589658123209 := by
  unfold tailWord_1143327
  simp only [CollatzResearch.WordTrace]
  refine ⟨41700561528929018550892235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27800374352619345700594823 41700561528929018550892235)
  ·
    refine ⟨62550842293393527826338353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41700561528929018550892235 62550842293393527826338353)
    ·
      refine ⟨46913131720045145869753765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62550842293393527826338353 46913131720045145869753765)
      ·
        refine ⟨8796212197508464850578831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 46913131720045145869753765 8796212197508464850578831)
        ·
          refine ⟨13194318296262697275868247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8796212197508464850578831 13194318296262697275868247)
          ·
            refine ⟨19791477444394045913802371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13194318296262697275868247 19791477444394045913802371)
            ·
              refine ⟨29687216166591068870703557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19791477444394045913802371 29687216166591068870703557)
              ·
                refine ⟨5566353031235825413256917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29687216166591068870703557 5566353031235825413256917)
                ·
                  refine ⟨130461399169589658123209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5566353031235825413256917 130461399169589658123209)
                  ·
                    rfl

theorem cell22_1143327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 4, 7].length) (baseStart_1143327 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1143327 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1143327 prefixEnd_1143327 := by exact prefixLift 1143327
  have htrace : WordTrace (prefixWord ++ tailWord_1143327) baseStart_1143327 baseEnd_1143327 := by
    simpa [prefixWord, tailWord_1143327, baseEnd_1143327] using wordTrace_append hprefix tailTrace_1143327
  have hstable : (prefixWord ++ tailWord_1143327).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1143327).length < 2 ^ (prefixWord ++ tailWord_1143327).sum := by decide
  have hdescent : baseEnd_1143327 < baseStart_1143327 := by decide
  rcases family_descends (prefixWord ++ tailWord_1143327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1143344 : List Nat := [2, 1, 1, 1, 2, 3, 5, 2, 5]
def baseStart_1143344 : Nat := 118140960795 + 1143344 * 2 ^ 59
def prefixEnd_1143344 : Nat := 4983230072969 + 3 ^ 40 * 1143344 * 2
def baseEnd_1143344 : Nat := 130463338985395532231525

theorem tailTrace_1143344 : CollatzResearch.WordTrace tailWord_1143344 prefixEnd_1143344 130463338985395532231525 := by
  unfold tailWord_1143344
  simp only [CollatzResearch.WordTrace]
  refine ⟨20850590784933715227130543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27800787713244953636174057 20850590784933715227130543)
  ·
    refine ⟨31275886177400572840695815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20850590784933715227130543 31275886177400572840695815)
    ·
      refine ⟨46913829266100859261043723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31275886177400572840695815 46913829266100859261043723)
      ·
        refine ⟨70370743899151288891565585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46913829266100859261043723 70370743899151288891565585)
        ·
          refine ⟨52778057924363466668674189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70370743899151288891565585 52778057924363466668674189)
          ·
            refine ⟨19791771721636300000752821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52778057924363466668674189 19791771721636300000752821)
            ·
              refine ⟨1855478598903403125070577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 19791771721636300000752821 1855478598903403125070577)
              ·
                refine ⟨1391608949177552343802933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1855478598903403125070577 1391608949177552343802933)
                ·
                  refine ⟨130463338985395532231525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1391608949177552343802933 130463338985395532231525)
                  ·
                    rfl

theorem cell22_1143344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 5, 2, 5].length) (baseStart_1143344 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1143344 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1143344 prefixEnd_1143344 := by exact prefixLift 1143344
  have htrace : WordTrace (prefixWord ++ tailWord_1143344) baseStart_1143344 baseEnd_1143344 := by
    simpa [prefixWord, tailWord_1143344, baseEnd_1143344] using wordTrace_append hprefix tailTrace_1143344
  have hstable : (prefixWord ++ tailWord_1143344).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1143344).length < 2 ^ (prefixWord ++ tailWord_1143344).sum := by decide
  have hdescent : baseEnd_1143344 < baseStart_1143344 := by decide
  rcases family_descends (prefixWord ++ tailWord_1143344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1143374 : List Nat := [4, 1, 1, 1, 1, 2, 2, 3, 3, 4]
def baseStart_1143374 : Nat := 118140960795 + 1143374 * 2 ^ 59
def prefixEnd_1143374 : Nat := 4983230072969 + 3 ^ 40 * 1143374 * 2
def baseEnd_1143374 : Nat := 391400286569276518444483

theorem tailTrace_1143374 : CollatzResearch.WordTrace tailWord_1143374 prefixEnd_1143374 391400286569276518444483 := by
  unfold tailWord_1143374
  simp only [CollatzResearch.WordTrace]
  refine ⟨5212784469969843197231647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27801517173172497051902117 5212784469969843197231647)
  ·
    refine ⟨7819176704954764795847471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5212784469969843197231647 7819176704954764795847471)
    ·
      refine ⟨11728765057432147193771207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7819176704954764795847471 11728765057432147193771207)
      ·
        refine ⟨17593147586148220790656811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11728765057432147193771207 17593147586148220790656811)
        ·
          refine ⟨26389721379222331185985217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17593147586148220790656811 26389721379222331185985217)
          ·
            refine ⟨19792291034416748389488913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26389721379222331185985217 19792291034416748389488913)
            ·
              refine ⟨14844218275812561292116685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19792291034416748389488913 14844218275812561292116685)
              ·
                refine ⟨5566581853429710484543757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14844218275812561292116685 5566581853429710484543757)
                ·
                  refine ⟨2087468195036141431703909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5566581853429710484543757 2087468195036141431703909)
                  ·
                    refine ⟨391400286569276518444483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2087468195036141431703909 391400286569276518444483)
                    ·
                      rfl

theorem cell22_1143374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 3, 3, 4].length) (baseStart_1143374 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1143374 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1143374 prefixEnd_1143374 := by exact prefixLift 1143374
  have htrace : WordTrace (prefixWord ++ tailWord_1143374) baseStart_1143374 baseEnd_1143374 := by
    simpa [prefixWord, tailWord_1143374, baseEnd_1143374] using wordTrace_append hprefix tailTrace_1143374
  have hstable : (prefixWord ++ tailWord_1143374).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1143374).length < 2 ^ (prefixWord ++ tailWord_1143374).sum := by decide
  have hdescent : baseEnd_1143374 < baseStart_1143374 := by decide
  rcases family_descends (prefixWord ++ tailWord_1143374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1143406 : List Nat := [4, 1, 2, 2, 2, 1, 3, 1, 6]
def baseStart_1143406 : Nat := 118140960795 + 1143406 * 2 ^ 59
def prefixEnd_1143406 : Nat := 4983230072969 + 3 ^ 40 * 1143406 * 2
def baseEnd_1143406 : Nat := 130470413607746367214795

theorem tailTrace_1143406 : CollatzResearch.WordTrace tailWord_1143406 prefixEnd_1143406 130470413607746367214795 := by
  unfold tailWord_1143406
  simp only [CollatzResearch.WordTrace]
  refine ⟨5212930361955351880377259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27802295263761876695345381 5212930361955351880377259)
  ·
    refine ⟨7819395542933027820565889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5212930361955351880377259 7819395542933027820565889)
    ·
      refine ⟨5864546657199770865424417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7819395542933027820565889 5864546657199770865424417)
      ·
        refine ⟨4398409992899828149068313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5864546657199770865424417 4398409992899828149068313)
        ·
          refine ⟨3298807494674871111801235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4398409992899828149068313 3298807494674871111801235)
          ·
            refine ⟨4948211242012306667701853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3298807494674871111801235 4948211242012306667701853)
            ·
              refine ⟨1855579215754615000388195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4948211242012306667701853 1855579215754615000388195)
              ·
                refine ⟨2783368823631922500582293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1855579215754615000388195 2783368823631922500582293)
                ·
                  refine ⟨130470413607746367214795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2783368823631922500582293 130470413607746367214795)
                  ·
                    rfl

theorem cell22_1143406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 3, 1, 6].length) (baseStart_1143406 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1143406 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1143406 prefixEnd_1143406 := by exact prefixLift 1143406
  have htrace : WordTrace (prefixWord ++ tailWord_1143406) baseStart_1143406 baseEnd_1143406 := by
    simpa [prefixWord, tailWord_1143406, baseEnd_1143406] using wordTrace_append hprefix tailTrace_1143406
  have hstable : (prefixWord ++ tailWord_1143406).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1143406).length < 2 ^ (prefixWord ++ tailWord_1143406).sum := by decide
  have hdescent : baseEnd_1143406 < baseStart_1143406 := by decide
  rcases family_descends (prefixWord ++ tailWord_1143406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1143457 : List Nat := [1, 2, 3, 3, 4, 1, 2, 2, 4]
def baseStart_1143457 : Nat := 118140960795 + 1143457 * 2 ^ 59
def prefixEnd_1143457 : Nat := 4983230072969 + 3 ^ 40 * 1143457 * 2
def baseEnd_1143457 : Nat := 130476233055163989539743

theorem tailTrace_1143457 : CollatzResearch.WordTrace tailWord_1143457 prefixEnd_1143457 130476233055163989539743 := by
  unfold tailWord_1143457
  simp only [CollatzResearch.WordTrace]
  refine ⟨41705303018458050753124625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27803535345638700502083083 41705303018458050753124625)
  ·
    refine ⟨31278977263843538064843469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41705303018458050753124625 31278977263843538064843469)
    ·
      refine ⟨11729616473941326774316301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31278977263843538064843469 11729616473941326774316301)
      ·
        refine ⟨4398606177727997540368613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11729616473941326774316301 4398606177727997540368613)
        ·
          refine ⟨824738658323999538819115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4398606177727997540368613 824738658323999538819115)
          ·
            refine ⟨1237107987485999308228673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 824738658323999538819115 1237107987485999308228673)
            ·
              refine ⟨927830990614499481171505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1237107987485999308228673 927830990614499481171505)
              ·
                refine ⟨695873242960874610878629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 927830990614499481171505 695873242960874610878629)
                ·
                  refine ⟨130476233055163989539743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 695873242960874610878629 130476233055163989539743)
                  ·
                    rfl

theorem cell22_1143457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 4, 1, 2, 2, 4].length) (baseStart_1143457 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1143457 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1143457 prefixEnd_1143457 := by exact prefixLift 1143457
  have htrace : WordTrace (prefixWord ++ tailWord_1143457) baseStart_1143457 baseEnd_1143457 := by
    simpa [prefixWord, tailWord_1143457, baseEnd_1143457] using wordTrace_append hprefix tailTrace_1143457
  have hstable : (prefixWord ++ tailWord_1143457).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1143457).length < 2 ^ (prefixWord ++ tailWord_1143457).sum := by decide
  have hdescent : baseEnd_1143457 < baseStart_1143457 := by decide
  rcases family_descends (prefixWord ++ tailWord_1143457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1143500 : List Nat := [2, 2, 1, 5, 1, 1, 1, 5, 1, 3]
def baseStart_1143500 : Nat := 118140960795 + 1143500 * 2 ^ 59
def prefixEnd_1143500 : Nat := 4983230072969 + 3 ^ 40 * 1143500 * 2
def baseEnd_1143500 : Nat := 391443418944254189794097

theorem tailTrace_1143500 : CollatzResearch.WordTrace tailWord_1143500 prefixEnd_1143500 391443418944254189794097 := by
  unfold tailWord_1143500
  simp only [CollatzResearch.WordTrace]
  refine ⟨20853435678651134548469977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27804580904868179397959969 20853435678651134548469977)
  ·
    refine ⟨15640076758988350911352483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20853435678651134548469977 15640076758988350911352483)
    ·
      refine ⟨23460115138482526367028725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15640076758988350911352483 23460115138482526367028725)
      ·
        refine ⟨2199385794232736846908943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 23460115138482526367028725 2199385794232736846908943)
        ·
          refine ⟨3299078691349105270363415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2199385794232736846908943 3299078691349105270363415)
          ·
            refine ⟨4948618037023657905545123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3299078691349105270363415 4948618037023657905545123)
            ·
              refine ⟨7422927055535486858317685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4948618037023657905545123 7422927055535486858317685)
              ·
                refine ⟨695899411456451892967283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7422927055535486858317685 695899411456451892967283)
                ·
                  refine ⟨1043849117184677839450925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 695899411456451892967283 1043849117184677839450925)
                  ·
                    refine ⟨391443418944254189794097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1043849117184677839450925 391443418944254189794097)
                    ·
                      rfl

theorem cell22_1143500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 1, 5, 1, 3].length) (baseStart_1143500 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1143500 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1143500 prefixEnd_1143500 := by exact prefixLift 1143500
  have htrace : WordTrace (prefixWord ++ tailWord_1143500) baseStart_1143500 baseEnd_1143500 := by
    simpa [prefixWord, tailWord_1143500, baseEnd_1143500] using wordTrace_append hprefix tailTrace_1143500
  have hstable : (prefixWord ++ tailWord_1143500).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1143500).length < 2 ^ (prefixWord ++ tailWord_1143500).sum := by decide
  have hdescent : baseEnd_1143500 < baseStart_1143500 := by decide
  rcases family_descends (prefixWord ++ tailWord_1143500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1143556 : List Nat := [2, 3, 2, 2, 1, 1, 2, 1, 3, 5]
def baseStart_1143556 : Nat := 118140960795 + 1143556 * 2 ^ 59
def prefixEnd_1143556 : Nat := 4983230072969 + 3 ^ 40 * 1143556 * 2
def baseEnd_1143556 : Nat := 391462588888688710393925

theorem tailTrace_1143556 : CollatzResearch.WordTrace tailWord_1143556 prefixEnd_1143556 391462588888688710393925 := by
  unfold tailWord_1143556
  simp only [CollatzResearch.WordTrace]
  refine ⟨20854456922549695330489261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27805942563399593773985681 20854456922549695330489261)
  ·
    refine ⟨7820421345956135748933473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20854456922549695330489261 7820421345956135748933473)
    ·
      refine ⟨5865316009467101811700105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7820421345956135748933473 5865316009467101811700105)
      ·
        refine ⟨4398987007100326358775079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5865316009467101811700105 4398987007100326358775079)
        ·
          refine ⟨6598480510650489538162619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4398987007100326358775079 6598480510650489538162619)
          ·
            refine ⟨9897720765975734307243929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6598480510650489538162619 9897720765975734307243929)
            ·
              refine ⟨7423290574481800730432947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9897720765975734307243929 7423290574481800730432947)
              ·
                refine ⟨11134935861722701095649421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7423290574481800730432947 11134935861722701095649421)
                ·
                  refine ⟨4175600948146012910868533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11134935861722701095649421 4175600948146012910868533)
                  ·
                    refine ⟨391462588888688710393925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4175600948146012910868533 391462588888688710393925)
                    ·
                      rfl

theorem cell22_1143556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 2, 1, 3, 5].length) (baseStart_1143556 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1143556 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1143556 prefixEnd_1143556 := by exact prefixLift 1143556
  have htrace : WordTrace (prefixWord ++ tailWord_1143556) baseStart_1143556 baseEnd_1143556 := by
    simpa [prefixWord, tailWord_1143556, baseEnd_1143556] using wordTrace_append hprefix tailTrace_1143556
  have hstable : (prefixWord ++ tailWord_1143556).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1143556).length < 2 ^ (prefixWord ++ tailWord_1143556).sum := by decide
  have hdescent : baseEnd_1143556 < baseStart_1143556 := by decide
  rcases family_descends (prefixWord ++ tailWord_1143556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1143569 : List Nat := [1, 2, 2, 1, 1, 3, 12]
def baseStart_1143569 : Nat := 118140960795 + 1143569 * 2 ^ 59
def prefixEnd_1143569 : Nat := 4983230072969 + 3 ^ 40 * 1143569 * 2
def baseEnd_1143569 : Nat := 14498779224235592956255

theorem tailTrace_1143569 : CollatzResearch.WordTrace tailWord_1143569 prefixEnd_1143569 14498779224235592956255 := by
  unfold tailWord_1143569
  simp only [CollatzResearch.WordTrace]
  refine ⟨41709387994052293881201761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27806258662701529254134507 41709387994052293881201761)
  ·
    refine ⟨31282040995539220410901321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41709387994052293881201761 31282040995539220410901321)
    ·
      refine ⟨23461530746654415308175991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31282040995539220410901321 23461530746654415308175991)
      ·
        refine ⟨35192296119981622962263987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23461530746654415308175991 35192296119981622962263987)
        ·
          refine ⟨52788444179972434443395981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35192296119981622962263987 52788444179972434443395981)
          ·
            refine ⟨19795666567489662916273493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52788444179972434443395981 19795666567489662916273493)
            ·
              refine ⟨14498779224235592956255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 19795666567489662916273493 14498779224235592956255)
              ·
                rfl

theorem cell22_1143569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 12].length) (baseStart_1143569 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1143569 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1143569 prefixEnd_1143569 := by exact prefixLift 1143569
  have htrace : WordTrace (prefixWord ++ tailWord_1143569) baseStart_1143569 baseEnd_1143569 := by
    simpa [prefixWord, tailWord_1143569, baseEnd_1143569] using wordTrace_append hprefix tailTrace_1143569
  have hstable : (prefixWord ++ tailWord_1143569).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1143569).length < 2 ^ (prefixWord ++ tailWord_1143569).sum := by decide
  have hdescent : baseEnd_1143569 < baseStart_1143569 := by decide
  rcases family_descends (prefixWord ++ tailWord_1143569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1143571 : List Nat := [1, 1, 1, 2, 1, 3, 5, 2, 2, 4]
def baseStart_1143571 : Nat := 118140960795 + 1143571 * 2 ^ 59
def prefixEnd_1143571 : Nat := 4983230072969 + 3 ^ 40 * 1143571 * 2
def baseEnd_1143571 : Nat := 391467723695233671268879

theorem tailTrace_1143571 : CollatzResearch.WordTrace tailWord_1143571 prefixEnd_1143571 391467723695233671268879 := by
  unfold tailWord_1143571
  simp only [CollatzResearch.WordTrace]
  refine ⟨41709460940045048222774567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27806307293363365481849711 41709460940045048222774567)
  ·
    refine ⟨62564191410067572334161851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41709460940045048222774567 62564191410067572334161851)
    ·
      refine ⟨93846287115101358501242777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62564191410067572334161851 93846287115101358501242777)
      ·
        refine ⟨70384715336326018875932083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93846287115101358501242777 70384715336326018875932083)
        ·
          refine ⟨105577073004489028313898125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70384715336326018875932083 105577073004489028313898125)
          ·
            refine ⟨39591402376683385617711797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 105577073004489028313898125 39591402376683385617711797)
            ·
              refine ⟨3711693972814067401660481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 39591402376683385617711797 3711693972814067401660481)
              ·
                refine ⟨2783770479610550551245361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3711693972814067401660481 2783770479610550551245361)
                ·
                  refine ⟨2087827859707912913434021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2783770479610550551245361 2087827859707912913434021)
                  ·
                    refine ⟨391467723695233671268879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2087827859707912913434021 391467723695233671268879)
                    ·
                      rfl

theorem cell22_1143571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 5, 2, 2, 4].length) (baseStart_1143571 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1143571 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1143571 prefixEnd_1143571 := by exact prefixLift 1143571
  have htrace : WordTrace (prefixWord ++ tailWord_1143571) baseStart_1143571 baseEnd_1143571 := by
    simpa [prefixWord, tailWord_1143571, baseEnd_1143571] using wordTrace_append hprefix tailTrace_1143571
  have hstable : (prefixWord ++ tailWord_1143571).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1143571).length < 2 ^ (prefixWord ++ tailWord_1143571).sum := by decide
  have hdescent : baseEnd_1143571 < baseStart_1143571 := by decide
  rcases family_descends (prefixWord ++ tailWord_1143571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1143573 : List Nat := [1, 3, 2, 1, 2, 2, 2, 4, 2, 3]
def baseStart_1143573 : Nat := 118140960795 + 1143573 * 2 ^ 59
def prefixEnd_1143573 : Nat := 4983230072969 + 3 ^ 40 * 1143573 * 2
def baseEnd_1143573 : Nat := 391468408336106332718873

theorem tailTrace_1143573 : CollatzResearch.WordTrace tailWord_1143573 prefixEnd_1143573 391468408336106332718873 := by
  unfold tailWord_1143573
  simp only [CollatzResearch.WordTrace]
  refine ⟨41709533886037802564347373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27806355924025201709564915 41709533886037802564347373)
  ·
    refine ⟨15641075207264175961630265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41709533886037802564347373 15641075207264175961630265)
    ·
      refine ⟨11730806405448131971222699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15641075207264175961630265 11730806405448131971222699)
      ·
        refine ⟨17596209608172197956834049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11730806405448131971222699 17596209608172197956834049)
        ·
          refine ⟨13197157206129148467625537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17596209608172197956834049 13197157206129148467625537)
          ·
            refine ⟨9897867904596861350719153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13197157206129148467625537 9897867904596861350719153)
            ·
              refine ⟨7423400928447646013039365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9897867904596861350719153 7423400928447646013039365)
              ·
                refine ⟨1391887674083933627444881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7423400928447646013039365 1391887674083933627444881)
                ·
                  refine ⟨1043915755562950220583661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1391887674083933627444881 1043915755562950220583661)
                  ·
                    refine ⟨391468408336106332718873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1043915755562950220583661 391468408336106332718873)
                    ·
                      rfl

theorem cell22_1143573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 2, 4, 2, 3].length) (baseStart_1143573 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1143573 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1143573 prefixEnd_1143573 := by exact prefixLift 1143573
  have htrace : WordTrace (prefixWord ++ tailWord_1143573) baseStart_1143573 baseEnd_1143573 := by
    simpa [prefixWord, tailWord_1143573, baseEnd_1143573] using wordTrace_append hprefix tailTrace_1143573
  have hstable : (prefixWord ++ tailWord_1143573).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1143573).length < 2 ^ (prefixWord ++ tailWord_1143573).sum := by decide
  have hdescent : baseEnd_1143573 < baseStart_1143573 := by decide
  rcases family_descends (prefixWord ++ tailWord_1143573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1143575 : List Nat := [1, 1, 3, 4, 4, 1, 1, 1, 6]
def baseStart_1143575 : Nat := 118140960795 + 1143575 * 2 ^ 59
def prefixEnd_1143575 : Nat := 4983230072969 + 3 ^ 40 * 1143575 * 2
def baseEnd_1143575 : Nat := 130489697658992998056289

theorem tailTrace_1143575 : CollatzResearch.WordTrace tailWord_1143575 prefixEnd_1143575 130489697658992998056289 := by
  unfold tailWord_1143575
  simp only [CollatzResearch.WordTrace]
  refine ⟨41709606832030556905920179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27806404554687037937280119 41709606832030556905920179)
  ·
    refine ⟨62564410248045835358880269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41709606832030556905920179 62564410248045835358880269)
    ·
      refine ⟨23461653843017188259580101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62564410248045835358880269 23461653843017188259580101)
      ·
        refine ⟨4399060095565722798671269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23461653843017188259580101 4399060095565722798671269)
        ·
          refine ⟨824823767918573024750863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4399060095565722798671269 824823767918573024750863)
          ·
            refine ⟨1237235651877859537126295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 824823767918573024750863 1237235651877859537126295)
            ·
              refine ⟨1855853477816789305689443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1237235651877859537126295 1855853477816789305689443)
              ·
                refine ⟨2783780216725183958534165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1855853477816789305689443 2783780216725183958534165)
                ·
                  refine ⟨130489697658992998056289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2783780216725183958534165 130489697658992998056289)
                  ·
                    rfl

theorem cell22_1143575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 4, 1, 1, 1, 6].length) (baseStart_1143575 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1143575 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1143575 prefixEnd_1143575 := by exact prefixLift 1143575
  have htrace : WordTrace (prefixWord ++ tailWord_1143575) baseStart_1143575 baseEnd_1143575 := by
    simpa [prefixWord, tailWord_1143575, baseEnd_1143575] using wordTrace_append hprefix tailTrace_1143575
  have hstable : (prefixWord ++ tailWord_1143575).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1143575).length < 2 ^ (prefixWord ++ tailWord_1143575).sum := by decide
  have hdescent : baseEnd_1143575 < baseStart_1143575 := by decide
  rcases family_descends (prefixWord ++ tailWord_1143575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1143586 : List Nat := [3, 3, 1, 1, 2, 2, 1, 9]
def baseStart_1143586 : Nat := 118140960795 + 1143586 * 2 ^ 59
def prefixEnd_1143586 : Nat := 4983230072969 + 3 ^ 40 * 1143586 * 2
def baseEnd_1143586 : Nat := 43496984277975403571537

theorem tailTrace_1143586 : CollatzResearch.WordTrace tailWord_1143586 prefixEnd_1143586 43496984277975403571537 := by
  unfold tailWord_1143586
  simp only [CollatzResearch.WordTrace]
  refine ⟨10427502008747676446142653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27806672023327137189713741 10427502008747676446142653)
  ·
    refine ⟨3910313253280378667303495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10427502008747676446142653 3910313253280378667303495)
    ·
      refine ⟨5865469879920568000955243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3910313253280378667303495 5865469879920568000955243)
      ·
        refine ⟨8798204819880852001432865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5865469879920568000955243 8798204819880852001432865)
        ·
          refine ⟨6598653614910639001074649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8798204819880852001432865 6598653614910639001074649)
          ·
            refine ⟨4948990211182979250805987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6598653614910639001074649 4948990211182979250805987)
            ·
              refine ⟨7423485316774468876208981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4948990211182979250805987 7423485316774468876208981)
              ·
                refine ⟨43496984277975403571537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 7423485316774468876208981 43496984277975403571537)
                ·
                  rfl

theorem cell22_1143586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 1, 9].length) (baseStart_1143586 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1143586 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1143586 prefixEnd_1143586 := by exact prefixLift 1143586
  have htrace : WordTrace (prefixWord ++ tailWord_1143586) baseStart_1143586 baseEnd_1143586 := by
    simpa [prefixWord, tailWord_1143586, baseEnd_1143586] using wordTrace_append hprefix tailTrace_1143586
  have hstable : (prefixWord ++ tailWord_1143586).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1143586).length < 2 ^ (prefixWord ++ tailWord_1143586).sum := by decide
  have hdescent : baseEnd_1143586 < baseStart_1143586 := by decide
  rcases family_descends (prefixWord ++ tailWord_1143586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1143594 : List Nat := [3, 1, 4, 3, 2, 1, 1, 2, 1, 4]
def baseStart_1143594 : Nat := 118140960795 + 1143594 * 2 ^ 59
def prefixEnd_1143594 : Nat := 4983230072969 + 3 ^ 40 * 1143594 * 2
def baseEnd_1143594 : Nat := 391475597065269277943809

theorem tailTrace_1143594 : CollatzResearch.WordTrace tailWord_1143594 prefixEnd_1143594 391475597065269277943809 := by
  unfold tailWord_1143594
  simp only [CollatzResearch.WordTrace]
  refine ⟨10427574954740430787715459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27806866545974482100574557 10427574954740430787715459)
  ·
    refine ⟨15641362432110646181573189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10427574954740430787715459 15641362432110646181573189)
    ·
      refine ⟨2932755456020746159044973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15641362432110646181573189 2932755456020746159044973)
      ·
        refine ⟨1099783296007779809641865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2932755456020746159044973 1099783296007779809641865)
        ·
          refine ⟨824837472005834857231399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1099783296007779809641865 824837472005834857231399)
          ·
            refine ⟨1237256208008752285847099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 824837472005834857231399 1237256208008752285847099)
            ·
              refine ⟨1855884312013128428770649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1237256208008752285847099 1855884312013128428770649)
              ·
                refine ⟨1391913234009846321577987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1855884312013128428770649 1391913234009846321577987)
                ·
                  refine ⟨2087869851014769482366981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1391913234009846321577987 2087869851014769482366981)
                  ·
                    refine ⟨391475597065269277943809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2087869851014769482366981 391475597065269277943809)
                    ·
                      rfl

theorem cell22_1143594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 2, 1, 1, 2, 1, 4].length) (baseStart_1143594 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1143594 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1143594 prefixEnd_1143594 := by exact prefixLift 1143594
  have htrace : WordTrace (prefixWord ++ tailWord_1143594) baseStart_1143594 baseEnd_1143594 := by
    simpa [prefixWord, tailWord_1143594, baseEnd_1143594] using wordTrace_append hprefix tailTrace_1143594
  have hstable : (prefixWord ++ tailWord_1143594).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1143594).length < 2 ^ (prefixWord ++ tailWord_1143594).sum := by decide
  have hdescent : baseEnd_1143594 < baseStart_1143594 := by decide
  rcases family_descends (prefixWord ++ tailWord_1143594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1143620 : List Nat := [2, 3, 4, 2, 2, 9]
def baseStart_1143620 : Nat := 118140960795 + 1143620 * 2 ^ 59
def prefixEnd_1143620 : Nat := 4983230072969 + 3 ^ 40 * 1143620 * 2
def baseEnd_1143620 : Nat := 4833141943168072553009

theorem tailTrace_1143620 : CollatzResearch.WordTrace tailWord_1143620 prefixEnd_1143620 4833141943168072553009 := by
  unfold tailWord_1143620
  simp only [CollatzResearch.WordTrace]
  refine ⟨20855624058433764795654157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27807498744578353060872209 20855624058433764795654157)
  ·
    refine ⟨7820859021912661798370309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20855624058433764795654157 7820859021912661798370309)
    ·
      refine ⟨1466411066608624087194433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7820859021912661798370309 1466411066608624087194433)
      ·
        refine ⟨1099808299956468065395825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1466411066608624087194433 1099808299956468065395825)
        ·
          refine ⟨824856224967351049046869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1099808299956468065395825 824856224967351049046869)
          ·
            refine ⟨4833141943168072553009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 824856224967351049046869 4833141943168072553009)
            ·
              rfl

theorem cell22_1143620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 2, 9].length) (baseStart_1143620 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1143620 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1143620 prefixEnd_1143620 := by exact prefixLift 1143620
  have htrace : WordTrace (prefixWord ++ tailWord_1143620) baseStart_1143620 baseEnd_1143620 := by
    simpa [prefixWord, tailWord_1143620, baseEnd_1143620] using wordTrace_append hprefix tailTrace_1143620
  have hstable : (prefixWord ++ tailWord_1143620).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1143620).length < 2 ^ (prefixWord ++ tailWord_1143620).sum := by decide
  have hdescent : baseEnd_1143620 < baseStart_1143620 := by decide
  rcases family_descends (prefixWord ++ tailWord_1143620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1143682 : List Nat := [3, 4, 2, 2, 1, 1, 1, 1, 7]
def baseStart_1143682 : Nat := 118140960795 + 1143682 * 2 ^ 59
def prefixEnd_1143682 : Nat := 4983230072969 + 3 ^ 40 * 1143682 * 2
def baseEnd_1143682 : Nat := 130501907087888793914513

theorem tailTrace_1143682 : CollatzResearch.WordTrace tailWord_1143682 prefixEnd_1143682 130501907087888793914513 := by
  unfold tailWord_1143682
  simp only [CollatzResearch.WordTrace]
  refine ⟨10428377360660728545016325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27809006295095276120043533 10428377360660728545016325)
  ·
    refine ⟨1955320755123886602190561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10428377360660728545016325 1955320755123886602190561)
    ·
      refine ⟨1466490566342914951642921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1955320755123886602190561 1466490566342914951642921)
      ·
        refine ⟨1099867924757186213732191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1466490566342914951642921 1099867924757186213732191)
        ·
          refine ⟨1649801887135779320598287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1099867924757186213732191 1649801887135779320598287)
          ·
            refine ⟨2474702830703668980897431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1649801887135779320598287 2474702830703668980897431)
            ·
              refine ⟨3712054246055503471346147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2474702830703668980897431 3712054246055503471346147)
              ·
                refine ⟨5568081369083255207019221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3712054246055503471346147 5568081369083255207019221)
                ·
                  refine ⟨130501907087888793914513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5568081369083255207019221 130501907087888793914513)
                  ·
                    rfl

theorem cell22_1143682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 1, 1, 7].length) (baseStart_1143682 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1143682 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1143682 prefixEnd_1143682 := by exact prefixLift 1143682
  have htrace : WordTrace (prefixWord ++ tailWord_1143682) baseStart_1143682 baseEnd_1143682 := by
    simpa [prefixWord, tailWord_1143682, baseEnd_1143682] using wordTrace_append hprefix tailTrace_1143682
  have hstable : (prefixWord ++ tailWord_1143682).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1143682).length < 2 ^ (prefixWord ++ tailWord_1143682).sum := by decide
  have hdescent : baseEnd_1143682 < baseStart_1143682 := by decide
  rcases family_descends (prefixWord ++ tailWord_1143682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1143691 : List Nat := [1, 1, 1, 1, 4, 2, 2, 2, 3, 5]
def baseStart_1143691 : Nat := 118140960795 + 1143691 * 2 ^ 59
def prefixEnd_1143691 : Nat := 4983230072969 + 3 ^ 40 * 1143691 * 2
def baseEnd_1143691 : Nat := 391508802147593358268511

theorem tailTrace_1143691 : CollatzResearch.WordTrace tailWord_1143691 prefixEnd_1143691 391508802147593358268511 := by
  unfold tailWord_1143691
  simp only [CollatzResearch.WordTrace]
  refine ⟨41713837699610308717142927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27809225133073539144761951 41713837699610308717142927)
  ·
    refine ⟨62570756549415463075714391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41713837699610308717142927 62570756549415463075714391)
    ·
      refine ⟨93856134824123194613571587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62570756549415463075714391 93856134824123194613571587)
      ·
        refine ⟨140784202236184791920357381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93856134824123194613571587 140784202236184791920357381)
        ·
          refine ⟨26397037919284648485067009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 140784202236184791920357381 26397037919284648485067009)
          ·
            refine ⟨19797778439463486363800257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26397037919284648485067009 19797778439463486363800257)
            ·
              refine ⟨14848333829597614772850193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19797778439463486363800257 14848333829597614772850193)
              ·
                refine ⟨11136250372198211079637645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14848333829597614772850193 11136250372198211079637645)
                ·
                  refine ⟨4176093889574329154864117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11136250372198211079637645 4176093889574329154864117)
                  ·
                    refine ⟨391508802147593358268511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4176093889574329154864117 391508802147593358268511)
                    ·
                      rfl

theorem cell22_1143691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 2, 3, 5].length) (baseStart_1143691 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1143691 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1143691 prefixEnd_1143691 := by exact prefixLift 1143691
  have htrace : WordTrace (prefixWord ++ tailWord_1143691) baseStart_1143691 baseEnd_1143691 := by
    simpa [prefixWord, tailWord_1143691, baseEnd_1143691] using wordTrace_append hprefix tailTrace_1143691
  have hstable : (prefixWord ++ tailWord_1143691).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1143691).length < 2 ^ (prefixWord ++ tailWord_1143691).sum := by decide
  have hdescent : baseEnd_1143691 < baseStart_1143691 := by decide
  rcases family_descends (prefixWord ++ tailWord_1143691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1143721 : List Nat := [1, 2, 1, 1, 1, 1, 7, 8]
def baseStart_1143721 : Nat := 118140960795 + 1143721 * 2 ^ 59
def prefixEnd_1143721 : Nat := 4983230072969 + 3 ^ 40 * 1143721 * 2
def baseEnd_1143721 : Nat := 43502119084520364446491

theorem tailTrace_1143721 : CollatzResearch.WordTrace tailWord_1143721 prefixEnd_1143721 43502119084520364446491 := by
  unfold tailWord_1143721
  simp only [CollatzResearch.WordTrace]
  refine ⟨41714931889501623840735017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27809954593001082560490011 41714931889501623840735017)
  ·
    refine ⟨31286198917126217880551263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41714931889501623840735017 31286198917126217880551263)
    ·
      refine ⟨46929298375689326820826895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31286198917126217880551263 46929298375689326820826895)
      ·
        refine ⟨70393947563533990231240343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46929298375689326820826895 70393947563533990231240343)
        ·
          refine ⟨105590921345300985346860515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70393947563533990231240343 105590921345300985346860515)
          ·
            refine ⟨158386382017951478020290773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 105590921345300985346860515 158386382017951478020290773)
            ·
              refine ⟨3712180828545737766100565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 158386382017951478020290773 3712180828545737766100565)
              ·
                refine ⟨43502119084520364446491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3712180828545737766100565 43502119084520364446491)
                ·
                  rfl

theorem cell22_1143721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 7, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 7, 8].length) (baseStart_1143721 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1143721 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1143721 prefixEnd_1143721 := by exact prefixLift 1143721
  have htrace : WordTrace (prefixWord ++ tailWord_1143721) baseStart_1143721 baseEnd_1143721 := by
    simpa [prefixWord, tailWord_1143721, baseEnd_1143721] using wordTrace_append hprefix tailTrace_1143721
  have hstable : (prefixWord ++ tailWord_1143721).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1143721).length < 2 ^ (prefixWord ++ tailWord_1143721).sum := by decide
  have hdescent : baseEnd_1143721 < baseStart_1143721 := by decide
  rcases family_descends (prefixWord ++ tailWord_1143721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1143750 : List Nat := [6, 1, 3, 1, 2, 1, 2, 1, 5]
def baseStart_1143750 : Nat := 118140960795 + 1143750 * 2 ^ 59
def prefixEnd_1143750 : Nat := 4983230072969 + 3 ^ 40 * 1143750 * 2
def baseEnd_1143750 : Nat := 130509666351112290347777

theorem tailTrace_1143750 : CollatzResearch.WordTrace tailWord_1143750 prefixEnd_1143750 130509666351112290347777 := by
  unfold tailWord_1143750
  simp only [CollatzResearch.WordTrace]
  refine ⟨1303624675199892556048147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 27810659737597707862360469 1303624675199892556048147)
  ·
    refine ⟨1955437012799838834072221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1303624675199892556048147 1955437012799838834072221)
    ·
      refine ⟨733288879799939562777083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1955437012799838834072221 733288879799939562777083)
      ·
        refine ⟨1099933319699909344165625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 733288879799939562777083 1099933319699909344165625)
        ·
          refine ⟨824949989774932008124219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1099933319699909344165625 824949989774932008124219)
          ·
            refine ⟨1237424984662398012186329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 824949989774932008124219 1237424984662398012186329)
            ·
              refine ⟨928068738496798509139747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1237424984662398012186329 928068738496798509139747)
              ·
                refine ⟨1392103107745197763709621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 928068738496798509139747 1392103107745197763709621)
                ·
                  refine ⟨130509666351112290347777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1392103107745197763709621 130509666351112290347777)
                  ·
                    rfl

theorem cell22_1143750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 2, 1, 2, 1, 5].length) (baseStart_1143750 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1143750 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1143750 prefixEnd_1143750 := by exact prefixLift 1143750
  have htrace : WordTrace (prefixWord ++ tailWord_1143750) baseStart_1143750 baseEnd_1143750 := by
    simpa [prefixWord, tailWord_1143750, baseEnd_1143750] using wordTrace_append hprefix tailTrace_1143750
  have hstable : (prefixWord ++ tailWord_1143750).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1143750).length < 2 ^ (prefixWord ++ tailWord_1143750).sum := by decide
  have hdescent : baseEnd_1143750 < baseStart_1143750 := by decide
  rcases family_descends (prefixWord ++ tailWord_1143750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1143804 : List Nat := [2, 2, 2, 1, 2, 3, 4, 2, 1, 3]
def baseStart_1143804 : Nat := 118140960795 + 1143804 * 2 ^ 59
def prefixEnd_1143804 : Nat := 4983230072969 + 3 ^ 40 * 1143804 * 2
def baseEnd_1143804 : Nat := 391547484356898730193165

theorem tailTrace_1143804 : CollatzResearch.WordTrace tailWord_1143804 prefixEnd_1143804 391547484356898730193165 := by
  unfold tailWord_1143804
  simp only [CollatzResearch.WordTrace]
  refine ⟨20858979574100464508003233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27811972765467286010670977 20858979574100464508003233)
  ·
    refine ⟨15644234680575348381002425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20858979574100464508003233 15644234680575348381002425)
    ·
      refine ⟨11733176010431511285751819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15644234680575348381002425 11733176010431511285751819)
      ·
        refine ⟨17599764015647266928627729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11733176010431511285751819 17599764015647266928627729)
        ·
          refine ⟨13199823011735450196470797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17599764015647266928627729 13199823011735450196470797)
          ·
            refine ⟨4949933629400793823676549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13199823011735450196470797 4949933629400793823676549)
            ·
              refine ⟨928112555512648841939353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4949933629400793823676549 928112555512648841939353)
              ·
                refine ⟨696084416634486631454515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 928112555512648841939353 696084416634486631454515)
                ·
                  refine ⟨1044126624951729947181773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 696084416634486631454515 1044126624951729947181773)
                  ·
                    refine ⟨391547484356898730193165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1044126624951729947181773 391547484356898730193165)
                    ·
                      rfl

theorem cell22_1143804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 4, 2, 1, 3].length) (baseStart_1143804 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1143804 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1143804 prefixEnd_1143804 := by exact prefixLift 1143804
  have htrace : WordTrace (prefixWord ++ tailWord_1143804) baseStart_1143804 baseEnd_1143804 := by
    simpa [prefixWord, tailWord_1143804, baseEnd_1143804] using wordTrace_append hprefix tailTrace_1143804
  have hstable : (prefixWord ++ tailWord_1143804).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1143804).length < 2 ^ (prefixWord ++ tailWord_1143804).sum := by decide
  have hdescent : baseEnd_1143804 < baseStart_1143804 := by decide
  rcases family_descends (prefixWord ++ tailWord_1143804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1143813 : List Nat := [1, 3, 1, 1, 2, 3, 1, 1, 5, 4]
def baseStart_1143813 : Nat := 118140960795 + 1143813 * 2 ^ 59
def prefixEnd_1143813 : Nat := 4983230072969 + 3 ^ 40 * 1143813 * 2
def baseEnd_1143813 : Nat := 391550565240825706718137

theorem tailTrace_1143813 : CollatzResearch.WordTrace tailWord_1143813 prefixEnd_1143813 391550565240825706718137 := by
  unfold tailWord_1143813
  simp only [CollatzResearch.WordTrace]
  refine ⟨41718287405168323553084093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27812191603445549035389395 41718287405168323553084093)
  ·
    refine ⟨15644357776938121332406535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41718287405168323553084093 15644357776938121332406535)
    ·
      refine ⟨23466536665407181998609803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15644357776938121332406535 23466536665407181998609803)
      ·
        refine ⟨35199804998110772997914705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23466536665407181998609803 35199804998110772997914705)
        ·
          refine ⟨26399853748583079748436029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35199804998110772997914705 26399853748583079748436029)
          ·
            refine ⟨9899945155718654905663511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26399853748583079748436029 9899945155718654905663511)
            ·
              refine ⟨14849917733577982358495267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9899945155718654905663511 14849917733577982358495267)
              ·
                refine ⟨22274876600366973537742901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14849917733577982358495267 22274876600366973537742901)
                ·
                  refine ⟨2088269681284403769163397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 22274876600366973537742901 2088269681284403769163397)
                  ·
                    refine ⟨391550565240825706718137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2088269681284403769163397 391550565240825706718137)
                    ·
                      rfl

theorem cell22_1143813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 1, 5, 4].length) (baseStart_1143813 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1143813 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1143813 prefixEnd_1143813 := by exact prefixLift 1143813
  have htrace : WordTrace (prefixWord ++ tailWord_1143813) baseStart_1143813 baseEnd_1143813 := by
    simpa [prefixWord, tailWord_1143813, baseEnd_1143813] using wordTrace_append hprefix tailTrace_1143813
  have hstable : (prefixWord ++ tailWord_1143813).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1143813).length < 2 ^ (prefixWord ++ tailWord_1143813).sum := by decide
  have hdescent : baseEnd_1143813 < baseStart_1143813 := by decide
  rcases family_descends (prefixWord ++ tailWord_1143813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1143862 : List Nat := [5, 1, 2, 1, 1, 3, 2, 1, 6]
def baseStart_1143862 : Nat := 118140960795 + 1143862 * 2 ^ 59
def prefixEnd_1143862 : Nat := 4983230072969 + 3 ^ 40 * 1143862 * 2
def baseEnd_1143862 : Nat := 130522446314068637414329

theorem tailTrace_1143862 : CollatzResearch.WordTrace tailWord_1143862 prefixEnd_1143862 130522446314068637414329 := by
  unfold tailWord_1143862
  simp only [CollatzResearch.WordTrace]
  refine ⟨2607504661374425307601115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 27813383054660536614411893 2607504661374425307601115)
  ·
    refine ⟨3911256992061637961401673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2607504661374425307601115 3911256992061637961401673)
    ·
      refine ⟨2933442744046228471051255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3911256992061637961401673 2933442744046228471051255)
      ·
        refine ⟨4400164116069342706576883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2933442744046228471051255 4400164116069342706576883)
        ·
          refine ⟨6600246174104014059865325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4400164116069342706576883 6600246174104014059865325)
          ·
            refine ⟨2475092315289005272449497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6600246174104014059865325 2475092315289005272449497)
            ·
              refine ⟨1856319236466753954337123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2475092315289005272449497 1856319236466753954337123)
              ·
                refine ⟨2784478854700130931505685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1856319236466753954337123 2784478854700130931505685)
                ·
                  refine ⟨130522446314068637414329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2784478854700130931505685 130522446314068637414329)
                  ·
                    rfl

theorem cell22_1143862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 2, 1, 6].length) (baseStart_1143862 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1143862 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1143862 prefixEnd_1143862 := by exact prefixLift 1143862
  have htrace : WordTrace (prefixWord ++ tailWord_1143862) baseStart_1143862 baseEnd_1143862 := by
    simpa [prefixWord, tailWord_1143862, baseEnd_1143862] using wordTrace_append hprefix tailTrace_1143862
  have hstable : (prefixWord ++ tailWord_1143862).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1143862).length < 2 ^ (prefixWord ++ tailWord_1143862).sum := by decide
  have hdescent : baseEnd_1143862 < baseStart_1143862 := by decide
  rcases family_descends (prefixWord ++ tailWord_1143862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1143890 : List Nat := [3, 2, 2, 1, 3, 2, 1, 8]
def baseStart_1143890 : Nat := 118140960795 + 1143890 * 2 ^ 59
def prefixEnd_1143890 : Nat := 4983230072969 + 3 ^ 40 * 1143890 * 2
def baseEnd_1143890 : Nat := 43508547101602574726989

theorem tailTrace_1143890 : CollatzResearch.WordTrace tailWord_1143890 prefixEnd_1143890 43508547101602574726989 := by
  unfold tailWord_1143890
  simp only [CollatzResearch.WordTrace]
  refine ⟨10430273956472341425909281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27814063883926243802424749 10430273956472341425909281)
  ·
    refine ⟨7822705467354256069431961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10430273956472341425909281 7822705467354256069431961)
    ·
      refine ⟨5867029100515692052073971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7822705467354256069431961 5867029100515692052073971)
      ·
        refine ⟨8800543650773538078110957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5867029100515692052073971 8800543650773538078110957)
        ·
          refine ⟨3300203869040076779291609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8800543650773538078110957 3300203869040076779291609)
          ·
            refine ⟨2475152901780057584468707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3300203869040076779291609 2475152901780057584468707)
            ·
              refine ⟨3712729352670086376703061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2475152901780057584468707 3712729352670086376703061)
              ·
                refine ⟨43508547101602574726989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3712729352670086376703061 43508547101602574726989)
                ·
                  rfl

theorem cell22_1143890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 1, 8].length) (baseStart_1143890 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1143890 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1143890 prefixEnd_1143890 := by exact prefixLift 1143890
  have htrace : WordTrace (prefixWord ++ tailWord_1143890) baseStart_1143890 baseEnd_1143890 := by
    simpa [prefixWord, tailWord_1143890, baseEnd_1143890] using wordTrace_append hprefix tailTrace_1143890
  have hstable : (prefixWord ++ tailWord_1143890).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1143890).length < 2 ^ (prefixWord ++ tailWord_1143890).sum := by decide
  have hdescent : baseEnd_1143890 < baseStart_1143890 := by decide
  rcases family_descends (prefixWord ++ tailWord_1143890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1143905 : List Nat := [1, 2, 3, 1, 1, 2, 2, 2, 5, 3]
def baseStart_1143905 : Nat := 118140960795 + 1143905 * 2 ^ 59
def prefixEnd_1143905 : Nat := 4983230072969 + 3 ^ 40 * 1143905 * 2
def baseEnd_1143905 : Nat := 391582058720968133417855

theorem tailTrace_1143905 : CollatzResearch.WordTrace tailWord_1143905 prefixEnd_1143905 391582058720968133417855 := by
  unfold tailWord_1143905
  simp only [CollatzResearch.WordTrace]
  refine ⟨41721642920835023265433169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27814428613890015510288779 41721642920835023265433169)
  ·
    refine ⟨31291232190626267449074877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41721642920835023265433169 31291232190626267449074877)
    ·
      refine ⟨11734212071484850293403079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31291232190626267449074877 11734212071484850293403079)
      ·
        refine ⟨17601318107227275440104619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11734212071484850293403079 17601318107227275440104619)
        ·
          refine ⟨26401977160840913160156929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17601318107227275440104619 26401977160840913160156929)
          ·
            refine ⟨19801482870630684870117697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26401977160840913160156929 19801482870630684870117697)
            ·
              refine ⟨14851112152973013652588273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19801482870630684870117697 14851112152973013652588273)
              ·
                refine ⟨11138334114729760239441205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14851112152973013652588273 11138334114729760239441205)
                ·
                  refine ⟨1044218823255915022447613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 11138334114729760239441205 1044218823255915022447613)
                  ·
                    refine ⟨391582058720968133417855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1044218823255915022447613 391582058720968133417855)
                    ·
                      rfl

theorem cell22_1143905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 2, 5, 3].length) (baseStart_1143905 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1143905 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1143905 prefixEnd_1143905 := by exact prefixLift 1143905
  have htrace : WordTrace (prefixWord ++ tailWord_1143905) baseStart_1143905 baseEnd_1143905 := by
    simpa [prefixWord, tailWord_1143905, baseEnd_1143905] using wordTrace_append hprefix tailTrace_1143905
  have hstable : (prefixWord ++ tailWord_1143905).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1143905).length < 2 ^ (prefixWord ++ tailWord_1143905).sum := by decide
  have hdescent : baseEnd_1143905 < baseStart_1143905 := by decide
  rcases family_descends (prefixWord ++ tailWord_1143905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1144057 : List Nat := [1, 2, 1, 3, 1, 1, 3, 4, 3, 3]
def baseStart_1144057 : Nat := 118140960795 + 1144057 * 2 ^ 59
def prefixEnd_1144057 : Nat := 4983230072969 + 3 ^ 40 * 1144057 * 2
def baseEnd_1144057 : Nat := 391634091427290403617389

theorem tailTrace_1144057 : CollatzResearch.WordTrace tailWord_1144057 prefixEnd_1144057 391634091427290403617389 := by
  unfold tailWord_1144057
  simp only [CollatzResearch.WordTrace]
  refine ⟨41727186816284353224966425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27818124544189568816644283 41727186816284353224966425)
  ·
    refine ⟨31295390112213264918724819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41727186816284353224966425 31295390112213264918724819)
    ·
      refine ⟨46943085168319897378087229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31295390112213264918724819 46943085168319897378087229)
      ·
        refine ⟨17603656938119961516782711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46943085168319897378087229 17603656938119961516782711)
        ·
          refine ⟨26405485407179942275174067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17603656938119961516782711 26405485407179942275174067)
          ·
            refine ⟨39608228110769913412761101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26405485407179942275174067 39608228110769913412761101)
            ·
              refine ⟨14853085541538717529785413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39608228110769913412761101 14853085541538717529785413)
              ·
                refine ⟨2784953539038509536834765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14853085541538717529785413 2784953539038509536834765)
                ·
                  refine ⟨1044357577139441076313037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2784953539038509536834765 1044357577139441076313037)
                  ·
                    refine ⟨391634091427290403617389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1044357577139441076313037 391634091427290403617389)
                    ·
                      rfl

theorem cell22_1144057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 4, 3, 3].length) (baseStart_1144057 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1144057 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1144057 prefixEnd_1144057 := by exact prefixLift 1144057
  have htrace : WordTrace (prefixWord ++ tailWord_1144057) baseStart_1144057 baseEnd_1144057 := by
    simpa [prefixWord, tailWord_1144057, baseEnd_1144057] using wordTrace_append hprefix tailTrace_1144057
  have hstable : (prefixWord ++ tailWord_1144057).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1144057).length < 2 ^ (prefixWord ++ tailWord_1144057).sum := by decide
  have hdescent : baseEnd_1144057 < baseStart_1144057 := by decide
  rcases family_descends (prefixWord ++ tailWord_1144057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1144087 : List Nat := [1, 1, 3, 4, 1, 1, 2, 4, 5]
def baseStart_1144087 : Nat := 118140960795 + 1144087 * 2 ^ 59
def prefixEnd_1144087 : Nat := 4983230072969 + 3 ^ 40 * 1144087 * 2
def baseEnd_1144087 : Nat := 130548120346793441789099

theorem tailTrace_1144087 : CollatzResearch.WordTrace tailWord_1144087 prefixEnd_1144087 130548120346793441789099 := by
  unfold tailWord_1144087
  simp only [CollatzResearch.WordTrace]
  refine ⟨41728281006175668348558515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27818854004117112232372343 41728281006175668348558515)
  ·
    refine ⟨62592421509263502522837773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41728281006175668348558515 62592421509263502522837773)
    ·
      refine ⟨23472158065973813446064165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62592421509263502522837773 23472158065973813446064165)
      ·
        refine ⟨4401029637370090021137031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23472158065973813446064165 4401029637370090021137031)
        ·
          refine ⟨6601544456055135031705547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4401029637370090021137031 6601544456055135031705547)
          ·
            refine ⟨9902316684082702547558321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6601544456055135031705547 9902316684082702547558321)
            ·
              refine ⟨7426737513062026910668741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9902316684082702547558321 7426737513062026910668741)
              ·
                refine ⟨1392513283699130045750389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7426737513062026910668741 1392513283699130045750389)
                ·
                  refine ⟨130548120346793441789099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1392513283699130045750389 130548120346793441789099)
                  ·
                    rfl

theorem cell22_1144087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 2, 4, 5].length) (baseStart_1144087 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1144087 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1144087 prefixEnd_1144087 := by exact prefixLift 1144087
  have htrace : WordTrace (prefixWord ++ tailWord_1144087) baseStart_1144087 baseEnd_1144087 := by
    simpa [prefixWord, tailWord_1144087, baseEnd_1144087] using wordTrace_append hprefix tailTrace_1144087
  have hstable : (prefixWord ++ tailWord_1144087).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1144087).length < 2 ^ (prefixWord ++ tailWord_1144087).sum := by decide
  have hdescent : baseEnd_1144087 < baseStart_1144087 := by decide
  rcases family_descends (prefixWord ++ tailWord_1144087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1144104 : List Nat := [2, 1, 5, 1, 2, 2, 1, 3, 5]
def baseStart_1144104 : Nat := 118140960795 + 1144104 * 2 ^ 59
def prefixEnd_1144104 : Nat := 4983230072969 + 3 ^ 40 * 1144104 * 2
def baseEnd_1144104 : Nat := 130550060162599315897415

theorem tailTrace_1144104 : CollatzResearch.WordTrace tailWord_1144104 prefixEnd_1144104 130550060162599315897415 := by
  unfold tailWord_1144104
  simp only [CollatzResearch.WordTrace]
  refine ⟨20864450523557040125963683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27819267364742720167951577 20864450523557040125963683)
  ·
    refine ⟨31296675785335560188945525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20864450523557040125963683 31296675785335560188945525)
    ·
      refine ⟨2934063354875208767713643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 31296675785335560188945525 2934063354875208767713643)
      ·
        refine ⟨4401095032312813151570465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2934063354875208767713643 4401095032312813151570465)
        ·
          refine ⟨3300821274234609863677849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4401095032312813151570465 3300821274234609863677849)
          ·
            refine ⟨2475615955675957397758387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3300821274234609863677849 2475615955675957397758387)
            ·
              refine ⟨3713423933513936096637581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2475615955675957397758387 3713423933513936096637581)
              ·
                refine ⟨1392533975067726036239093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3713423933513936096637581 1392533975067726036239093)
                ·
                  refine ⟨130550060162599315897415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1392533975067726036239093 130550060162599315897415)
                  ·
                    rfl

theorem cell22_1144104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 1, 3, 5].length) (baseStart_1144104 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1144104 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1144104 prefixEnd_1144104 := by exact prefixLift 1144104
  have htrace : WordTrace (prefixWord ++ tailWord_1144104) baseStart_1144104 baseEnd_1144104 := by
    simpa [prefixWord, tailWord_1144104, baseEnd_1144104] using wordTrace_append hprefix tailTrace_1144104
  have hstable : (prefixWord ++ tailWord_1144104).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1144104).length < 2 ^ (prefixWord ++ tailWord_1144104).sum := by decide
  have hdescent : baseEnd_1144104 < baseStart_1144104 := by decide
  rcases family_descends (prefixWord ++ tailWord_1144104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1144164 : List Nat := [2, 3, 1, 1, 3, 3, 2, 1, 1, 5]
def baseStart_1144164 : Nat := 118140960795 + 1144164 * 2 ^ 59
def prefixEnd_1144164 : Nat := 4983230072969 + 3 ^ 40 * 1144164 * 2
def baseEnd_1144164 : Nat := 391670719713977791192061

theorem tailTrace_1144164 : CollatzResearch.WordTrace tailWord_1144164 prefixEnd_1144164 391670719713977791192061 := by
  unfold tailWord_1144164
  simp only [CollatzResearch.WordTrace]
  refine ⟨20865544713448355249555773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27820726284597806999407697 20865544713448355249555773)
  ·
    refine ⟨7824579267543133218583415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20865544713448355249555773 7824579267543133218583415)
    ·
      refine ⟨11736868901314699827875123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7824579267543133218583415 11736868901314699827875123)
      ·
        refine ⟨17605303351972049741812685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11736868901314699827875123 17605303351972049741812685)
        ·
          refine ⟨6601988756989518653179757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17605303351972049741812685 6601988756989518653179757)
          ·
            refine ⟨2475745783871069494942409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6601988756989518653179757 2475745783871069494942409)
            ·
              refine ⟨1856809337903302121206807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2475745783871069494942409 1856809337903302121206807)
              ·
                refine ⟨2785214006854953181810211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1856809337903302121206807 2785214006854953181810211)
                ·
                  refine ⟨4177821010282429772715317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2785214006854953181810211 4177821010282429772715317)
                  ·
                    refine ⟨391670719713977791192061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4177821010282429772715317 391670719713977791192061)
                    ·
                      rfl

theorem cell22_1144164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 2, 1, 1, 5].length) (baseStart_1144164 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1144164 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1144164 prefixEnd_1144164 := by exact prefixLift 1144164
  have htrace : WordTrace (prefixWord ++ tailWord_1144164) baseStart_1144164 baseEnd_1144164 := by
    simpa [prefixWord, tailWord_1144164, baseEnd_1144164] using wordTrace_append hprefix tailTrace_1144164
  have hstable : (prefixWord ++ tailWord_1144164).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1144164).length < 2 ^ (prefixWord ++ tailWord_1144164).sum := by decide
  have hdescent : baseEnd_1144164 < baseStart_1144164 := by decide
  rcases family_descends (prefixWord ++ tailWord_1144164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1144226 : List Nat := [3, 3, 1, 2, 1, 2, 2, 2, 3, 3]
def baseStart_1144226 : Nat := 118140960795 + 1144226 * 2 ^ 59
def prefixEnd_1144226 : Nat := 4983230072969 + 3 ^ 40 * 1144226 * 2
def baseEnd_1144226 : Nat := 391691943581030296141871

theorem tailTrace_1144226 : CollatzResearch.WordTrace tailWord_1144226 prefixEnd_1144226 391691943581030296141871 := by
  unfold tailWord_1144226
  simp only [CollatzResearch.WordTrace]
  refine ⟨10433337688168023771967133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27822233835114730058579021 10433337688168023771967133)
  ·
    refine ⟨3912501633063008914487675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10433337688168023771967133 3912501633063008914487675)
    ·
      refine ⟨5868752449594513371731513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3912501633063008914487675 5868752449594513371731513)
      ·
        refine ⟨4401564337195885028798635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5868752449594513371731513 4401564337195885028798635)
        ·
          refine ⟨6602346505793827543197953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4401564337195885028798635 6602346505793827543197953)
          ·
            refine ⟨4951759879345370657398465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6602346505793827543197953 4951759879345370657398465)
            ·
              refine ⟨3713819909509027993048849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4951759879345370657398465 3713819909509027993048849)
              ·
                refine ⟨2785364932131770994786637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3713819909509027993048849 2785364932131770994786637)
                ·
                  refine ⟨1044511849549414123044989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2785364932131770994786637 1044511849549414123044989)
                  ·
                    refine ⟨391691943581030296141871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1044511849549414123044989 391691943581030296141871)
                    ·
                      rfl

theorem cell22_1144226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 2, 2, 3, 3].length) (baseStart_1144226 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1144226 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1144226 prefixEnd_1144226 := by exact prefixLift 1144226
  have htrace : WordTrace (prefixWord ++ tailWord_1144226) baseStart_1144226 baseEnd_1144226 := by
    simpa [prefixWord, tailWord_1144226, baseEnd_1144226] using wordTrace_append hprefix tailTrace_1144226
  have hstable : (prefixWord ++ tailWord_1144226).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1144226).length < 2 ^ (prefixWord ++ tailWord_1144226).sum := by decide
  have hdescent : baseEnd_1144226 < baseStart_1144226 := by decide
  rcases family_descends (prefixWord ++ tailWord_1144226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1144297 : List Nat := [1, 2, 1, 1, 1, 2, 1, 2, 5, 6]
def baseStart_1144297 : Nat := 118140960795 + 1144297 * 2 ^ 59
def prefixEnd_1144297 : Nat := 4983230072969 + 3 ^ 40 * 1144297 * 2
def baseEnd_1144297 : Nat := 391716248332009777616653

theorem tailTrace_1144297 : CollatzResearch.WordTrace tailWord_1144297 prefixEnd_1144297 391716248332009777616653 := by
  unfold tailWord_1144297
  simp only [CollatzResearch.WordTrace]
  refine ⟨41735940335414874213703145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27823960223609916142468763 41735940335414874213703145)
  ·
    refine ⟨31301955251561155660277359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41735940335414874213703145 31301955251561155660277359)
    ·
      refine ⟨46952932877341733490416039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31301955251561155660277359 46952932877341733490416039)
      ·
        refine ⟨70429399316012600235624059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46952932877341733490416039 70429399316012600235624059)
        ·
          refine ⟨105644098974018900353436089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70429399316012600235624059 105644098974018900353436089)
          ·
            refine ⟨79233074230514175265077067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 105644098974018900353436089 79233074230514175265077067)
            ·
              refine ⟨118849611345771262897615601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79233074230514175265077067 118849611345771262897615601)
              ·
                refine ⟨89137208509328447173211701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 118849611345771262897615601 89137208509328447173211701)
                ·
                  refine ⟨8356613297749541922488597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 89137208509328447173211701 8356613297749541922488597)
                  ·
                    refine ⟨391716248332009777616653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8356613297749541922488597 391716248332009777616653)
                    ·
                      rfl

theorem cell22_1144297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 2, 5, 6].length) (baseStart_1144297 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1144297 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1144297 prefixEnd_1144297 := by exact prefixLift 1144297
  have htrace : WordTrace (prefixWord ++ tailWord_1144297) baseStart_1144297 baseEnd_1144297 := by
    simpa [prefixWord, tailWord_1144297, baseEnd_1144297] using wordTrace_append hprefix tailTrace_1144297
  have hstable : (prefixWord ++ tailWord_1144297).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1144297).length < 2 ^ (prefixWord ++ tailWord_1144297).sum := by decide
  have hdescent : baseEnd_1144297 < baseStart_1144297 := by decide
  rcases family_descends (prefixWord ++ tailWord_1144297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1144299 : List Nat := [1, 1, 1, 1, 2, 3, 2, 4, 4, 3]
def baseStart_1144299 : Nat := 118140960795 + 1144299 * 2 ^ 59
def prefixEnd_1144299 : Nat := 4983230072969 + 3 ^ 40 * 1144299 * 2
def baseEnd_1144299 : Nat := 391716932972882439066647

theorem tailTrace_1144299 : CollatzResearch.WordTrace tailWord_1144299 prefixEnd_1144299 391716932972882439066647 := by
  unfold tailWord_1144299
  simp only [CollatzResearch.WordTrace]
  refine ⟨41736013281407628555275951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27824008854271752370183967 41736013281407628555275951)
  ·
    refine ⟨62604019922111442832913927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41736013281407628555275951 62604019922111442832913927)
    ·
      refine ⟨93906029883167164249370891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62604019922111442832913927 93906029883167164249370891)
      ·
        refine ⟨140859044824750746374056337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93906029883167164249370891 140859044824750746374056337)
        ·
          refine ⟨105644283618563059780542253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 140859044824750746374056337 105644283618563059780542253)
          ·
            refine ⟨39616606356961147417703345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 105644283618563059780542253 39616606356961147417703345)
            ·
              refine ⟨29712454767720860563277509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39616606356961147417703345 29712454767720860563277509)
              ·
                refine ⟨5571085268947661355614533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29712454767720860563277509 5571085268947661355614533)
                ·
                  refine ⟨1044578487927686504177725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5571085268947661355614533 1044578487927686504177725)
                  ·
                    refine ⟨391716932972882439066647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1044578487927686504177725 391716932972882439066647)
                    ·
                      rfl

theorem cell22_1144299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 4, 4, 3].length) (baseStart_1144299 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1144299 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1144299 prefixEnd_1144299 := by exact prefixLift 1144299
  have htrace : WordTrace (prefixWord ++ tailWord_1144299) baseStart_1144299 baseEnd_1144299 := by
    simpa [prefixWord, tailWord_1144299, baseEnd_1144299] using wordTrace_append hprefix tailTrace_1144299
  have hstable : (prefixWord ++ tailWord_1144299).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1144299).length < 2 ^ (prefixWord ++ tailWord_1144299).sum := by decide
  have hdescent : baseEnd_1144299 < baseStart_1144299 := by decide
  rcases family_descends (prefixWord ++ tailWord_1144299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1144312 : List Nat := [2, 1, 2, 1, 1, 15]
def baseStart_1144312 : Nat := 118140960795 + 1144312 * 2 ^ 59
def prefixEnd_1144312 : Nat := 4983230072969 + 3 ^ 40 * 1144312 * 2
def baseEnd_1144312 : Nat := 4836066458500675783847

theorem tailTrace_1144312 : CollatzResearch.WordTrace tailWord_1144312 prefixEnd_1144312 4836066458500675783847 := by
  unfold tailWord_1144312
  simp only [CollatzResearch.WordTrace]
  refine ⟨20868243715180265887749595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27824324953573687850332793 20868243715180265887749595)
  ·
    refine ⟨31302365572770398831624393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20868243715180265887749595 31302365572770398831624393)
    ·
      refine ⟨23476774179577799123718295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31302365572770398831624393 23476774179577799123718295)
      ·
        refine ⟨35215161269366698685577443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23476774179577799123718295 35215161269366698685577443)
        ·
          refine ⟨52822741904050048028366165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35215161269366698685577443 52822741904050048028366165)
          ·
            refine ⟨4836066458500675783847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 15 52822741904050048028366165 4836066458500675783847)
            ·
              rfl

theorem cell22_1144312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 15].length) (baseStart_1144312 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1144312 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1144312 prefixEnd_1144312 := by exact prefixLift 1144312
  have htrace : WordTrace (prefixWord ++ tailWord_1144312) baseStart_1144312 baseEnd_1144312 := by
    simpa [prefixWord, tailWord_1144312, baseEnd_1144312] using wordTrace_append hprefix tailTrace_1144312
  have hstable : (prefixWord ++ tailWord_1144312).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1144312).length < 2 ^ (prefixWord ++ tailWord_1144312).sum := by decide
  have hdescent : baseEnd_1144312 < baseStart_1144312 := by decide
  rcases family_descends (prefixWord ++ tailWord_1144312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1144314 : List Nat := [3, 1, 1, 1, 1, 2, 3, 4, 2, 4]
def baseStart_1144314 : Nat := 118140960795 + 1144314 * 2 ^ 59
def prefixEnd_1144314 : Nat := 4983230072969 + 3 ^ 40 * 1144314 * 2
def baseEnd_1144314 : Nat := 391722067779427399941601

theorem tailTrace_1144314 : CollatzResearch.WordTrace tailWord_1144314 prefixEnd_1144314 391722067779427399941601 := by
  unfold tailWord_1144314
  simp only [CollatzResearch.WordTrace]
  refine ⟨10434140094088321529267999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27824373584235524078047997 10434140094088321529267999)
  ·
    refine ⟨15651210141132482293901999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10434140094088321529267999 15651210141132482293901999)
    ·
      refine ⟨23476815211698723440852999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15651210141132482293901999 23476815211698723440852999)
      ·
        refine ⟨35215222817548085161279499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23476815211698723440852999 35215222817548085161279499)
        ·
          refine ⟨52822834226322127741919249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35215222817548085161279499 52822834226322127741919249)
          ·
            refine ⟨39617125669741595806439437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52822834226322127741919249 39617125669741595806439437)
            ·
              refine ⟨14856422126153098427414789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39617125669741595806439437 14856422126153098427414789)
              ·
                refine ⟨2785579148653705955140273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14856422126153098427414789 2785579148653705955140273)
                ·
                  refine ⟨2089184361490279466355205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2785579148653705955140273 2089184361490279466355205)
                  ·
                    refine ⟨391722067779427399941601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2089184361490279466355205 391722067779427399941601)
                    ·
                      rfl

theorem cell22_1144314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 4, 2, 4].length) (baseStart_1144314 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1144314 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1144314 prefixEnd_1144314 := by exact prefixLift 1144314
  have htrace : WordTrace (prefixWord ++ tailWord_1144314) baseStart_1144314 baseEnd_1144314 := by
    simpa [prefixWord, tailWord_1144314, baseEnd_1144314] using wordTrace_append hprefix tailTrace_1144314
  have hstable : (prefixWord ++ tailWord_1144314).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1144314).length < 2 ^ (prefixWord ++ tailWord_1144314).sum := by decide
  have hdescent : baseEnd_1144314 < baseStart_1144314 := by decide
  rcases family_descends (prefixWord ++ tailWord_1144314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1144316 : List Nat := [2, 2, 2, 1, 2, 1, 3, 4, 2, 3]
def baseStart_1144316 : Nat := 118140960795 + 1144316 * 2 ^ 59
def prefixEnd_1144316 : Nat := 4983230072969 + 3 ^ 40 * 1144316 * 2
def baseEnd_1144316 : Nat := 391722752420300061391595

theorem tailTrace_1144316 : CollatzResearch.WordTrace tailWord_1144316 prefixEnd_1144316 391722752420300061391595 := by
  unfold tailWord_1144316
  simp only [CollatzResearch.WordTrace]
  refine ⟨20868316661173020229322401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27824422214897360305763201 20868316661173020229322401)
  ·
    refine ⟨15651237495879765171991801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20868316661173020229322401 15651237495879765171991801)
    ·
      refine ⟨11738428121909823878993851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15651237495879765171991801 11738428121909823878993851)
      ·
        refine ⟨17607642182864735818490777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11738428121909823878993851 17607642182864735818490777)
        ·
          refine ⟨13205731637148551863868083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17607642182864735818490777 13205731637148551863868083)
          ·
            refine ⟨19808597455722827795802125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13205731637148551863868083 19808597455722827795802125)
            ·
              refine ⟨7428224045896060423425797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19808597455722827795802125 7428224045896060423425797)
              ·
                refine ⟨1392792008605511329392337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7428224045896060423425797 1392792008605511329392337)
                ·
                  refine ⟨1044594006454133497044253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1392792008605511329392337 1044594006454133497044253)
                  ·
                    refine ⟨391722752420300061391595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1044594006454133497044253 391722752420300061391595)
                    ·
                      rfl

theorem cell22_1144316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 3, 4, 2, 3].length) (baseStart_1144316 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1144316 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1144316 prefixEnd_1144316 := by exact prefixLift 1144316
  have htrace : WordTrace (prefixWord ++ tailWord_1144316) baseStart_1144316 baseEnd_1144316 := by
    simpa [prefixWord, tailWord_1144316, baseEnd_1144316] using wordTrace_append hprefix tailTrace_1144316
  have hstable : (prefixWord ++ tailWord_1144316).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1144316).length < 2 ^ (prefixWord ++ tailWord_1144316).sum := by decide
  have hdescent : baseEnd_1144316 < baseStart_1144316 := by decide
  rcases family_descends (prefixWord ++ tailWord_1144316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1144378 : List Nat := [3, 1, 1, 1, 3, 2, 1, 6, 1, 3]
def baseStart_1144378 : Nat := 118140960795 + 1144378 * 2 ^ 59
def prefixEnd_1144378 : Nat := 4983230072969 + 3 ^ 40 * 1144378 * 2
def baseEnd_1144378 : Nat := 391743976287352566341405

theorem tailTrace_1144378 : CollatzResearch.WordTrace tailWord_1144378 prefixEnd_1144378 391743976287352566341405 := by
  unfold tailWord_1144378
  simp only [CollatzResearch.WordTrace]
  refine ⟨10434723662030356261850447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27825929765414283364934525 10434723662030356261850447)
  ·
    refine ⟨15652085493045534392775671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10434723662030356261850447 15652085493045534392775671)
    ·
      refine ⟨23478128239568301589163507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15652085493045534392775671 23478128239568301589163507)
      ·
        refine ⟨35217192359352452383745261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23478128239568301589163507 35217192359352452383745261)
        ·
          refine ⟨13206447134757169643904473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35217192359352452383745261 13206447134757169643904473)
          ·
            refine ⟨9904835351067877232928355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13206447134757169643904473 9904835351067877232928355)
            ·
              refine ⟨14857253026601815849392533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9904835351067877232928355 14857253026601815849392533)
              ·
                refine ⟨696433735621960117940275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 14857253026601815849392533 696433735621960117940275)
                ·
                  refine ⟨1044650603432940176910413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 696433735621960117940275 1044650603432940176910413)
                  ·
                    refine ⟨391743976287352566341405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1044650603432940176910413 391743976287352566341405)
                    ·
                      rfl

theorem cell22_1144378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 6, 1, 3].length) (baseStart_1144378 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1144378 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1144378 prefixEnd_1144378 := by exact prefixLift 1144378
  have htrace : WordTrace (prefixWord ++ tailWord_1144378) baseStart_1144378 baseEnd_1144378 := by
    simpa [prefixWord, tailWord_1144378, baseEnd_1144378] using wordTrace_append hprefix tailTrace_1144378
  have hstable : (prefixWord ++ tailWord_1144378).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1144378).length < 2 ^ (prefixWord ++ tailWord_1144378).sum := by decide
  have hdescent : baseEnd_1144378 < baseStart_1144378 := by decide
  rcases family_descends (prefixWord ++ tailWord_1144378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1144389 : List Nat := [1, 3, 1, 1, 1, 4, 1, 3, 2, 5]
def baseStart_1144389 : Nat := 118140960795 + 1144389 * 2 ^ 59
def prefixEnd_1144389 : Nat := 4983230072969 + 3 ^ 40 * 1144389 * 2
def baseEnd_1144389 : Nat := 391747741812152204316371

theorem tailTrace_1144389 : CollatzResearch.WordTrace tailWord_1144389 prefixEnd_1144389 391747741812152204316371 := by
  unfold tailWord_1144389
  simp only [CollatzResearch.WordTrace]
  refine ⟨41739295851081573926052221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27826197234054382617368147 41739295851081573926052221)
  ·
    refine ⟨15652235944155590222269583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41739295851081573926052221 15652235944155590222269583)
    ·
      refine ⟨23478353916233385333404375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15652235944155590222269583 23478353916233385333404375)
      ·
        refine ⟨35217530874350078000106563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23478353916233385333404375 35217530874350078000106563)
        ·
          refine ⟨52826296311525117000159845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35217530874350078000106563 52826296311525117000159845)
          ·
            refine ⟨9904930558410959437529971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 52826296311525117000159845 9904930558410959437529971)
            ·
              refine ⟨14857395837616439156294957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9904930558410959437529971 14857395837616439156294957)
              ·
                refine ⟨5571523439106164683610609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14857395837616439156294957 5571523439106164683610609)
                ·
                  refine ⟨4178642579329623512707957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5571523439106164683610609 4178642579329623512707957)
                  ·
                    refine ⟨391747741812152204316371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4178642579329623512707957 391747741812152204316371)
                    ·
                      rfl

theorem cell22_1144389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 3, 2, 5].length) (baseStart_1144389 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1144389 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1144389 prefixEnd_1144389 := by exact prefixLift 1144389
  have htrace : WordTrace (prefixWord ++ tailWord_1144389) baseStart_1144389 baseEnd_1144389 := by
    simpa [prefixWord, tailWord_1144389, baseEnd_1144389] using wordTrace_append hprefix tailTrace_1144389
  have hstable : (prefixWord ++ tailWord_1144389).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1144389).length < 2 ^ (prefixWord ++ tailWord_1144389).sum := by decide
  have hdescent : baseEnd_1144389 < baseStart_1144389 := by decide
  rcases family_descends (prefixWord ++ tailWord_1144389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1144412 : List Nat := [2, 2, 4, 1, 2, 3, 1, 3, 1, 3]
def baseStart_1144412 : Nat := 118140960795 + 1144412 * 2 ^ 59
def prefixEnd_1144412 : Nat := 4983230072969 + 3 ^ 40 * 1144412 * 2
def baseEnd_1144412 : Nat := 391755615182187810991301

theorem tailTrace_1144412 : CollatzResearch.WordTrace tailWord_1144412 prefixEnd_1144412 391755615182187810991301 := by
  unfold tailWord_1144412
  simp only [CollatzResearch.WordTrace]
  refine ⟨20870067364999124427069745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27826756486665499236092993 20870067364999124427069745)
  ·
    refine ⟨15652550523749343320302309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20870067364999124427069745 15652550523749343320302309)
    ·
      refine ⟨2934853223203001872556683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15652550523749343320302309 2934853223203001872556683)
      ·
        refine ⟨4402279834804502808835025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2934853223203001872556683 4402279834804502808835025)
        ·
          refine ⟨3301709876103377106626269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4402279834804502808835025 3301709876103377106626269)
          ·
            refine ⟨1238141203538766414984851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3301709876103377106626269 1238141203538766414984851)
            ·
              refine ⟨1857211805308149622477277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1238141203538766414984851 1857211805308149622477277)
              ·
                refine ⟨696454426990556108428979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1857211805308149622477277 696454426990556108428979)
                ·
                  refine ⟨1044681640485834162643469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 696454426990556108428979 1044681640485834162643469)
                  ·
                    refine ⟨391755615182187810991301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1044681640485834162643469 391755615182187810991301)
                    ·
                      rfl

theorem cell22_1144412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 3, 1, 3, 1, 3].length) (baseStart_1144412 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1144412 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1144412 prefixEnd_1144412 := by exact prefixLift 1144412
  have htrace : WordTrace (prefixWord ++ tailWord_1144412) baseStart_1144412 baseEnd_1144412 := by
    simpa [prefixWord, tailWord_1144412, baseEnd_1144412] using wordTrace_append hprefix tailTrace_1144412
  have hstable : (prefixWord ++ tailWord_1144412).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1144412).length < 2 ^ (prefixWord ++ tailWord_1144412).sum := by decide
  have hdescent : baseEnd_1144412 < baseStart_1144412 := by decide
  rcases family_descends (prefixWord ++ tailWord_1144412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1144502 : List Nat := [5, 1, 3, 1, 1, 1, 2, 3, 2, 3]
def baseStart_1144502 : Nat := 118140960795 + 1144502 * 2 ^ 59
def prefixEnd_1144502 : Nat := 4983230072969 + 3 ^ 40 * 1144502 * 2
def baseEnd_1144502 : Nat := 391786424021457576241025

theorem tailTrace_1144502 : CollatzResearch.WordTrace tailWord_1144502 prefixEnd_1144502 391786424021457576241025 := by
  unfold tailWord_1144502
  simp only [CollatzResearch.WordTrace]
  refine ⟨2608963581229512139057235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 27828944866448129483277173 2608963581229512139057235)
  ·
    refine ⟨3913445371844268208585853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2608963581229512139057235 3913445371844268208585853)
    ·
      refine ⟨1467542014441600578219695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3913445371844268208585853 1467542014441600578219695)
      ·
        refine ⟨2201313021662400867329543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1467542014441600578219695 2201313021662400867329543)
        ·
          refine ⟨3301969532493601300994315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2201313021662400867329543 3301969532493601300994315)
          ·
            refine ⟨4952954298740401951491473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3301969532493601300994315 4952954298740401951491473)
            ·
              refine ⟨3714715724055301463618605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4952954298740401951491473 3714715724055301463618605)
              ·
                refine ⟨1393018396520738048856977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3714715724055301463618605 1393018396520738048856977)
                ·
                  refine ⟨1044763797390553536642733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1393018396520738048856977 1044763797390553536642733)
                  ·
                    refine ⟨391786424021457576241025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1044763797390553536642733 391786424021457576241025)
                    ·
                      rfl

theorem cell22_1144502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 2, 3, 2, 3].length) (baseStart_1144502 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1144502 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1144502 prefixEnd_1144502 := by exact prefixLift 1144502
  have htrace : WordTrace (prefixWord ++ tailWord_1144502) baseStart_1144502 baseEnd_1144502 := by
    simpa [prefixWord, tailWord_1144502, baseEnd_1144502] using wordTrace_append hprefix tailTrace_1144502
  have hstable : (prefixWord ++ tailWord_1144502).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1144502).length < 2 ^ (prefixWord ++ tailWord_1144502).sum := by decide
  have hdescent : baseEnd_1144502 < baseStart_1144502 := by decide
  rcases family_descends (prefixWord ++ tailWord_1144502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1144526 : List Nat := [4, 1, 1, 1, 3, 1, 2, 2, 7]
def baseStart_1144526 : Nat := 118140960795 + 1144526 * 2 ^ 59
def prefixEnd_1144526 : Nat := 4983230072969 + 3 ^ 40 * 1144526 * 2
def baseEnd_1144526 : Nat := 130598213237309837880317

theorem tailTrace_1144526 : CollatzResearch.WordTrace tailWord_1144526 prefixEnd_1144526 130598213237309837880317 := by
  unfold tailWord_1144526
  simp only [CollatzResearch.WordTrace]
  refine ⟨5218036581448155790473679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27829528434390164215859621 5218036581448155790473679)
  ·
    refine ⟨7827054872172233685710519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5218036581448155790473679 7827054872172233685710519)
    ·
      refine ⟨11740582308258350528565779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7827054872172233685710519 11740582308258350528565779)
      ·
        refine ⟨17610873462387525792848669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11740582308258350528565779 17610873462387525792848669)
        ·
          refine ⟨6604077548395322172318251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17610873462387525792848669 6604077548395322172318251)
          ·
            refine ⟨9906116322592983258477377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6604077548395322172318251 9906116322592983258477377)
            ·
              refine ⟨7429587241944737443858033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9906116322592983258477377 7429587241944737443858033)
              ·
                refine ⟨5572190431458553082893525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7429587241944737443858033 5572190431458553082893525)
                ·
                  refine ⟨130598213237309837880317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5572190431458553082893525 130598213237309837880317)
                  ·
                    rfl

theorem cell22_1144526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 2, 2, 7].length) (baseStart_1144526 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1144526 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1144526 prefixEnd_1144526 := by exact prefixLift 1144526
  have htrace : WordTrace (prefixWord ++ tailWord_1144526) baseStart_1144526 baseEnd_1144526 := by
    simpa [prefixWord, tailWord_1144526, baseEnd_1144526] using wordTrace_append hprefix tailTrace_1144526
  have hstable : (prefixWord ++ tailWord_1144526).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1144526).length < 2 ^ (prefixWord ++ tailWord_1144526).sum := by decide
  have hdescent : baseEnd_1144526 < baseStart_1144526 := by decide
  rcases family_descends (prefixWord ++ tailWord_1144526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1144556 : List Nat := [2, 2, 1, 1, 2, 2, 2, 1, 5, 4]
def baseStart_1144556 : Nat := 118140960795 + 1144556 * 2 ^ 59
def prefixEnd_1144556 : Nat := 4983230072969 + 3 ^ 40 * 1144556 * 2
def baseEnd_1144556 : Nat := 391804909325019435390859

theorem tailTrace_1144556 : CollatzResearch.WordTrace tailWord_1144556 prefixEnd_1144556 391804909325019435390859 := by
  unfold tailWord_1144556
  simp only [CollatzResearch.WordTrace]
  refine ⟨20872693420738280723690761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27830257894317707631587681 20872693420738280723690761)
  ·
    refine ⟨15654520065553710542768071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20872693420738280723690761 15654520065553710542768071)
    ·
      refine ⟨23481780098330565814152107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15654520065553710542768071 23481780098330565814152107)
      ·
        refine ⟨35222670147495848721228161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23481780098330565814152107 35222670147495848721228161)
        ·
          refine ⟨26417002610621886540921121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35222670147495848721228161 26417002610621886540921121)
          ·
            refine ⟨19812751957966414905690841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26417002610621886540921121 19812751957966414905690841)
            ·
              refine ⟨14859563968474811179268131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19812751957966414905690841 14859563968474811179268131)
              ·
                refine ⟨22289345952712216768902197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14859563968474811179268131 22289345952712216768902197)
                ·
                  refine ⟨2089626183066770322084581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 22289345952712216768902197 2089626183066770322084581)
                  ·
                    refine ⟨391804909325019435390859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2089626183066770322084581 391804909325019435390859)
                    ·
                      rfl

theorem cell22_1144556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 4].length) (baseStart_1144556 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1144556 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1144556 prefixEnd_1144556 := by exact prefixLift 1144556
  have htrace : WordTrace (prefixWord ++ tailWord_1144556) baseStart_1144556 baseEnd_1144556 := by
    simpa [prefixWord, tailWord_1144556, baseEnd_1144556] using wordTrace_append hprefix tailTrace_1144556
  have hstable : (prefixWord ++ tailWord_1144556).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1144556).length < 2 ^ (prefixWord ++ tailWord_1144556).sum := by decide
  have hdescent : baseEnd_1144556 < baseStart_1144556 := by decide
  rcases family_descends (prefixWord ++ tailWord_1144556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1144620 : List Nat := [2, 2, 1, 1, 1, 6, 1, 3, 2, 3]
def baseStart_1144620 : Nat := 118140960795 + 1144620 * 2 ^ 59
def prefixEnd_1144620 : Nat := 4983230072969 + 3 ^ 40 * 1144620 * 2
def baseEnd_1144620 : Nat := 391826817832944601790663

theorem tailTrace_1144620 : CollatzResearch.WordTrace tailWord_1144620 prefixEnd_1144620 391826817832944601790663 := by
  unfold tailWord_1144620
  simp only [CollatzResearch.WordTrace]
  refine ⟨20873860556622350188855657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27831814075496466918474209 20873860556622350188855657)
  ·
    refine ⟨15655395417466762641641743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20873860556622350188855657 15655395417466762641641743)
    ·
      refine ⟨23483093126200143962462615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15655395417466762641641743 23483093126200143962462615)
      ·
        refine ⟨35224639689300215943693923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23483093126200143962462615 35224639689300215943693923)
        ·
          refine ⟨52836959533950323915540885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35224639689300215943693923 52836959533950323915540885)
          ·
            refine ⟨2476732478153921433540979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 52836959533950323915540885 2476732478153921433540979)
            ·
              refine ⟨3715098717230882150311469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2476732478153921433540979 3715098717230882150311469)
              ·
                refine ⟨1393162018961580806366801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3715098717230882150311469 1393162018961580806366801)
                ·
                  refine ⟨1044871514221185604775101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1393162018961580806366801 1044871514221185604775101)
                  ·
                    refine ⟨391826817832944601790663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1044871514221185604775101 391826817832944601790663)
                    ·
                      rfl

theorem cell22_1144620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 2, 3].length) (baseStart_1144620 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1144620 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1144620 prefixEnd_1144620 := by exact prefixLift 1144620
  have htrace : WordTrace (prefixWord ++ tailWord_1144620) baseStart_1144620 baseEnd_1144620 := by
    simpa [prefixWord, tailWord_1144620, baseEnd_1144620] using wordTrace_append hprefix tailTrace_1144620
  have hstable : (prefixWord ++ tailWord_1144620).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1144620).length < 2 ^ (prefixWord ++ tailWord_1144620).sum := by decide
  have hdescent : baseEnd_1144620 < baseStart_1144620 := by decide
  rcases family_descends (prefixWord ++ tailWord_1144620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1144693 : List Nat := [1, 3, 4, 1, 1, 1, 1, 2, 1, 7]
def baseStart_1144693 : Nat := 118140960795 + 1144693 * 2 ^ 59
def prefixEnd_1144693 : Nat := 4983230072969 + 3 ^ 40 * 1144693 * 2
def baseEnd_1144693 : Nat := 391851807224796744715439

theorem tailTrace_1144693 : CollatzResearch.WordTrace tailWord_1144693 prefixEnd_1144693 391851807224796744715439 := by
  unfold tailWord_1144693
  simp only [CollatzResearch.WordTrace]
  refine ⟨41750383641980233845118733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27833589094653489230079155 41750383641980233845118733)
  ·
    refine ⟨15656393865742587691919525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41750383641980233845118733 15656393865742587691919525)
    ·
      refine ⟨2935573849826735192234911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15656393865742587691919525 2935573849826735192234911)
      ·
        refine ⟨4403360774740102788352367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2935573849826735192234911 4403360774740102788352367)
        ·
          refine ⟨6605041162110154182528551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4403360774740102788352367 6605041162110154182528551)
          ·
            refine ⟨9907561743165231273792827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6605041162110154182528551 9907561743165231273792827)
            ·
              refine ⟨14861342614747846910689241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9907561743165231273792827 14861342614747846910689241)
              ·
                refine ⟨11146006961060885183016931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14861342614747846910689241 11146006961060885183016931)
                ·
                  refine ⟨16719010441591327774525397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11146006961060885183016931 16719010441591327774525397)
                  ·
                    refine ⟨391851807224796744715439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 16719010441591327774525397 391851807224796744715439)
                    ·
                      rfl

theorem cell22_1144693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 2, 1, 7].length) (baseStart_1144693 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1144693 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1144693 prefixEnd_1144693 := by exact prefixLift 1144693
  have htrace : WordTrace (prefixWord ++ tailWord_1144693) baseStart_1144693 baseEnd_1144693 := by
    simpa [prefixWord, tailWord_1144693, baseEnd_1144693] using wordTrace_append hprefix tailTrace_1144693
  have hstable : (prefixWord ++ tailWord_1144693).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1144693).length < 2 ^ (prefixWord ++ tailWord_1144693).sum := by decide
  have hdescent : baseEnd_1144693 < baseStart_1144693 := by decide
  rcases family_descends (prefixWord ++ tailWord_1144693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1144712 : List Nat := [2, 1, 3, 3, 3, 2, 1, 2, 5]
def baseStart_1144712 : Nat := 118140960795 + 1144712 * 2 ^ 59
def prefixEnd_1144712 : Nat := 4983230072969 + 3 ^ 40 * 1144712 * 2
def baseEnd_1144712 : Nat := 130619437104362342830127

theorem tailTrace_1144712 : CollatzResearch.WordTrace tailWord_1144712 prefixEnd_1144712 130619437104362342830127 := by
  unfold tailWord_1144712
  simp only [CollatzResearch.WordTrace]
  refine ⟨20875538314455700045030195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27834051085940933393373593 20875538314455700045030195)
  ·
    refine ⟨31313307471683550067545293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20875538314455700045030195 31313307471683550067545293)
    ·
      refine ⟨11742490301881331275329485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31313307471683550067545293 11742490301881331275329485)
      ·
        refine ⟨4403433863205499228248557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11742490301881331275329485 4403433863205499228248557)
        ·
          refine ⟨1651287698702062210593209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4403433863205499228248557 1651287698702062210593209)
          ·
            refine ⟨1238465774026546657944907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1651287698702062210593209 1238465774026546657944907)
            ·
              refine ⟨1857698661039819986917361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1238465774026546657944907 1857698661039819986917361)
              ·
                refine ⟨1393273995779864990188021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1857698661039819986917361 1393273995779864990188021)
                ·
                  refine ⟨130619437104362342830127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1393273995779864990188021 130619437104362342830127)
                  ·
                    rfl

theorem cell22_1144712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 2, 1, 2, 5].length) (baseStart_1144712 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1144712 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1144712 prefixEnd_1144712 := by exact prefixLift 1144712
  have htrace : WordTrace (prefixWord ++ tailWord_1144712) baseStart_1144712 baseEnd_1144712 := by
    simpa [prefixWord, tailWord_1144712, baseEnd_1144712] using wordTrace_append hprefix tailTrace_1144712
  have hstable : (prefixWord ++ tailWord_1144712).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1144712).length < 2 ^ (prefixWord ++ tailWord_1144712).sum := by decide
  have hdescent : baseEnd_1144712 < baseStart_1144712 := by decide
  rcases family_descends (prefixWord ++ tailWord_1144712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1144750 : List Nat := [4, 1, 5, 1, 1, 2, 1, 3, 1, 3]
def baseStart_1144750 : Nat := 118140960795 + 1144750 * 2 ^ 59
def prefixEnd_1144750 : Nat := 4983230072969 + 3 ^ 40 * 1144750 * 2
def baseEnd_1144750 : Nat := 391871319489667596040265

theorem tailTrace_1144750 : CollatzResearch.WordTrace tailWord_1144750 prefixEnd_1144750 391871319489667596040265 := by
  unfold tailWord_1144750
  simp only [CollatzResearch.WordTrace]
  refine ⟨5219057825346716572492963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27834975068515821719962469 5219057825346716572492963)
  ·
    refine ⟨7828586738020074858739445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5219057825346716572492963 7828586738020074858739445)
    ·
      refine ⟨733930006689382018006823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 7828586738020074858739445 733930006689382018006823)
      ·
        refine ⟨1100895010034073027010235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 733930006689382018006823 1100895010034073027010235)
        ·
          refine ⟨1651342515051109540515353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1100895010034073027010235 1651342515051109540515353)
          ·
            refine ⟨1238506886288332155386515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1651342515051109540515353 1238506886288332155386515)
            ·
              refine ⟨1857760329432498233079773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1238506886288332155386515 1857760329432498233079773)
              ·
                refine ⟨696660123537186837404915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1857760329432498233079773 696660123537186837404915)
                ·
                  refine ⟨1044990185305780256107373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 696660123537186837404915 1044990185305780256107373)
                  ·
                    refine ⟨391871319489667596040265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1044990185305780256107373 391871319489667596040265)
                    ·
                      rfl

theorem cell22_1144750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 2, 1, 3, 1, 3].length) (baseStart_1144750 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1144750 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1144750 prefixEnd_1144750 := by exact prefixLift 1144750
  have htrace : WordTrace (prefixWord ++ tailWord_1144750) baseStart_1144750 baseEnd_1144750 := by
    simpa [prefixWord, tailWord_1144750, baseEnd_1144750] using wordTrace_append hprefix tailTrace_1144750
  have hstable : (prefixWord ++ tailWord_1144750).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1144750).length < 2 ^ (prefixWord ++ tailWord_1144750).sum := by decide
  have hdescent : baseEnd_1144750 < baseStart_1144750 := by decide
  rcases family_descends (prefixWord ++ tailWord_1144750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1144757 : List Nat := [1, 3, 3, 2, 1, 2, 3, 3, 4]
def baseStart_1144757 : Nat := 118140960795 + 1144757 * 2 ^ 59
def prefixEnd_1144757 : Nat := 4983230072969 + 3 ^ 40 * 1144757 * 2
def baseEnd_1144757 : Nat := 130624571910907303705081

theorem tailTrace_1144757 : CollatzResearch.WordTrace tailWord_1144757 prefixEnd_1144757 130624571910907303705081 := by
  unfold tailWord_1144757
  simp only [CollatzResearch.WordTrace]
  refine ⟨41752717913748372775448525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27835145275832248516965683 41752717913748372775448525)
  ·
    refine ⟨15657269217655639790793197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41752717913748372775448525 15657269217655639790793197)
    ·
      refine ⟨5871475956620864921547449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15657269217655639790793197 5871475956620864921547449)
      ·
        refine ⟨4403606967465648691160587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5871475956620864921547449 4403606967465648691160587)
        ·
          refine ⟨6605410451198473036740881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4403606967465648691160587 6605410451198473036740881)
          ·
            refine ⟨4954057838398854777555661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6605410451198473036740881 4954057838398854777555661)
            ·
              refine ⟨1857771689399570541583373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4954057838398854777555661 1857771689399570541583373)
              ·
                refine ⟨696664383524838953093765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1857771689399570541583373 696664383524838953093765)
                ·
                  refine ⟨130624571910907303705081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 696664383524838953093765 130624571910907303705081)
                  ·
                    rfl

theorem cell22_1144757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 3, 3, 4].length) (baseStart_1144757 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1144757 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1144757 prefixEnd_1144757 := by exact prefixLift 1144757
  have htrace : WordTrace (prefixWord ++ tailWord_1144757) baseStart_1144757 baseEnd_1144757 := by
    simpa [prefixWord, tailWord_1144757, baseEnd_1144757] using wordTrace_append hprefix tailTrace_1144757
  have hstable : (prefixWord ++ tailWord_1144757).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1144757).length < 2 ^ (prefixWord ++ tailWord_1144757).sum := by decide
  have hdescent : baseEnd_1144757 < baseStart_1144757 := by decide
  rcases family_descends (prefixWord ++ tailWord_1144757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1144789 : List Nat := [1, 3, 2, 3, 2, 1, 4, 1, 2, 3]
def baseStart_1144789 : Nat := 118140960795 + 1144789 * 2 ^ 59
def prefixEnd_1144789 : Nat := 4983230072969 + 3 ^ 40 * 1144789 * 2
def baseEnd_1144789 : Nat := 391884669986684494315145

theorem tailTrace_1144789 : CollatzResearch.WordTrace tailWord_1144789 prefixEnd_1144789 391884669986684494315145 := by
  unfold tailWord_1144789
  simp only [CollatzResearch.WordTrace]
  refine ⟨41753885049632442240613421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27835923366421628160408947 41753885049632442240613421)
  ·
    refine ⟨15657706893612165840230033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41753885049632442240613421 15657706893612165840230033)
    ·
      refine ⟨11743280170209124380172525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15657706893612165840230033 11743280170209124380172525)
      ·
        refine ⟨4403730063828421642564697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11743280170209124380172525 4403730063828421642564697)
        ·
          refine ⟨3302797547871316231923523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4403730063828421642564697 3302797547871316231923523)
          ·
            refine ⟨4954196321806974347885285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3302797547871316231923523 4954196321806974347885285)
            ·
              refine ⟨928911810338807690228491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4954196321806974347885285 928911810338807690228491)
              ·
                refine ⟨1393367715508211535342737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 928911810338807690228491 1393367715508211535342737)
                ·
                  refine ⟨1045025786631158651507053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1393367715508211535342737 1045025786631158651507053)
                  ·
                    refine ⟨391884669986684494315145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1045025786631158651507053 391884669986684494315145)
                    ·
                      rfl

theorem cell22_1144789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 4, 1, 2, 3].length) (baseStart_1144789 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1144789 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1144789 prefixEnd_1144789 := by exact prefixLift 1144789
  have htrace : WordTrace (prefixWord ++ tailWord_1144789) baseStart_1144789 baseEnd_1144789 := by
    simpa [prefixWord, tailWord_1144789, baseEnd_1144789] using wordTrace_append hprefix tailTrace_1144789
  have hstable : (prefixWord ++ tailWord_1144789).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1144789).length < 2 ^ (prefixWord ++ tailWord_1144789).sum := by decide
  have hdescent : baseEnd_1144789 < baseStart_1144789 := by decide
  rcases family_descends (prefixWord ++ tailWord_1144789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1144800 : List Nat := [2, 1, 1, 3, 1, 1, 1, 6, 3, 3]
def baseStart_1144800 : Nat := 118140960795 + 1144800 * 2 ^ 59
def prefixEnd_1144800 : Nat := 4983230072969 + 3 ^ 40 * 1144800 * 2
def baseEnd_1144800 : Nat := 391888435511484132290111

theorem tailTrace_1144800 : CollatzResearch.WordTrace tailWord_1144800 prefixEnd_1144800 391888435511484132290111 := by
  unfold tailWord_1144800
  simp only [CollatzResearch.WordTrace]
  refine ⟨20877143126296295559631927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27836190835061727412842569 20877143126296295559631927)
  ·
    refine ⟨31315714689444443339447891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20877143126296295559631927 31315714689444443339447891)
    ·
      refine ⟨46973572034166665009171837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31315714689444443339447891 46973572034166665009171837)
      ·
        refine ⟨17615089512812499378439439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46973572034166665009171837 17615089512812499378439439)
        ·
          refine ⟨26422634269218749067659159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17615089512812499378439439 26422634269218749067659159)
          ·
            refine ⟨39633951403828123601488739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26422634269218749067659159 39633951403828123601488739)
            ·
              refine ⟨59450927105742185402233109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39633951403828123601488739 59450927105742185402233109)
              ·
                refine ⟨2786762208081664940729677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 59450927105742185402233109 2786762208081664940729677)
                ·
                  refine ⟨1045035828030624352773629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2786762208081664940729677 1045035828030624352773629)
                  ·
                    refine ⟨391888435511484132290111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1045035828030624352773629 391888435511484132290111)
                    ·
                      rfl

theorem cell22_1144800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 6, 3, 3].length) (baseStart_1144800 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1144800 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1144800 prefixEnd_1144800 := by exact prefixLift 1144800
  have htrace : WordTrace (prefixWord ++ tailWord_1144800) baseStart_1144800 baseEnd_1144800 := by
    simpa [prefixWord, tailWord_1144800, baseEnd_1144800] using wordTrace_append hprefix tailTrace_1144800
  have hstable : (prefixWord ++ tailWord_1144800).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1144800).length < 2 ^ (prefixWord ++ tailWord_1144800).sum := by decide
  have hdescent : baseEnd_1144800 < baseStart_1144800 := by decide
  rcases family_descends (prefixWord ++ tailWord_1144800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1144873 : List Nat := [1, 2, 1, 1, 1, 1, 1, 1, 4, 9]
def baseStart_1144873 : Nat := 118140960795 + 1144873 * 2 ^ 59
def prefixEnd_1144873 : Nat := 4983230072969 + 3 ^ 40 * 1144873 * 2
def baseEnd_1144873 : Nat := 391913424903336275214887

theorem tailTrace_1144873 : CollatzResearch.WordTrace tailWord_1144873 prefixEnd_1144873 391913424903336275214887 := by
  unfold tailWord_1144873
  simp only [CollatzResearch.WordTrace]
  refine ⟨41756948781328124586671273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27837965854218749724447515 41756948781328124586671273)
  ·
    refine ⟨31317711585996093440003455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41756948781328124586671273 31317711585996093440003455)
    ·
      refine ⟨46976567378994140160005183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31317711585996093440003455 46976567378994140160005183)
      ·
        refine ⟨70464851068491210240007775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46976567378994140160005183 70464851068491210240007775)
        ·
          refine ⟨105697276602736815360011663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70464851068491210240007775 105697276602736815360011663)
          ·
            refine ⟨158545914904105223040017495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 105697276602736815360011663 158545914904105223040017495)
            ·
              refine ⟨237818872356157834560026243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 158545914904105223040017495 237818872356157834560026243)
              ·
                refine ⟨356728308534236751840039365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 237818872356157834560026243 356728308534236751840039365)
                ·
                  refine ⟨66886557850169390970007381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 356728308534236751840039365 66886557850169390970007381)
                  ·
                    refine ⟨391913424903336275214887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 66886557850169390970007381 391913424903336275214887)
                    ·
                      rfl

theorem cell22_1144873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 4, 9].length) (baseStart_1144873 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1144873 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1144873 prefixEnd_1144873 := by exact prefixLift 1144873
  have htrace : WordTrace (prefixWord ++ tailWord_1144873) baseStart_1144873 baseEnd_1144873 := by
    simpa [prefixWord, tailWord_1144873, baseEnd_1144873] using wordTrace_append hprefix tailTrace_1144873
  have hstable : (prefixWord ++ tailWord_1144873).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1144873).length < 2 ^ (prefixWord ++ tailWord_1144873).sum := by decide
  have hdescent : baseEnd_1144873 < baseStart_1144873 := by decide
  rcases family_descends (prefixWord ++ tailWord_1144873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1144892 : List Nat := [2, 2, 2, 2, 2, 1, 1, 6, 4]
def baseStart_1144892 : Nat := 118140960795 + 1144892 * 2 ^ 59
def prefixEnd_1144892 : Nat := 4983230072969 + 3 ^ 40 * 1144892 * 2
def baseEnd_1144892 : Nat := 130639976330542186329943

theorem tailTrace_1144892 : CollatzResearch.WordTrace tailWord_1144892 prefixEnd_1144892 130639976330542186329943 := by
  unfold tailWord_1144892
  simp only [CollatzResearch.WordTrace]
  refine ⟨20878820884129645415806465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27838427845506193887741953 20878820884129645415806465)
  ·
    refine ⟨15659115663097234061854849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20878820884129645415806465 15659115663097234061854849)
    ·
      refine ⟨11744336747322925546391137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15659115663097234061854849 11744336747322925546391137)
      ·
        refine ⟨8808252560492194159793353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11744336747322925546391137 8808252560492194159793353)
        ·
          refine ⟨6606189420369145619845015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8808252560492194159793353 6606189420369145619845015)
          ·
            refine ⟨9909284130553718429767523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6606189420369145619845015 9909284130553718429767523)
            ·
              refine ⟨14863926195830577644651285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9909284130553718429767523 14863926195830577644651285)
              ·
                refine ⟨696746540429558327093029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 14863926195830577644651285 696746540429558327093029)
                ·
                  refine ⟨130639976330542186329943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 696746540429558327093029 130639976330542186329943)
                  ·
                    rfl

theorem cell22_1144892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 6, 4].length) (baseStart_1144892 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1144892 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1144892 prefixEnd_1144892 := by exact prefixLift 1144892
  have htrace : WordTrace (prefixWord ++ tailWord_1144892) baseStart_1144892 baseEnd_1144892 := by
    simpa [prefixWord, tailWord_1144892, baseEnd_1144892] using wordTrace_append hprefix tailTrace_1144892
  have hstable : (prefixWord ++ tailWord_1144892).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1144892).length < 2 ^ (prefixWord ++ tailWord_1144892).sum := by decide
  have hdescent : baseEnd_1144892 < baseStart_1144892 := by decide
  rcases family_descends (prefixWord ++ tailWord_1144892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1144920 : List Nat := [2, 1, 2, 2, 1, 5, 1, 8]
def baseStart_1144920 : Nat := 118140960795 + 1144920 * 2 ^ 59
def prefixEnd_1144920 : Nat := 4983230072969 + 3 ^ 40 * 1144920 * 2
def baseEnd_1144920 : Nat := 43547723773760424365527

theorem tailTrace_1144920 : CollatzResearch.WordTrace tailWord_1144920 prefixEnd_1144920 43547723773760424365527 := by
  unfold tailWord_1144920
  simp only [CollatzResearch.WordTrace]
  refine ⟨20879331506078925806816107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27839108674771901075754809 20879331506078925806816107)
  ·
    refine ⟨31318997259118388710224161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20879331506078925806816107 31318997259118388710224161)
    ·
      refine ⟨23489247944338791532668121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31318997259118388710224161 23489247944338791532668121)
      ·
        refine ⟨17616935958254093649501091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23489247944338791532668121 17616935958254093649501091)
        ·
          refine ⟨26425403937381140474251637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17616935958254093649501091 26425403937381140474251637)
          ·
            refine ⟨2477381619129481919461091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 26425403937381140474251637 2477381619129481919461091)
            ·
              refine ⟨3716072428694222879191637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2477381619129481919461091 3716072428694222879191637)
              ·
                refine ⟨43547723773760424365527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3716072428694222879191637 43547723773760424365527)
                ·
                  rfl

theorem cell22_1144920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 1, 8].length) (baseStart_1144920 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1144920 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1144920 prefixEnd_1144920 := by exact prefixLift 1144920
  have htrace : WordTrace (prefixWord ++ tailWord_1144920) baseStart_1144920 baseEnd_1144920 := by
    simpa [prefixWord, tailWord_1144920, baseEnd_1144920] using wordTrace_append hprefix tailTrace_1144920
  have hstable : (prefixWord ++ tailWord_1144920).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1144920).length < 2 ^ (prefixWord ++ tailWord_1144920).sum := by decide
  have hdescent : baseEnd_1144920 < baseStart_1144920 := by decide
  rcases family_descends (prefixWord ++ tailWord_1144920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1145057 : List Nat := [1, 2, 3, 1, 3, 1, 2, 1, 4, 4]
def baseStart_1145057 : Nat := 118140960795 + 1145057 * 2 ^ 59
def prefixEnd_1145057 : Nat := 4983230072969 + 3 ^ 40 * 1145057 * 2
def baseEnd_1145057 : Nat := 391976411863621128614323

theorem tailTrace_1145057 : CollatzResearch.WordTrace tailWord_1145057 prefixEnd_1145057 391976411863621128614323 := by
  unfold tailWord_1145057
  simp only [CollatzResearch.WordTrace]
  refine ⟨41763659812661524011369425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27842439875107682674246283 41763659812661524011369425)
  ·
    refine ⟨31322744859496143008527069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41763659812661524011369425 31322744859496143008527069)
    ·
      refine ⟨11746029322311053628197651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31322744859496143008527069 11746029322311053628197651)
      ·
        refine ⟨17619043983466580442296477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11746029322311053628197651 17619043983466580442296477)
        ·
          refine ⟨6607141493799967665861179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17619043983466580442296477 6607141493799967665861179)
          ·
            refine ⟨9910712240699951498791769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6607141493799967665861179 9910712240699951498791769)
            ·
              refine ⟨7433034180524963624093827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9910712240699951498791769 7433034180524963624093827)
              ·
                refine ⟨11149551270787445436140741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7433034180524963624093827 11149551270787445436140741)
                ·
                  refine ⟨2090540863272646019276389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11149551270787445436140741 2090540863272646019276389)
                  ·
                    refine ⟨391976411863621128614323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2090540863272646019276389 391976411863621128614323)
                    ·
                      rfl

theorem cell22_1145057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 2, 1, 4, 4].length) (baseStart_1145057 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1145057 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1145057 prefixEnd_1145057 := by exact prefixLift 1145057
  have htrace : WordTrace (prefixWord ++ tailWord_1145057) baseStart_1145057 baseEnd_1145057 := by
    simpa [prefixWord, tailWord_1145057, baseEnd_1145057] using wordTrace_append hprefix tailTrace_1145057
  have hstable : (prefixWord ++ tailWord_1145057).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1145057).length < 2 ^ (prefixWord ++ tailWord_1145057).sum := by decide
  have hdescent : baseEnd_1145057 < baseStart_1145057 := by decide
  rcases family_descends (prefixWord ++ tailWord_1145057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1145095 : List Nat := [1, 1, 4, 5, 2, 1, 1, 3, 4]
def baseStart_1145095 : Nat := 118140960795 + 1145095 * 2 ^ 59
def prefixEnd_1145095 : Nat := 4983230072969 + 3 ^ 40 * 1145095 * 2
def baseEnd_1145095 : Nat := 130663140013400565388069

theorem tailTrace_1145095 : CollatzResearch.WordTrace tailWord_1145095 prefixEnd_1145095 130663140013400565388069 := by
  unfold tailWord_1145095
  simp only [CollatzResearch.WordTrace]
  refine ⟨41765045786523856501252739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27843363857682571000835159 41765045786523856501252739)
  ·
    refine ⟨62647568679785784751879109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41765045786523856501252739 62647568679785784751879109)
    ·
      refine ⟨11746419127459834640977333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 62647568679785784751879109 11746419127459834640977333)
      ·
        refine ⟨1101226793199359497591625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 11746419127459834640977333 1101226793199359497591625)
        ·
          refine ⟨825920094899519623193719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1101226793199359497591625 825920094899519623193719)
          ·
            refine ⟨1238880142349279434790579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 825920094899519623193719 1238880142349279434790579)
            ·
              refine ⟨1858320213523919152185869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1238880142349279434790579 1858320213523919152185869)
              ·
                refine ⟨696870080071469682069701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1858320213523919152185869 696870080071469682069701)
                ·
                  refine ⟨130663140013400565388069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 696870080071469682069701 130663140013400565388069)
                  ·
                    rfl

theorem cell22_1145095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 2, 1, 1, 3, 4].length) (baseStart_1145095 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1145095 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1145095 prefixEnd_1145095 := by exact prefixLift 1145095
  have htrace : WordTrace (prefixWord ++ tailWord_1145095) baseStart_1145095 baseEnd_1145095 := by
    simpa [prefixWord, tailWord_1145095, baseEnd_1145095] using wordTrace_append hprefix tailTrace_1145095
  have hstable : (prefixWord ++ tailWord_1145095).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1145095).length < 2 ^ (prefixWord ++ tailWord_1145095).sum := by decide
  have hdescent : baseEnd_1145095 < baseStart_1145095 := by decide
  rcases family_descends (prefixWord ++ tailWord_1145095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1145121 : List Nat := [1, 2, 3, 2, 1, 1, 2, 6, 1, 3]
def baseStart_1145121 : Nat := 118140960795 + 1145121 * 2 ^ 59
def prefixEnd_1145121 : Nat := 4983230072969 + 3 ^ 40 * 1145121 * 2
def baseEnd_1145121 : Nat := 391998320371546295014127

theorem tailTrace_1145121 : CollatzResearch.WordTrace tailWord_1145121 prefixEnd_1145121 391998320371546295014127 := by
  unfold tailWord_1145121
  simp only [CollatzResearch.WordTrace]
  refine ⟨41765994084429662941699217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27843996056286441961132811 41765994084429662941699217)
  ·
    refine ⟨31324495563322247206274413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41765994084429662941699217 31324495563322247206274413)
    ·
      refine ⟨11746685836245842702352905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31324495563322247206274413 11746685836245842702352905)
      ·
        refine ⟨8810014377184382026764679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11746685836245842702352905 8810014377184382026764679)
        ·
          refine ⟨13215021565776573040147019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8810014377184382026764679 13215021565776573040147019)
          ·
            refine ⟨19822532348664859560220529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13215021565776573040147019 19822532348664859560220529)
            ·
              refine ⟨14866899261498644670165397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19822532348664859560220529 14866899261498644670165397)
              ·
                refine ⟨696885902882748968914003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 14866899261498644670165397 696885902882748968914003)
                ·
                  refine ⟨1045328854324123453371005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 696885902882748968914003 1045328854324123453371005)
                  ·
                    refine ⟨391998320371546295014127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1045328854324123453371005 391998320371546295014127)
                    ·
                      rfl

theorem cell22_1145121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 6, 1, 3].length) (baseStart_1145121 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1145121 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1145121 prefixEnd_1145121 := by exact prefixLift 1145121
  have htrace : WordTrace (prefixWord ++ tailWord_1145121) baseStart_1145121 baseEnd_1145121 := by
    simpa [prefixWord, tailWord_1145121, baseEnd_1145121] using wordTrace_append hprefix tailTrace_1145121
  have hstable : (prefixWord ++ tailWord_1145121).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1145121).length < 2 ^ (prefixWord ++ tailWord_1145121).sum := by decide
  have hdescent : baseEnd_1145121 < baseStart_1145121 := by decide
  rcases family_descends (prefixWord ++ tailWord_1145121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1145132 : List Nat := [2, 2, 1, 1, 1, 3, 2, 3, 2, 5]
def baseStart_1145132 : Nat := 118140960795 + 1145132 * 2 ^ 59
def prefixEnd_1145132 : Nat := 4983230072969 + 3 ^ 40 * 1145132 * 2
def baseEnd_1145132 : Nat := 392002085896345932989093

theorem tailTrace_1145132 : CollatzResearch.WordTrace tailWord_1145132 prefixEnd_1145132 392002085896345932989093 := by
  unfold tailWord_1145132
  simp only [CollatzResearch.WordTrace]
  refine ⟨20883197643694905910174825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27844263524926541213566433 20883197643694905910174825)
  ·
    refine ⟨15662398232771179432631119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20883197643694905910174825 15662398232771179432631119)
    ·
      refine ⟨23493597349156769148946679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15662398232771179432631119 23493597349156769148946679)
      ·
        refine ⟨35240396023735153723420019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23493597349156769148946679 35240396023735153723420019)
        ·
          refine ⟨52860594035602730585130029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35240396023735153723420019 52860594035602730585130029)
          ·
            refine ⟨19822722763351023969423761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52860594035602730585130029 19822722763351023969423761)
            ·
              refine ⟨14867042072513267977067821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19822722763351023969423761 14867042072513267977067821)
              ·
                refine ⟨5575140777192475491400433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14867042072513267977067821 5575140777192475491400433)
                ·
                  refine ⟨4181355582894356618550325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5575140777192475491400433 4181355582894356618550325)
                  ·
                    refine ⟨392002085896345932989093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4181355582894356618550325 392002085896345932989093)
                    ·
                      rfl

theorem cell22_1145132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 5].length) (baseStart_1145132 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1145132 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1145132 prefixEnd_1145132 := by exact prefixLift 1145132
  have htrace : WordTrace (prefixWord ++ tailWord_1145132) baseStart_1145132 baseEnd_1145132 := by
    simpa [prefixWord, tailWord_1145132, baseEnd_1145132] using wordTrace_append hprefix tailTrace_1145132
  have hstable : (prefixWord ++ tailWord_1145132).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1145132).length < 2 ^ (prefixWord ++ tailWord_1145132).sum := by decide
  have hdescent : baseEnd_1145132 < baseStart_1145132 := by decide
  rcases family_descends (prefixWord ++ tailWord_1145132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1145177 : List Nat := [1, 2, 1, 2, 2, 2, 1, 1, 5, 5]
def baseStart_1145177 : Nat := 118140960795 + 1145177 * 2 ^ 59
def prefixEnd_1145177 : Nat := 4983230072969 + 3 ^ 40 * 1145177 * 2
def baseEnd_1145177 : Nat := 392017490315980815613955

theorem tailTrace_1145177 : CollatzResearch.WordTrace tailWord_1145177 prefixEnd_1145177 392017490315980815613955 := by
  unfold tailWord_1145177
  simp only [CollatzResearch.WordTrace]
  refine ⟨41768036572226784505737785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27845357714817856337158523 41768036572226784505737785)
  ·
    refine ⟨31326027429170088379303339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41768036572226784505737785 31326027429170088379303339)
    ·
      refine ⟨46989041143755132568955009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31326027429170088379303339 46989041143755132568955009)
      ·
        refine ⟨35241780857816349426716257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46989041143755132568955009 35241780857816349426716257)
        ·
          refine ⟨26431335643362262070037193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35241780857816349426716257 26431335643362262070037193)
          ·
            refine ⟨19823501732521696552527895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26431335643362262070037193 19823501732521696552527895)
            ·
              refine ⟨29735252598782544828791843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19823501732521696552527895 29735252598782544828791843)
              ·
                refine ⟨44602878898173817243187765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29735252598782544828791843 44602878898173817243187765)
                ·
                  refine ⟨4181519896703795366548853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 44602878898173817243187765 4181519896703795366548853)
                  ·
                    refine ⟨392017490315980815613955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4181519896703795366548853 392017490315980815613955)
                    ·
                      rfl

theorem cell22_1145177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 1, 5, 5].length) (baseStart_1145177 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1145177 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1145177 prefixEnd_1145177 := by exact prefixLift 1145177
  have htrace : WordTrace (prefixWord ++ tailWord_1145177) baseStart_1145177 baseEnd_1145177 := by
    simpa [prefixWord, tailWord_1145177, baseEnd_1145177] using wordTrace_append hprefix tailTrace_1145177
  have hstable : (prefixWord ++ tailWord_1145177).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1145177).length < 2 ^ (prefixWord ++ tailWord_1145177).sum := by decide
  have hdescent : baseEnd_1145177 < baseStart_1145177 := by decide
  rcases family_descends (prefixWord ++ tailWord_1145177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1145228 : List Nat := [2, 2, 1, 2, 1, 6, 1, 2, 2, 3]
def baseStart_1145228 : Nat := 118140960795 + 1145228 * 2 ^ 59
def prefixEnd_1145228 : Nat := 4983230072969 + 3 ^ 40 * 1145228 * 2
def baseEnd_1145228 : Nat := 392034948658233682588799

theorem tailTrace_1145228 : CollatzResearch.WordTrace tailWord_1145228 prefixEnd_1145228 392034948658233682588799 := by
  unfold tailWord_1145228
  simp only [CollatzResearch.WordTrace]
  refine ⟨20884948347521010107922169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27846597796694680143896225 20884948347521010107922169)
  ·
    refine ⟨15663711260640757580941627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20884948347521010107922169 15663711260640757580941627)
    ·
      refine ⟨23495566890961136371412441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15663711260640757580941627 23495566890961136371412441)
      ·
        refine ⟨17621675168220852278559331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23495566890961136371412441 17621675168220852278559331)
        ·
          refine ⟨26432512752331278417838997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17621675168220852278559331 26432512752331278417838997)
          ·
            refine ⟨1239024035265528675836203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 26432512752331278417838997 1239024035265528675836203)
            ·
              refine ⟨1858536052898293013754305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1239024035265528675836203 1858536052898293013754305)
              ·
                refine ⟨1393902039673719760315729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1858536052898293013754305 1393902039673719760315729)
                ·
                  refine ⟨1045426529755289820236797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1393902039673719760315729 1045426529755289820236797)
                  ·
                    refine ⟨392034948658233682588799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1045426529755289820236797 392034948658233682588799)
                    ·
                      rfl

theorem cell22_1145228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 6, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 6, 1, 2, 2, 3].length) (baseStart_1145228 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1145228 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1145228 prefixEnd_1145228 := by exact prefixLift 1145228
  have htrace : WordTrace (prefixWord ++ tailWord_1145228) baseStart_1145228 baseEnd_1145228 := by
    simpa [prefixWord, tailWord_1145228, baseEnd_1145228] using wordTrace_append hprefix tailTrace_1145228
  have hstable : (prefixWord ++ tailWord_1145228).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1145228).length < 2 ^ (prefixWord ++ tailWord_1145228).sum := by decide
  have hdescent : baseEnd_1145228 < baseStart_1145228 := by decide
  rcases family_descends (prefixWord ++ tailWord_1145228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1145245 : List Nat := [1, 4, 2, 1, 4, 1, 3, 1, 2, 3]
def baseStart_1145245 : Nat := 118140960795 + 1145245 * 2 ^ 59
def prefixEnd_1145245 : Nat := 4983230072969 + 3 ^ 40 * 1145245 * 2
def baseEnd_1145245 : Nat := 392040768105651304913747

theorem tailTrace_1145245 : CollatzResearch.WordTrace tailWord_1145245 prefixEnd_1145245 392040768105651304913747 := by
  unfold tailWord_1145245
  simp only [CollatzResearch.WordTrace]
  refine ⟨41770516735980432119213189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27847011157320288079475459 41770516735980432119213189)
  ·
    refine ⟨7831971887996331022352473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 41770516735980432119213189 7831971887996331022352473)
    ·
      refine ⟨5873978915997248266764355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7831971887996331022352473 5873978915997248266764355)
      ·
        refine ⟨8810968373995872400146533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5873978915997248266764355 8810968373995872400146533)
        ·
          refine ⟨1652056570124226075027475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8810968373995872400146533 1652056570124226075027475)
          ·
            refine ⟨2478084855186339112541213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1652056570124226075027475 2478084855186339112541213)
            ·
              refine ⟨929281820694877167202955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2478084855186339112541213 929281820694877167202955)
              ·
                refine ⟨1393922731042315750804433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 929281820694877167202955 1393922731042315750804433)
                ·
                  refine ⟨1045442048281736813103325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1393922731042315750804433 1045442048281736813103325)
                  ·
                    refine ⟨392040768105651304913747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1045442048281736813103325 392040768105651304913747)
                    ·
                      rfl

theorem cell22_1145245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 3, 1, 2, 3].length) (baseStart_1145245 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1145245 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1145245 prefixEnd_1145245 := by exact prefixLift 1145245
  have htrace : WordTrace (prefixWord ++ tailWord_1145245) baseStart_1145245 baseEnd_1145245 := by
    simpa [prefixWord, tailWord_1145245, baseEnd_1145245] using wordTrace_append hprefix tailTrace_1145245
  have hstable : (prefixWord ++ tailWord_1145245).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1145245).length < 2 ^ (prefixWord ++ tailWord_1145245).sum := by decide
  have hdescent : baseEnd_1145245 < baseStart_1145245 := by decide
  rcases family_descends (prefixWord ++ tailWord_1145245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1145290 : List Nat := [3, 1, 2, 1, 2, 2, 5, 2, 1, 3]
def baseStart_1145290 : Nat := 118140960795 + 1145290 * 2 ^ 59
def prefixEnd_1145290 : Nat := 4983230072969 + 3 ^ 40 * 1145290 * 2
def baseEnd_1145290 : Nat := 392056172525286187538609

theorem tailTrace_1145290 : CollatzResearch.WordTrace tailWord_1145290 prefixEnd_1145290 392056172525286187538609 := by
  unfold tailWord_1145290
  simp only [CollatzResearch.WordTrace]
  refine ⟨10443039505204351201150331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27848105347211603203067549 10443039505204351201150331)
  ·
    refine ⟨15664559257806526801725497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10443039505204351201150331 15664559257806526801725497)
    ·
      refine ⟨11748419443354895101294123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15664559257806526801725497 11748419443354895101294123)
      ·
        refine ⟨17622629165032342651941185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11748419443354895101294123 17622629165032342651941185)
        ·
          refine ⟨13216971873774256988955889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17622629165032342651941185 13216971873774256988955889)
          ·
            refine ⟨9912728905330692741716917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13216971873774256988955889 9912728905330692741716917)
            ·
              refine ⟨929318334874752444535961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9912728905330692741716917 929318334874752444535961)
              ·
                refine ⟨696988751156064333401971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 929318334874752444535961 696988751156064333401971)
                ·
                  refine ⟨1045483126734096500102957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 696988751156064333401971 1045483126734096500102957)
                  ·
                    refine ⟨392056172525286187538609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1045483126734096500102957 392056172525286187538609)
                    ·
                      rfl

theorem cell22_1145290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 5, 2, 1, 3].length) (baseStart_1145290 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1145290 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1145290 prefixEnd_1145290 := by exact prefixLift 1145290
  have htrace : WordTrace (prefixWord ++ tailWord_1145290) baseStart_1145290 baseEnd_1145290 := by
    simpa [prefixWord, tailWord_1145290, baseEnd_1145290] using wordTrace_append hprefix tailTrace_1145290
  have hstable : (prefixWord ++ tailWord_1145290).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1145290).length < 2 ^ (prefixWord ++ tailWord_1145290).sum := by decide
  have hdescent : baseEnd_1145290 < baseStart_1145290 := by decide
  rcases family_descends (prefixWord ++ tailWord_1145290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1145331 : List Nat := [1, 1, 1, 2, 2, 2, 4, 5, 4]
def baseStart_1145331 : Nat := 118140960795 + 1145331 * 2 ^ 59
def prefixEnd_1145331 : Nat := 4983230072969 + 3 ^ 40 * 1145331 * 2
def baseEnd_1145331 : Nat := 130690069221058582421161

theorem tailTrace_1145331 : CollatzResearch.WordTrace tailWord_1145331 prefixEnd_1145331 130690069221058582421161 := by
  unfold tailWord_1145331
  simp only [CollatzResearch.WordTrace]
  refine ⟨41773653413668868806843847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27849102275779245871229231 41773653413668868806843847)
  ·
    refine ⟨62660480120503303210265771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41773653413668868806843847 62660480120503303210265771)
    ·
      refine ⟨93990720180754954815398657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62660480120503303210265771 93990720180754954815398657)
      ·
        refine ⟨70493040135566216111548993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93990720180754954815398657 70493040135566216111548993)
        ·
          refine ⟨52869780101674662083661745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70493040135566216111548993 52869780101674662083661745)
          ·
            refine ⟨39652335076255996562746309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52869780101674662083661745 39652335076255996562746309)
            ·
              refine ⟨7434812826797999355514933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 39652335076255996562746309 7434812826797999355514933)
              ·
                refine ⟨697013702512312439579525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7434812826797999355514933 697013702512312439579525)
                ·
                  refine ⟨130690069221058582421161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 697013702512312439579525 130690069221058582421161)
                  ·
                    rfl

theorem cell22_1145331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 4, 5, 4].length) (baseStart_1145331 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1145331 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1145331 prefixEnd_1145331 := by exact prefixLift 1145331
  have htrace : WordTrace (prefixWord ++ tailWord_1145331) baseStart_1145331 baseEnd_1145331 := by
    simpa [prefixWord, tailWord_1145331, baseEnd_1145331] using wordTrace_append hprefix tailTrace_1145331
  have hstable : (prefixWord ++ tailWord_1145331).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1145331).length < 2 ^ (prefixWord ++ tailWord_1145331).sum := by decide
  have hdescent : baseEnd_1145331 < baseStart_1145331 := by decide
  rcases family_descends (prefixWord ++ tailWord_1145331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1145414 : List Nat := [6, 1, 1, 1, 2, 2, 3, 1, 2, 3]
def baseStart_1145414 : Nat := 118140960795 + 1145414 * 2 ^ 59
def prefixEnd_1145414 : Nat := 4983230072969 + 3 ^ 40 * 1145414 * 2
def baseEnd_1145414 : Nat := 392098620259391197438229

theorem tailTrace_1145414 : CollatzResearch.WordTrace tailWord_1145414 prefixEnd_1145414 392098620259391197438229 := by
  unfold tailWord_1145414
  simp only [CollatzResearch.WordTrace]
  refine ⟨1305521271011505436941103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 27851120448245449321410197 1305521271011505436941103)
  ·
    refine ⟨1958281906517258155411655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1305521271011505436941103 1958281906517258155411655)
    ·
      refine ⟨2937422859775887233117483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1958281906517258155411655 2937422859775887233117483)
      ·
        refine ⟨4406134289663830849676225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2937422859775887233117483 4406134289663830849676225)
        ·
          refine ⟨3304600717247873137257169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4406134289663830849676225 3304600717247873137257169)
          ·
            refine ⟨2478450537935904852942877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3304600717247873137257169 2478450537935904852942877)
            ·
              refine ⟨929418951725964319853579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2478450537935904852942877 929418951725964319853579)
              ·
                refine ⟨1394128427588946479780369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 929418951725964319853579 1394128427588946479780369)
                ·
                  refine ⟨1045596320691709859835277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1394128427588946479780369 1045596320691709859835277)
                  ·
                    refine ⟨392098620259391197438229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1045596320691709859835277 392098620259391197438229)
                    ·
                      rfl

theorem cell22_1145414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 3, 1, 2, 3].length) (baseStart_1145414 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1145414 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1145414 prefixEnd_1145414 := by exact prefixLift 1145414
  have htrace : WordTrace (prefixWord ++ tailWord_1145414) baseStart_1145414 baseEnd_1145414 := by
    simpa [prefixWord, tailWord_1145414, baseEnd_1145414] using wordTrace_append hprefix tailTrace_1145414
  have hstable : (prefixWord ++ tailWord_1145414).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1145414).length < 2 ^ (prefixWord ++ tailWord_1145414).sum := by decide
  have hdescent : baseEnd_1145414 < baseStart_1145414 := by decide
  rcases family_descends (prefixWord ++ tailWord_1145414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1145481 : List Nat := [1, 2, 1, 1, 4, 1, 1, 5, 1, 5]
def baseStart_1145481 : Nat := 118140960795 + 1145481 * 2 ^ 59
def prefixEnd_1145481 : Nat := 4983230072969 + 3 ^ 40 * 1145481 * 2
def baseEnd_1145481 : Nat := 392121555728625356013023

theorem tailTrace_1145481 : CollatzResearch.WordTrace tailWord_1145481 prefixEnd_1145481 392121555728625356013023 := by
  unfold tailWord_1145481
  simp only [CollatzResearch.WordTrace]
  refine ⟨41779124363125444424804297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27852749575416962949869531 41779124363125444424804297)
  ·
    refine ⟨31334343272344083318603223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41779124363125444424804297 31334343272344083318603223)
    ·
      refine ⟨47001514908516124977904835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31334343272344083318603223 47001514908516124977904835)
      ·
        refine ⟨70502272362774187466857253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47001514908516124977904835 70502272362774187466857253)
        ·
          refine ⟨13219176068020160150035735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 70502272362774187466857253 13219176068020160150035735)
          ·
            refine ⟨19828764102030240225053603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13219176068020160150035735 19828764102030240225053603)
            ·
              refine ⟨29743146153045360337580405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19828764102030240225053603 29743146153045360337580405)
              ·
                refine ⟨2788419951848002531648163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 29743146153045360337580405 2788419951848002531648163)
                ·
                  refine ⟨4182629927772003797472245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2788419951848002531648163 4182629927772003797472245)
                  ·
                    refine ⟨392121555728625356013023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4182629927772003797472245 392121555728625356013023)
                    ·
                      rfl

theorem cell22_1145481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 5, 1, 5].length) (baseStart_1145481 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1145481 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1145481 prefixEnd_1145481 := by exact prefixLift 1145481
  have htrace : WordTrace (prefixWord ++ tailWord_1145481) baseStart_1145481 baseEnd_1145481 := by
    simpa [prefixWord, tailWord_1145481, baseEnd_1145481] using wordTrace_append hprefix tailTrace_1145481
  have hstable : (prefixWord ++ tailWord_1145481).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1145481).length < 2 ^ (prefixWord ++ tailWord_1145481).sum := by decide
  have hdescent : baseEnd_1145481 < baseStart_1145481 := by decide
  rcases family_descends (prefixWord ++ tailWord_1145481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1145502 : List Nat := [4, 3, 1, 1, 1, 1, 5, 1, 1, 4]
def baseStart_1145502 : Nat := 118140960795 + 1145502 * 2 ^ 59
def prefixEnd_1145502 : Nat := 4983230072969 + 3 ^ 40 * 1145502 * 2
def baseEnd_1145502 : Nat := 392128744457788301237959

theorem tailTrace_1145502 : CollatzResearch.WordTrace tailWord_1145502 prefixEnd_1145502 392128744457788301237959 := by
  unfold tailWord_1145502
  simp only [CollatzResearch.WordTrace]
  refine ⟨5222486287006170626414845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27853260197366243340879173 5222486287006170626414845)
  ·
    refine ⟨1958432357627313984905567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5222486287006170626414845 1958432357627313984905567)
    ·
      refine ⟨2937648536440970977358351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1958432357627313984905567 2937648536440970977358351)
      ·
        refine ⟨4406472804661456466037527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2937648536440970977358351 4406472804661456466037527)
        ·
          refine ⟨6609709206992184699056291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4406472804661456466037527 6609709206992184699056291)
          ·
            refine ⟨9914563810488277048584437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6609709206992184699056291 9914563810488277048584437)
            ·
              refine ⟨929490357233275973304791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9914563810488277048584437 929490357233275973304791)
              ·
                refine ⟨1394235535849913959957187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 929490357233275973304791 1394235535849913959957187)
                ·
                  refine ⟨2091353303774870939935781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1394235535849913959957187 2091353303774870939935781)
                  ·
                    refine ⟨392128744457788301237959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2091353303774870939935781 392128744457788301237959)
                    ·
                      rfl

theorem cell22_1145502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 5, 1, 1, 4].length) (baseStart_1145502 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1145502 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1145502 prefixEnd_1145502 := by exact prefixLift 1145502
  have htrace : WordTrace (prefixWord ++ tailWord_1145502) baseStart_1145502 baseEnd_1145502 := by
    simpa [prefixWord, tailWord_1145502, baseEnd_1145502] using wordTrace_append hprefix tailTrace_1145502
  have hstable : (prefixWord ++ tailWord_1145502).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1145502).length < 2 ^ (prefixWord ++ tailWord_1145502).sum := by decide
  have hdescent : baseEnd_1145502 < baseStart_1145502 := by decide
  rcases family_descends (prefixWord ++ tailWord_1145502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1145517 : List Nat := [1, 5, 2, 1, 1, 2, 4, 2, 4]
def baseStart_1145517 : Nat := 118140960795 + 1145517 * 2 ^ 59
def prefixEnd_1145517 : Nat := 4983230072969 + 3 ^ 40 * 1145517 * 2
def baseEnd_1145517 : Nat := 130711293088111087370971

theorem tailTrace_1145517 : CollatzResearch.WordTrace tailWord_1145517 prefixEnd_1145517 130711293088111087370971 := by
  unfold tailWord_1145517
  simp only [CollatzResearch.WordTrace]
  refine ⟨41780437390995022573114805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27853624927330015048743203 41780437390995022573114805)
  ·
    refine ⟨3916916005405783366229513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 41780437390995022573114805 3916916005405783366229513)
    ·
      refine ⟨2937687004054337524672135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3916916005405783366229513 2937687004054337524672135)
      ·
        refine ⟨4406530506081506287008203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2937687004054337524672135 4406530506081506287008203)
        ·
          refine ⟨6609795759122259430512305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4406530506081506287008203 6609795759122259430512305)
          ·
            refine ⟨4957346819341694572884229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6609795759122259430512305 4957346819341694572884229)
            ·
              refine ⟨929502528626567732415793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4957346819341694572884229 929502528626567732415793)
              ·
                refine ⟨697126896469925799311845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 929502528626567732415793 697126896469925799311845)
                ·
                  refine ⟨130711293088111087370971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 697126896469925799311845 130711293088111087370971)
                  ·
                    rfl

theorem cell22_1145517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 4, 2, 4].length) (baseStart_1145517 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1145517 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1145517 prefixEnd_1145517 := by exact prefixLift 1145517
  have htrace : WordTrace (prefixWord ++ tailWord_1145517) baseStart_1145517 baseEnd_1145517 := by
    simpa [prefixWord, tailWord_1145517, baseEnd_1145517] using wordTrace_append hprefix tailTrace_1145517
  have hstable : (prefixWord ++ tailWord_1145517).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1145517).length < 2 ^ (prefixWord ++ tailWord_1145517).sum := by decide
  have hdescent : baseEnd_1145517 < baseStart_1145517 := by decide
  rcases family_descends (prefixWord ++ tailWord_1145517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1145573 : List Nat := [1, 3, 1, 4, 1, 3, 1, 1, 7]
def baseStart_1145573 : Nat := 118140960795 + 1145573 * 2 ^ 59
def prefixEnd_1145573 : Nat := 4983230072969 + 3 ^ 40 * 1145573 * 2
def baseEnd_1145573 : Nat := 130717683069589260904247

theorem tailTrace_1145573 : CollatzResearch.WordTrace tailWord_1145573 prefixEnd_1145573 130717683069589260904247 := by
  unfold tailWord_1145573
  simp only [CollatzResearch.WordTrace]
  refine ⟨41782479878792144137153373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27854986585861429424768915 41782479878792144137153373)
  ·
    refine ⟨15668429954547054051432515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41782479878792144137153373 15668429954547054051432515)
    ·
      refine ⟨23502644931820581077148773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15668429954547054051432515 23502644931820581077148773)
      ·
        refine ⟨4406745924716358951965395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23502644931820581077148773 4406745924716358951965395)
        ·
          refine ⟨6610118887074538427948093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4406745924716358951965395 6610118887074538427948093)
          ·
            refine ⟨2478794582652951910480535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6610118887074538427948093 2478794582652951910480535)
            ·
              refine ⟨3718191873979427865720803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2478794582652951910480535 3718191873979427865720803)
              ·
                refine ⟨5577287810969141798581205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3718191873979427865720803 5577287810969141798581205)
                ·
                  refine ⟨130717683069589260904247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5577287810969141798581205 130717683069589260904247)
                  ·
                    rfl

theorem cell22_1145573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 1, 1, 7].length) (baseStart_1145573 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1145573 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1145573 prefixEnd_1145573 := by exact prefixLift 1145573
  have htrace : WordTrace (prefixWord ++ tailWord_1145573) baseStart_1145573 baseEnd_1145573 := by
    simpa [prefixWord, tailWord_1145573, baseEnd_1145573] using wordTrace_append hprefix tailTrace_1145573
  have hstable : (prefixWord ++ tailWord_1145573).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1145573).length < 2 ^ (prefixWord ++ tailWord_1145573).sum := by decide
  have hdescent : baseEnd_1145573 < baseStart_1145573 := by decide
  rcases family_descends (prefixWord ++ tailWord_1145573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1145663 : List Nat := [1, 1, 2, 2, 5, 1, 2, 8]
def baseStart_1145663 : Nat := 118140960795 + 1145663 * 2 ^ 59
def prefixEnd_1145663 : Nat := 4983230072969 + 3 ^ 40 * 1145663 * 2
def baseEnd_1145663 : Nat := 43575984227559727551385

theorem tailTrace_1145663 : CollatzResearch.WordTrace tailWord_1145663 prefixEnd_1145663 43575984227559727551385 := by
  unfold tailWord_1145663
  simp only [CollatzResearch.WordTrace]
  refine ⟨41785762448466089507929643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27857174965644059671953095 41785762448466089507929643)
  ·
    refine ⟨62678643672699134261894465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41785762448466089507929643 62678643672699134261894465)
    ·
      refine ⟨47008982754524350696420849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62678643672699134261894465 47008982754524350696420849)
      ·
        refine ⟨35256737065893263022315637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47008982754524350696420849 35256737065893263022315637)
        ·
          refine ⟨3305319099927493408342091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 35256737065893263022315637 3305319099927493408342091)
          ·
            refine ⟨4957978649891240112513137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3305319099927493408342091 4957978649891240112513137)
            ·
              refine ⟨3718483987418430084384853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4957978649891240112513137 3718483987418430084384853)
              ·
                refine ⟨43575984227559727551385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3718483987418430084384853 43575984227559727551385)
                ·
                  rfl

theorem cell22_1145663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 2, 8].length) (baseStart_1145663 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1145663 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1145663 prefixEnd_1145663 := by exact prefixLift 1145663
  have htrace : WordTrace (prefixWord ++ tailWord_1145663) baseStart_1145663 baseEnd_1145663 := by
    simpa [prefixWord, tailWord_1145663, baseEnd_1145663] using wordTrace_append hprefix tailTrace_1145663
  have hstable : (prefixWord ++ tailWord_1145663).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1145663).length < 2 ^ (prefixWord ++ tailWord_1145663).sum := by decide
  have hdescent : baseEnd_1145663 < baseStart_1145663 := by decide
  rcases family_descends (prefixWord ++ tailWord_1145663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1145684 : List Nat := [2, 4, 1, 1, 4, 1, 2, 2, 2, 3]
def baseStart_1145684 : Nat := 118140960795 + 1145684 * 2 ^ 59
def prefixEnd_1145684 : Nat := 4983230072969 + 3 ^ 40 * 1145684 * 2
def baseEnd_1145684 : Nat := 392191046777200493187401

theorem tailTrace_1145684 : CollatzResearch.WordTrace tailWord_1145684 prefixEnd_1145684 392191046777200493187401 := by
  unfold tailWord_1145684
  simp only [CollatzResearch.WordTrace]
  refine ⟨20893264190695005047222053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27857685587593340062962737 20893264190695005047222053)
  ·
    refine ⟨3917487035755313446354135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20893264190695005047222053 3917487035755313446354135)
    ·
      refine ⟨5876230553632970169531203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3917487035755313446354135 5876230553632970169531203)
      ·
        refine ⟨8814345830449455254296805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5876230553632970169531203 8814345830449455254296805)
        ·
          refine ⟨1652689843209272860180651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8814345830449455254296805 1652689843209272860180651)
          ·
            refine ⟨2479034764813909290270977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1652689843209272860180651 2479034764813909290270977)
            ·
              refine ⟨1859276073610431967703233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2479034764813909290270977 1859276073610431967703233)
              ·
                refine ⟨1394457055207823975777425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1859276073610431967703233 1394457055207823975777425)
                ·
                  refine ⟨1045842791405867981833069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1394457055207823975777425 1045842791405867981833069)
                  ·
                    refine ⟨392191046777200493187401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1045842791405867981833069 392191046777200493187401)
                    ·
                      rfl

theorem cell22_1145684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 2, 2, 2, 3].length) (baseStart_1145684 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1145684 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1145684 prefixEnd_1145684 := by exact prefixLift 1145684
  have htrace : WordTrace (prefixWord ++ tailWord_1145684) baseStart_1145684 baseEnd_1145684 := by
    simpa [prefixWord, tailWord_1145684, baseEnd_1145684] using wordTrace_append hprefix tailTrace_1145684
  have hstable : (prefixWord ++ tailWord_1145684).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1145684).length < 2 ^ (prefixWord ++ tailWord_1145684).sum := by decide
  have hdescent : baseEnd_1145684 < baseStart_1145684 := by decide
  rcases family_descends (prefixWord ++ tailWord_1145684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1145695 : List Nat := [1, 1, 2, 3, 1, 3, 2, 3, 3, 3]
def baseStart_1145695 : Nat := 118140960795 + 1145695 * 2 ^ 59
def prefixEnd_1145695 : Nat := 4983230072969 + 3 ^ 40 * 1145695 * 2
def baseEnd_1145695 : Nat := 392194812302000131162367

theorem tailTrace_1145695 : CollatzResearch.WordTrace tailWord_1145695 prefixEnd_1145695 392194812302000131162367 := by
  unfold tailWord_1145695
  simp only [CollatzResearch.WordTrace]
  refine ⟨41786929584350158973094539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27857953056233439315396359 41786929584350158973094539)
  ·
    refine ⟨62680394376525238459641809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41786929584350158973094539 62680394376525238459641809)
    ·
      refine ⟨47010295782393928844731357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62680394376525238459641809 47010295782393928844731357)
      ·
        refine ⟨17628860918397723316774259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47010295782393928844731357 17628860918397723316774259)
        ·
          refine ⟨26443291377596584975161389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17628860918397723316774259 26443291377596584975161389)
          ·
            refine ⟨9916234266598719365685521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26443291377596584975161389 9916234266598719365685521)
            ·
              refine ⟨7437175699949039524264141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9916234266598719365685521 7437175699949039524264141)
              ·
                refine ⟨2788940887480889821599053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7437175699949039524264141 2788940887480889821599053)
                ·
                  refine ⟨1045852832805333683099645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2788940887480889821599053 1045852832805333683099645)
                  ·
                    refine ⟨392194812302000131162367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1045852832805333683099645 392194812302000131162367)
                    ·
                      rfl

theorem cell22_1145695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 2, 3, 3, 3].length) (baseStart_1145695 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1145695 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1145695 prefixEnd_1145695 := by exact prefixLift 1145695
  have htrace : WordTrace (prefixWord ++ tailWord_1145695) baseStart_1145695 baseEnd_1145695 := by
    simpa [prefixWord, tailWord_1145695, baseEnd_1145695] using wordTrace_append hprefix tailTrace_1145695
  have hstable : (prefixWord ++ tailWord_1145695).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1145695).length < 2 ^ (prefixWord ++ tailWord_1145695).sum := by decide
  have hdescent : baseEnd_1145695 < baseStart_1145695 := by decide
  rcases family_descends (prefixWord ++ tailWord_1145695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1145802 : List Nat := [3, 1, 2, 1, 2, 1, 1, 6, 2, 3]
def baseStart_1145802 : Nat := 118140960795 + 1145802 * 2 ^ 59
def prefixEnd_1145802 : Nat := 4983230072969 + 3 ^ 40 * 1145802 * 2
def baseEnd_1145802 : Nat := 392231440588687518737039

theorem tailTrace_1145802 : CollatzResearch.WordTrace tailWord_1145802 prefixEnd_1145802 392231440588687518737039 := by
  unfold tailWord_1145802
  simp only [CollatzResearch.WordTrace]
  refine ⟨10447708048740629061809915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27860554796641677498159773 10447708048740629061809915)
  ·
    refine ⟨15671562073110943592714873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10447708048740629061809915 15671562073110943592714873)
    ·
      refine ⟨11753671554833207694536155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15671562073110943592714873 11753671554833207694536155)
      ·
        refine ⟨17630507332249811541804233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11753671554833207694536155 17630507332249811541804233)
        ·
          refine ⟨13222880499187358656353175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17630507332249811541804233 13222880499187358656353175)
          ·
            refine ⟨19834320748781037984529763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13222880499187358656353175 19834320748781037984529763)
            ·
              refine ⟨29751481123171556976794645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19834320748781037984529763 29751481123171556976794645)
              ·
                refine ⟨1394600677648666733287249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 29751481123171556976794645 1394600677648666733287249)
                ·
                  refine ⟨1045950508236500049965437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1394600677648666733287249 1045950508236500049965437)
                  ·
                    refine ⟨392231440588687518737039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1045950508236500049965437 392231440588687518737039)
                    ·
                      rfl

theorem cell22_1145802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 6, 2, 3].length) (baseStart_1145802 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1145802 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1145802 prefixEnd_1145802 := by exact prefixLift 1145802
  have htrace : WordTrace (prefixWord ++ tailWord_1145802) baseStart_1145802 baseEnd_1145802 := by
    simpa [prefixWord, tailWord_1145802, baseEnd_1145802] using wordTrace_append hprefix tailTrace_1145802
  have hstable : (prefixWord ++ tailWord_1145802).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1145802).length < 2 ^ (prefixWord ++ tailWord_1145802).sum := by decide
  have hdescent : baseEnd_1145802 < baseStart_1145802 := by decide
  rcases family_descends (prefixWord ++ tailWord_1145802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1145804 : List Nat := [2, 2, 1, 4, 1, 1, 5, 2, 4]
def baseStart_1145804 : Nat := 118140960795 + 1145804 * 2 ^ 59
def prefixEnd_1145804 : Nat := 4983230072969 + 3 ^ 40 * 1145804 * 2
def baseEnd_1145804 : Nat := 130744041743186726729011

theorem tailTrace_1145804 : CollatzResearch.WordTrace tailWord_1145804 prefixEnd_1145804 130744041743186726729011 := by
  unfold tailWord_1145804
  simp only [CollatzResearch.WordTrace]
  refine ⟨20895452570477635294406233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27860603427303513725874977 20895452570477635294406233)
  ·
    refine ⟨15671589427858226470804675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20895452570477635294406233 15671589427858226470804675)
    ·
      refine ⟨23507384141787339706207013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15671589427858226470804675 23507384141787339706207013)
      ·
        refine ⟨4407634526585126194913815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23507384141787339706207013 4407634526585126194913815)
        ·
          refine ⟨6611451789877689292370723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4407634526585126194913815 6611451789877689292370723)
          ·
            refine ⟨9917177684816533938556085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6611451789877689292370723 9917177684816533938556085)
            ·
              refine ⟨929735407951550056739633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9917177684816533938556085 929735407951550056739633)
              ·
                refine ⟨697301555963662542554725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 929735407951550056739633 697301555963662542554725)
                ·
                  refine ⟨130744041743186726729011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 697301555963662542554725 130744041743186726729011)
                  ·
                    rfl

theorem cell22_1145804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 5, 2, 4].length) (baseStart_1145804 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1145804 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1145804 prefixEnd_1145804 := by exact prefixLift 1145804
  have htrace : WordTrace (prefixWord ++ tailWord_1145804) baseStart_1145804 baseEnd_1145804 := by
    simpa [prefixWord, tailWord_1145804, baseEnd_1145804] using wordTrace_append hprefix tailTrace_1145804
  have hstable : (prefixWord ++ tailWord_1145804).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1145804).length < 2 ^ (prefixWord ++ tailWord_1145804).sum := by decide
  have hdescent : baseEnd_1145804 < baseStart_1145804 := by decide
  rcases family_descends (prefixWord ++ tailWord_1145804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1145877 : List Nat := [1, 3, 2, 1, 4, 1, 2, 3, 5]
def baseStart_1145877 : Nat := 118140960795 + 1145877 * 2 ^ 59
def prefixEnd_1145877 : Nat := 4983230072969 + 3 ^ 40 * 1145877 * 2
def baseEnd_1145877 : Nat := 130752371540470774370603

theorem tailTrace_1145877 : CollatzResearch.WordTrace tailWord_1145877 prefixEnd_1145877 130752371540470774370603 := by
  unfold tailWord_1145877
  simp only [CollatzResearch.WordTrace]
  refine ⟨41793567669690804056219885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27862378446460536037479923 41793567669690804056219885)
  ·
    refine ⟨15672587876134051521082457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41793567669690804056219885 15672587876134051521082457)
    ·
      refine ⟨11754440907100538640811843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15672587876134051521082457 11754440907100538640811843)
      ·
        refine ⟨17631661360650807961217765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11754440907100538640811843 17631661360650807961217765)
        ·
          refine ⟨3305936505122026492728331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17631661360650807961217765 3305936505122026492728331)
          ·
            refine ⟨4958904757683039739092497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3305936505122026492728331 4958904757683039739092497)
            ·
              refine ⟨3719178568262279804319373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4958904757683039739092497 3719178568262279804319373)
              ·
                refine ⟨1394691963098354926619765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3719178568262279804319373 1394691963098354926619765)
                ·
                  refine ⟨130752371540470774370603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1394691963098354926619765 130752371540470774370603)
                  ·
                    rfl

theorem cell22_1145877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 2, 3, 5].length) (baseStart_1145877 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1145877 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1145877 prefixEnd_1145877 := by exact prefixLift 1145877
  have htrace : WordTrace (prefixWord ++ tailWord_1145877) baseStart_1145877 baseEnd_1145877 := by
    simpa [prefixWord, tailWord_1145877, baseEnd_1145877] using wordTrace_append hprefix tailTrace_1145877
  have hstable : (prefixWord ++ tailWord_1145877).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1145877).length < 2 ^ (prefixWord ++ tailWord_1145877).sum := by decide
  have hdescent : baseEnd_1145877 < baseStart_1145877 := by decide
  rcases family_descends (prefixWord ++ tailWord_1145877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
