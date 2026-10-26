import V185TrunkScan22Chunk416

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_3718209 : List Nat := [1, 2, 5, 1, 4, 1, 1, 1, 3, 3]
def baseStart_3718209 : Nat := 118140960795 + 3718209 * 2 ^ 59
def prefixEnd_3718209 : Nat := 4983230072969 + 3 ^ 40 * 3718209 * 2
def baseEnd_3718209 : Nat := 1272818927248898815925183

theorem tailTrace_3718209 : CollatzResearch.WordTrace tailWord_3718209 prefixEnd_3718209 1272818927248898815925183 := by
  unfold tailWord_3718209
  simp only [CollatzResearch.WordTrace]
  refine ⟨135614223386571287385821681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90409482257714191590547787 135614223386571287385821681)
  ·
    refine ⟨101710667539928465539366261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135614223386571287385821681 101710667539928465539366261)
    ·
      refine ⟨9535375081868293644315587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 101710667539928465539366261 9535375081868293644315587)
      ·
        refine ⟨14303062622802440466473381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9535375081868293644315587 14303062622802440466473381)
        ·
          refine ⟨2681824241775457587463759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14303062622802440466473381 2681824241775457587463759)
          ·
            refine ⟨4022736362663186381195639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2681824241775457587463759 4022736362663186381195639)
            ·
              refine ⟨6034104543994779571793459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4022736362663186381195639 6034104543994779571793459)
              ·
                refine ⟨9051156815992169357690189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6034104543994779571793459 9051156815992169357690189)
                ·
                  refine ⟨3394183805997063509133821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9051156815992169357690189 3394183805997063509133821)
                  ·
                    refine ⟨1272818927248898815925183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3394183805997063509133821 1272818927248898815925183)
                    ·
                      rfl

theorem cell22_3718209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 4, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 4, 1, 1, 1, 3, 3].length) (baseStart_3718209 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3718209 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3718209 prefixEnd_3718209 := by exact prefixLift 3718209
  have htrace : WordTrace (prefixWord ++ tailWord_3718209) baseStart_3718209 baseEnd_3718209 := by
    simpa [prefixWord, tailWord_3718209, baseEnd_3718209] using wordTrace_append hprefix tailTrace_3718209
  have hstable : (prefixWord ++ tailWord_3718209).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3718209).length < 2 ^ (prefixWord ++ tailWord_3718209).sum := by decide
  have hdescent : baseEnd_3718209 < baseStart_3718209 := by decide
  rcases family_descends (prefixWord ++ tailWord_3718209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3718263 : List Nat := [1, 1, 3, 1, 1, 4, 1, 4, 2, 4]
def baseStart_3718263 : Nat := 118140960795 + 3718263 * 2 ^ 59
def prefixEnd_3718263 : Nat := 4983230072969 + 3 ^ 40 * 3718263 * 2
def baseEnd_3718263 : Nat := 1272837412552460675075017

theorem tailTrace_3718263 : CollatzResearch.WordTrace tailWord_3718263 prefixEnd_3718263 1272837412552460675075017 := by
  unfold tailWord_3718263
  simp only [CollatzResearch.WordTrace]
  refine ⟨135616192928375654608287443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90410795285583769738858295 135616192928375654608287443)
  ·
    refine ⟨203424289392563481912431165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135616192928375654608287443 203424289392563481912431165)
    ·
      refine ⟨76284108522211305717161687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 203424289392563481912431165 76284108522211305717161687)
      ·
        refine ⟨114426162783316958575742531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76284108522211305717161687 114426162783316958575742531)
        ·
          refine ⟨171639244174975437863613797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114426162783316958575742531 171639244174975437863613797)
          ·
            refine ⟨32182358282807894599427587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 171639244174975437863613797 32182358282807894599427587)
            ·
              refine ⟨48273537424211841899141381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32182358282807894599427587 48273537424211841899141381)
              ·
                refine ⟨9051288267039720356089009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48273537424211841899141381 9051288267039720356089009)
                ·
                  refine ⟨6788466200279790267066757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9051288267039720356089009 6788466200279790267066757)
                  ·
                    refine ⟨1272837412552460675075017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6788466200279790267066757 1272837412552460675075017)
                    ·
                      rfl

theorem cell22_3718263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 4, 2, 4].length) (baseStart_3718263 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3718263 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3718263 prefixEnd_3718263 := by exact prefixLift 3718263
  have htrace : WordTrace (prefixWord ++ tailWord_3718263) baseStart_3718263 baseEnd_3718263 := by
    simpa [prefixWord, tailWord_3718263, baseEnd_3718263] using wordTrace_append hprefix tailTrace_3718263
  have hstable : (prefixWord ++ tailWord_3718263).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3718263).length < 2 ^ (prefixWord ++ tailWord_3718263).sum := by decide
  have hdescent : baseEnd_3718263 < baseStart_3718263 := by decide
  rcases family_descends (prefixWord ++ tailWord_3718263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3718295 : List Nat := [1, 1, 3, 3, 3, 2, 3, 6]
def baseStart_3718295 : Nat := 118140960795 + 3718295 * 2 ^ 59
def prefixEnd_3718295 : Nat := 4983230072969 + 3 ^ 40 * 3718295 * 2
def baseEnd_3718295 : Nat := 141427596311824806474991

theorem tailTrace_3718295 : CollatzResearch.WordTrace tailWord_3718295 prefixEnd_3718295 141427596311824806474991 := by
  unfold tailWord_3718295
  simp only [CollatzResearch.WordTrace]
  refine ⟨135617360064259724073452339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90411573376173149382301559 135617360064259724073452339)
  ·
    refine ⟨203426040096389586110178509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135617360064259724073452339 203426040096389586110178509)
    ·
      refine ⟨76284765036146094791316941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 203426040096389586110178509 76284765036146094791316941)
      ·
        refine ⟨28606786888554785546743853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76284765036146094791316941 28606786888554785546743853)
        ·
          refine ⟨10727545083208044580028945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28606786888554785546743853 10727545083208044580028945)
          ·
            refine ⟨8045658812406033435021709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10727545083208044580028945 8045658812406033435021709)
            ·
              refine ⟨3017122054652262538133141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8045658812406033435021709 3017122054652262538133141)
              ·
                refine ⟨141427596311824806474991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3017122054652262538133141 141427596311824806474991)
                ·
                  rfl

theorem cell22_3718295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 3, 6].length) (baseStart_3718295 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3718295 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3718295 prefixEnd_3718295 := by exact prefixLift 3718295
  have htrace : WordTrace (prefixWord ++ tailWord_3718295) baseStart_3718295 baseEnd_3718295 := by
    simpa [prefixWord, tailWord_3718295, baseEnd_3718295] using wordTrace_append hprefix tailTrace_3718295
  have hstable : (prefixWord ++ tailWord_3718295).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3718295).length < 2 ^ (prefixWord ++ tailWord_3718295).sum := by decide
  have hdescent : baseEnd_3718295 < baseStart_3718295 := by decide
  rcases family_descends (prefixWord ++ tailWord_3718295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3718327 : List Nat := [1, 1, 3, 1, 4, 1, 1, 6, 1, 3]
def baseStart_3718327 : Nat := 118140960795 + 3718327 * 2 ^ 59
def prefixEnd_3718327 : Nat := 4983230072969 + 3 ^ 40 * 3718327 * 2
def baseEnd_3718327 : Nat := 1272859321060385841474821

theorem tailTrace_3718327 : CollatzResearch.WordTrace tailWord_3718327 prefixEnd_3718327 1272859321060385841474821 := by
  unfold tailWord_3718327
  simp only [CollatzResearch.WordTrace]
  refine ⟨135618527200143793538617235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90412351466762529025744823 135618527200143793538617235)
  ·
    refine ⟨203427790800215690307925853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135618527200143793538617235 203427790800215690307925853)
    ·
      refine ⟨76285421550080883865472195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 203427790800215690307925853 76285421550080883865472195)
      ·
        refine ⟨114428132325121325798208293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76285421550080883865472195 114428132325121325798208293)
        ·
          refine ⟨21455274810960248587164055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 114428132325121325798208293 21455274810960248587164055)
          ·
            refine ⟨32182912216440372880746083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21455274810960248587164055 32182912216440372880746083)
            ·
              refine ⟨48274368324660559321119125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32182912216440372880746083 48274368324660559321119125)
              ·
                refine ⟨2262861015218463718177459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 48274368324660559321119125 2262861015218463718177459)
                ·
                  refine ⟨3394291522827695577266189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2262861015218463718177459 3394291522827695577266189)
                  ·
                    refine ⟨1272859321060385841474821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3394291522827695577266189 1272859321060385841474821)
                    ·
                      rfl

theorem cell22_3718327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 6, 1, 3].length) (baseStart_3718327 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3718327 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3718327 prefixEnd_3718327 := by exact prefixLift 3718327
  have htrace : WordTrace (prefixWord ++ tailWord_3718327) baseStart_3718327 baseEnd_3718327 := by
    simpa [prefixWord, tailWord_3718327, baseEnd_3718327] using wordTrace_append hprefix tailTrace_3718327
  have hstable : (prefixWord ++ tailWord_3718327).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3718327).length < 2 ^ (prefixWord ++ tailWord_3718327).sum := by decide
  have hdescent : baseEnd_3718327 < baseStart_3718327 := by decide
  rcases family_descends (prefixWord ++ tailWord_3718327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3718404 : List Nat := [2, 3, 2, 2, 2, 3, 1, 2, 1, 4]
def baseStart_3718404 : Nat := 118140960795 + 3718404 * 2 ^ 59
def prefixEnd_3718404 : Nat := 4983230072969 + 3 ^ 40 * 3718404 * 2
def baseEnd_3718404 : Nat := 1272885679733983307299585

theorem tailTrace_3718404 : CollatzResearch.WordTrace tailWord_3718404 prefixEnd_3718404 1272885679733983307299585 := by
  unfold tailWord_3718404
  simp only [CollatzResearch.WordTrace]
  refine ⟨67810667810432417844585133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90414223747243223792780177 67810667810432417844585133)
  ·
    refine ⟨25429000428912156691719425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67810667810432417844585133 25429000428912156691719425)
    ·
      refine ⟨19071750321684117518789569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25429000428912156691719425 19071750321684117518789569)
      ·
        refine ⟨14303812741263088139092177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19071750321684117518789569 14303812741263088139092177)
        ·
          refine ⟨10727859555947316104319133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14303812741263088139092177 10727859555947316104319133)
          ·
            refine ⟨4022947333480243539119675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10727859555947316104319133 4022947333480243539119675)
            ·
              refine ⟨6034421000220365308679513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4022947333480243539119675 6034421000220365308679513)
              ·
                refine ⟨4525815750165273981509635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6034421000220365308679513 4525815750165273981509635)
                ·
                  refine ⟨6788723625247910972264453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4525815750165273981509635 6788723625247910972264453)
                  ·
                    refine ⟨1272885679733983307299585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6788723625247910972264453 1272885679733983307299585)
                    ·
                      rfl

theorem cell22_3718404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 3, 1, 2, 1, 4].length) (baseStart_3718404 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3718404 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3718404 prefixEnd_3718404 := by exact prefixLift 3718404
  have htrace : WordTrace (prefixWord ++ tailWord_3718404) baseStart_3718404 baseEnd_3718404 := by
    simpa [prefixWord, tailWord_3718404, baseEnd_3718404] using wordTrace_append hprefix tailTrace_3718404
  have hstable : (prefixWord ++ tailWord_3718404).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3718404).length < 2 ^ (prefixWord ++ tailWord_3718404).sum := by decide
  have hdescent : baseEnd_3718404 < baseStart_3718404 := by decide
  rcases family_descends (prefixWord ++ tailWord_3718404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3718490 : List Nat := [3, 1, 1, 2, 1, 2, 3, 2, 2, 5]
def baseStart_3718490 : Nat := 118140960795 + 3718490 * 2 ^ 59
def prefixEnd_3718490 : Nat := 4983230072969 + 3 ^ 40 * 3718490 * 2
def baseEnd_3718490 : Nat := 1272915119291507749649321

theorem tailTrace_3718490 : CollatzResearch.WordTrace tailWord_3718490 prefixEnd_3718490 1272915119291507749649321 := by
  unfold tailWord_3718490
  simp only [CollatzResearch.WordTrace]
  refine ⟨33906118074638318094200231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90416314865702181584533949 33906118074638318094200231)
  ·
    refine ⟨50859177111957477141300347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33906118074638318094200231 50859177111957477141300347)
    ·
      refine ⟨76288765667936215711950521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50859177111957477141300347 76288765667936215711950521)
      ·
        refine ⟨57216574250952161783962891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76288765667936215711950521 57216574250952161783962891)
        ·
          refine ⟨85824861376428242675944337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57216574250952161783962891 85824861376428242675944337)
          ·
            refine ⟨64368646032321182006958253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85824861376428242675944337 64368646032321182006958253)
            ·
              refine ⟨24138242262120443252609345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64368646032321182006958253 24138242262120443252609345)
              ·
                refine ⟨18103681696590332439457009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24138242262120443252609345 18103681696590332439457009)
                ·
                  refine ⟨13577761272442749329592757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18103681696590332439457009 13577761272442749329592757)
                  ·
                    refine ⟨1272915119291507749649321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13577761272442749329592757 1272915119291507749649321)
                    ·
                      rfl

theorem cell22_3718490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 3, 2, 2, 5].length) (baseStart_3718490 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3718490 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3718490 prefixEnd_3718490 := by exact prefixLift 3718490
  have htrace : WordTrace (prefixWord ++ tailWord_3718490) baseStart_3718490 baseEnd_3718490 := by
    simpa [prefixWord, tailWord_3718490, baseEnd_3718490] using wordTrace_append hprefix tailTrace_3718490
  have hstable : (prefixWord ++ tailWord_3718490).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3718490).length < 2 ^ (prefixWord ++ tailWord_3718490).sum := by decide
  have hdescent : baseEnd_3718490 < baseStart_3718490 := by decide
  rcases family_descends (prefixWord ++ tailWord_3718490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3718505 : List Nat := [1, 2, 1, 1, 1, 3, 2, 4, 3, 4]
def baseStart_3718505 : Nat := 118140960795 + 3718505 * 2 ^ 59
def prefixEnd_3718505 : Nat := 4983230072969 + 3 ^ 40 * 3718505 * 2
def baseEnd_3718505 : Nat := 1272920254098052710524275

theorem tailTrace_3718505 : CollatzResearch.WordTrace tailWord_3718505 prefixEnd_3718505 1272920254098052710524275 := by
  unfold tailWord_3718505
  simp only [CollatzResearch.WordTrace]
  refine ⟨135625019393498929938596969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90416679595665953292397979 135625019393498929938596969)
  ·
    refine ⟨101718764545124197453947727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135625019393498929938596969 101718764545124197453947727)
    ·
      refine ⟨152578146817686296180921591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101718764545124197453947727 152578146817686296180921591)
      ·
        refine ⟨228867220226529444271382387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152578146817686296180921591 228867220226529444271382387)
        ·
          refine ⟨343300830339794166407073581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 228867220226529444271382387 343300830339794166407073581)
          ·
            refine ⟨128737811377422812402652593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 343300830339794166407073581 128737811377422812402652593)
            ·
              refine ⟨96553358533067109301989445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 128737811377422812402652593 96553358533067109301989445)
              ·
                refine ⟨18103754724950082994123021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 96553358533067109301989445 18103754724950082994123021)
                ·
                  refine ⟨6788908021856281122796133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18103754724950082994123021 6788908021856281122796133)
                  ·
                    refine ⟨1272920254098052710524275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6788908021856281122796133 1272920254098052710524275)
                    ·
                      rfl

theorem cell22_3718505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 4, 3, 4].length) (baseStart_3718505 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3718505 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3718505 prefixEnd_3718505 := by exact prefixLift 3718505
  have htrace : WordTrace (prefixWord ++ tailWord_3718505) baseStart_3718505 baseEnd_3718505 := by
    simpa [prefixWord, tailWord_3718505, baseEnd_3718505] using wordTrace_append hprefix tailTrace_3718505
  have hstable : (prefixWord ++ tailWord_3718505).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3718505).length < 2 ^ (prefixWord ++ tailWord_3718505).sum := by decide
  have hdescent : baseEnd_3718505 < baseStart_3718505 := by decide
  rcases family_descends (prefixWord ++ tailWord_3718505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3718509 : List Nat := [1, 5, 1, 1, 1, 4, 3, 1, 5]
def baseStart_3718509 : Nat := 118140960795 + 3718509 * 2 ^ 59
def prefixEnd_3718509 : Nat := 4983230072969 + 3 ^ 40 * 3718509 * 2
def baseEnd_3718509 : Nat := 424307207793266011141421

theorem tailTrace_3718509 : CollatzResearch.WordTrace tailWord_3718509 prefixEnd_3718509 424307207793266011141421 := by
  unfold tailWord_3718509
  simp only [CollatzResearch.WordTrace]
  refine ⟨135625165285484438621742581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90416776856989625747828387 135625165285484438621742581)
  ·
    refine ⟨12714859245514166120788367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 135625165285484438621742581 12714859245514166120788367)
    ·
      refine ⟨19072288868271249181182551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12714859245514166120788367 19072288868271249181182551)
      ·
        refine ⟨28608433302406873771773827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19072288868271249181182551 28608433302406873771773827)
        ·
          refine ⟨42912649953610310657660741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28608433302406873771773827 42912649953610310657660741)
          ·
            refine ⟨8046121866301933248311389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42912649953610310657660741 8046121866301933248311389)
            ·
              refine ⟨3017295699863224968116771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8046121866301933248311389 3017295699863224968116771)
              ·
                refine ⟨4525943549794837452175157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3017295699863224968116771 4525943549794837452175157)
                ·
                  refine ⟨424307207793266011141421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4525943549794837452175157 424307207793266011141421)
                  ·
                    rfl

theorem cell22_3718509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 3, 1, 5].length) (baseStart_3718509 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3718509 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3718509 prefixEnd_3718509 := by exact prefixLift 3718509
  have htrace : WordTrace (prefixWord ++ tailWord_3718509) baseStart_3718509 baseEnd_3718509 := by
    simpa [prefixWord, tailWord_3718509, baseEnd_3718509] using wordTrace_append hprefix tailTrace_3718509
  have hstable : (prefixWord ++ tailWord_3718509).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3718509).length < 2 ^ (prefixWord ++ tailWord_3718509).sum := by decide
  have hdescent : baseEnd_3718509 < baseStart_3718509 := by decide
  rcases family_descends (prefixWord ++ tailWord_3718509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3718530 : List Nat := [3, 4, 2, 1, 1, 3, 1, 3, 1, 3]
def baseStart_3718530 : Nat := 118140960795 + 3718530 * 2 ^ 59
def prefixEnd_3718530 : Nat := 4983230072969 + 3 ^ 40 * 3718530 * 2
def baseEnd_3718530 : Nat := 1272928812108960978649199

theorem tailTrace_3718530 : CollatzResearch.WordTrace tailWord_3718530 prefixEnd_3718530 1272928812108960978649199 := by
  unfold tailWord_3718530
  simp only [CollatzResearch.WordTrace]
  refine ⟨33906482804602089802064261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90417287478938906138838029 33906482804602089802064261)
  ·
    refine ⟨6357465525862891837887049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33906482804602089802064261 6357465525862891837887049)
    ·
      refine ⟨4768099144397168878415287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6357465525862891837887049 4768099144397168878415287)
      ·
        refine ⟨7152148716595753317622931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4768099144397168878415287 7152148716595753317622931)
        ·
          refine ⟨10728223074893629976434397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7152148716595753317622931 10728223074893629976434397)
          ·
            refine ⟨4023083653085111241162899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10728223074893629976434397 4023083653085111241162899)
            ·
              refine ⟨6034625479627666861744349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4023083653085111241162899 6034625479627666861744349)
              ·
                refine ⟨2262984554860375073154131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6034625479627666861744349 2262984554860375073154131)
                ·
                  refine ⟨3394476832290562609731197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2262984554860375073154131 3394476832290562609731197)
                  ·
                    refine ⟨1272928812108960978649199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3394476832290562609731197 1272928812108960978649199)
                    ·
                      rfl

theorem cell22_3718530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 3, 1, 3, 1, 3].length) (baseStart_3718530 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3718530 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3718530 prefixEnd_3718530 := by exact prefixLift 3718530
  have htrace : WordTrace (prefixWord ++ tailWord_3718530) baseStart_3718530 baseEnd_3718530 := by
    simpa [prefixWord, tailWord_3718530, baseEnd_3718530] using wordTrace_append hprefix tailTrace_3718530
  have hstable : (prefixWord ++ tailWord_3718530).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3718530).length < 2 ^ (prefixWord ++ tailWord_3718530).sum := by decide
  have hdescent : baseEnd_3718530 < baseStart_3718530 := by decide
  rcases family_descends (prefixWord ++ tailWord_3718530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3718567 : List Nat := [1, 1, 6, 1, 1, 1, 1, 2, 4, 4]
def baseStart_3718567 : Nat := 118140960795 + 3718567 * 2 ^ 59
def prefixEnd_3718567 : Nat := 4983230072969 + 3 ^ 40 * 3718567 * 2
def baseEnd_3718567 : Nat := 1272941477965105215474085

theorem tailTrace_3718567 : CollatzResearch.WordTrace tailWord_3718567 prefixEnd_3718567 1272941477965105215474085 := by
  unfold tailWord_3718567
  simp only [CollatzResearch.WordTrace]
  refine ⟨135627280719274314527353955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90418187146182876351569303 135627280719274314527353955)
  ·
    refine ⟨203440921078911471791030933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135627280719274314527353955 203440921078911471791030933)
    ·
      refine ⟨9536293175573975240204575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 203440921078911471791030933 9536293175573975240204575)
      ·
        refine ⟨14304439763360962860306863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9536293175573975240204575 14304439763360962860306863)
        ·
          refine ⟨21456659645041444290460295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14304439763360962860306863 21456659645041444290460295)
          ·
            refine ⟨32184989467562166435690443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21456659645041444290460295 32184989467562166435690443)
            ·
              refine ⟨48277484201343249653535665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32184989467562166435690443 48277484201343249653535665)
              ·
                refine ⟨36208113151007437240151749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48277484201343249653535665 36208113151007437240151749)
                ·
                  refine ⟨6789021215813894482528453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36208113151007437240151749 6789021215813894482528453)
                  ·
                    refine ⟨1272941477965105215474085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6789021215813894482528453 1272941477965105215474085)
                    ·
                      rfl

theorem cell22_3718567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 2, 4, 4].length) (baseStart_3718567 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3718567 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3718567 prefixEnd_3718567 := by exact prefixLift 3718567
  have htrace : WordTrace (prefixWord ++ tailWord_3718567) baseStart_3718567 baseEnd_3718567 := by
    simpa [prefixWord, tailWord_3718567, baseEnd_3718567] using wordTrace_append hprefix tailTrace_3718567
  have hstable : (prefixWord ++ tailWord_3718567).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3718567).length < 2 ^ (prefixWord ++ tailWord_3718567).sum := by decide
  have hdescent : baseEnd_3718567 < baseStart_3718567 := by decide
  rcases family_descends (prefixWord ++ tailWord_3718567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3718691 : List Nat := [1, 1, 1, 4, 5, 1, 2, 2, 1, 4]
def baseStart_3718691 : Nat := 118140960795 + 3718691 * 2 ^ 59
def prefixEnd_3718691 : Nat := 4983230072969 + 3 ^ 40 * 3718691 * 2
def baseEnd_3718691 : Nat := 1272983925699210225373705

theorem tailTrace_3718691 : CollatzResearch.WordTrace tailWord_3718691 prefixEnd_3718691 1272983925699210225373705 := by
  unfold tailWord_3718691
  simp only [CollatzResearch.WordTrace]
  refine ⟨135631803370825083704867927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90421202247216722469911951 135631803370825083704867927)
  ·
    refine ⟨203447705056237625557301891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135631803370825083704867927 203447705056237625557301891)
    ·
      refine ⟨305171557584356438335952837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203447705056237625557301891 305171557584356438335952837)
      ·
        refine ⟨57219667047066832187991157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 305171557584356438335952837 57219667047066832187991157)
        ·
          refine ⟨5364343785662515517624171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 57219667047066832187991157 5364343785662515517624171)
          ·
            refine ⟨8046515678493773276436257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5364343785662515517624171 8046515678493773276436257)
            ·
              refine ⟨6034886758870329957327193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8046515678493773276436257 6034886758870329957327193)
              ·
                refine ⟨4526165069152747467995395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6034886758870329957327193 4526165069152747467995395)
                ·
                  refine ⟨6789247603729121201993093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4526165069152747467995395 6789247603729121201993093)
                  ·
                    refine ⟨1272983925699210225373705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6789247603729121201993093 1272983925699210225373705)
                    ·
                      rfl

theorem cell22_3718691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 2, 2, 1, 4].length) (baseStart_3718691 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3718691 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3718691 prefixEnd_3718691 := by exact prefixLift 3718691
  have htrace : WordTrace (prefixWord ++ tailWord_3718691) baseStart_3718691 baseEnd_3718691 := by
    simpa [prefixWord, tailWord_3718691, baseEnd_3718691] using wordTrace_append hprefix tailTrace_3718691
  have hstable : (prefixWord ++ tailWord_3718691).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3718691).length < 2 ^ (prefixWord ++ tailWord_3718691).sum := by decide
  have hdescent : baseEnd_3718691 < baseStart_3718691 := by decide
  rcases family_descends (prefixWord ++ tailWord_3718691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3718719 : List Nat := [1, 1, 2, 2, 3, 4, 1, 2, 2, 4]
def baseStart_3718719 : Nat := 118140960795 + 3718719 * 2 ^ 59
def prefixEnd_3718719 : Nat := 4983230072969 + 3 ^ 40 * 3718719 * 2
def baseEnd_3718719 : Nat := 1272993510671427485673619

theorem tailTrace_3718719 : CollatzResearch.WordTrace tailWord_3718719 prefixEnd_3718719 1272993510671427485673619 := by
  unfold tailWord_3718719
  simp only [CollatzResearch.WordTrace]
  refine ⟨135632824614723644486887211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90421883076482429657924807 135632824614723644486887211)
  ·
    refine ⟨203449236922085466730330817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135632824614723644486887211 203449236922085466730330817)
    ·
      refine ⟨152586927691564100047748113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 203449236922085466730330817 152586927691564100047748113)
      ·
        refine ⟨114440195768673075035811085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152586927691564100047748113 114440195768673075035811085)
        ·
          refine ⟨42915073413252403138429157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 114440195768673075035811085 42915073413252403138429157)
          ·
            refine ⟨8046576264984825588455467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42915073413252403138429157 8046576264984825588455467)
            ·
              refine ⟨12069864397477238382683201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8046576264984825588455467 12069864397477238382683201)
              ·
                refine ⟨9052398298107928787012401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12069864397477238382683201 9052398298107928787012401)
                ·
                  refine ⟨6789298723580946590259301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9052398298107928787012401 6789298723580946590259301)
                  ·
                    refine ⟨1272993510671427485673619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6789298723580946590259301 1272993510671427485673619)
                    ·
                      rfl

theorem cell22_3718719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 1, 2, 2, 4].length) (baseStart_3718719 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3718719 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3718719 prefixEnd_3718719 := by exact prefixLift 3718719
  have htrace : WordTrace (prefixWord ++ tailWord_3718719) baseStart_3718719 baseEnd_3718719 := by
    simpa [prefixWord, tailWord_3718719, baseEnd_3718719] using wordTrace_append hprefix tailTrace_3718719
  have hstable : (prefixWord ++ tailWord_3718719).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3718719).length < 2 ^ (prefixWord ++ tailWord_3718719).sum := by decide
  have hdescent : baseEnd_3718719 < baseStart_3718719 := by decide
  rcases family_descends (prefixWord ++ tailWord_3718719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3718721 : List Nat := [1, 2, 5, 1, 1, 1, 2, 4, 2, 3]
def baseStart_3718721 : Nat := 118140960795 + 3718721 * 2 ^ 59
def prefixEnd_3718721 : Nat := 4983230072969 + 3 ^ 40 * 3718721 * 2
def baseEnd_3718721 : Nat := 1272994195312300147123613

theorem tailTrace_3718721 : CollatzResearch.WordTrace tailWord_3718721 prefixEnd_3718721 1272994195312300147123613 := by
  unfold tailWord_3718721
  simp only [CollatzResearch.WordTrace]
  refine ⟨135632897560716398828460017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90421931707144265885640011 135632897560716398828460017)
  ·
    refine ⟨101724673170537299121345013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135632897560716398828460017 101724673170537299121345013)
    ·
      refine ⟨9536688109737871792626095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 101724673170537299121345013 9536688109737871792626095)
      ·
        refine ⟨14305032164606807688939143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9536688109737871792626095 14305032164606807688939143)
        ·
          refine ⟨21457548246910211533408715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14305032164606807688939143 21457548246910211533408715)
          ·
            refine ⟨32186322370365317300113073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21457548246910211533408715 32186322370365317300113073)
            ·
              refine ⟨24139741777773987975084805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32186322370365317300113073 24139741777773987975084805)
              ·
                refine ⟨4526201583332622745328401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24139741777773987975084805 4526201583332622745328401)
                ·
                  refine ⟨3394651187499467058996301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4526201583332622745328401 3394651187499467058996301)
                  ·
                    refine ⟨1272994195312300147123613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3394651187499467058996301 1272994195312300147123613)
                    ·
                      rfl

theorem cell22_3718721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 2, 4, 2, 3].length) (baseStart_3718721 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3718721 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3718721 prefixEnd_3718721 := by exact prefixLift 3718721
  have htrace : WordTrace (prefixWord ++ tailWord_3718721) baseStart_3718721 baseEnd_3718721 := by
    simpa [prefixWord, tailWord_3718721, baseEnd_3718721] using wordTrace_append hprefix tailTrace_3718721
  have hstable : (prefixWord ++ tailWord_3718721).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3718721).length < 2 ^ (prefixWord ++ tailWord_3718721).sum := by decide
  have hdescent : baseEnd_3718721 < baseStart_3718721 := by decide
  rcases family_descends (prefixWord ++ tailWord_3718721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3718738 : List Nat := [3, 2, 2, 1, 2, 2, 4, 1, 2, 3]
def baseStart_3718738 : Nat := 118140960795 + 3718738 * 2 ^ 59
def prefixEnd_3718738 : Nat := 4983230072969 + 3 ^ 40 * 3718738 * 2
def baseEnd_3718738 : Nat := 1273000014759717769448561

theorem tailTrace_3718738 : CollatzResearch.WordTrace tailWord_3718738 prefixEnd_3718738 1273000014759717769448561 := by
  unfold tailWord_3718738
  simp only [CollatzResearch.WordTrace]
  refine ⟨33908379400413702682957217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90422345067769873821219245 33908379400413702682957217)
  ·
    refine ⟨25431284550310277012217913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33908379400413702682957217 25431284550310277012217913)
    ·
      refine ⟨19073463412732707759163435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25431284550310277012217913 19073463412732707759163435)
      ·
        refine ⟨28610195119099061638745153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19073463412732707759163435 28610195119099061638745153)
        ·
          refine ⟨21457646339324296229058865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28610195119099061638745153 21457646339324296229058865)
          ·
            refine ⟨16093234754493222171794149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21457646339324296229058865 16093234754493222171794149)
            ·
              refine ⟨3017481516467479157211403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16093234754493222171794149 3017481516467479157211403)
              ·
                refine ⟨4526222274701218735817105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3017481516467479157211403 4526222274701218735817105)
                ·
                  refine ⟨3394666706025914051862829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4526222274701218735817105 3394666706025914051862829)
                  ·
                    refine ⟨1273000014759717769448561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3394666706025914051862829 1273000014759717769448561)
                    ·
                      rfl

theorem cell22_3718738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 4, 1, 2, 3].length) (baseStart_3718738 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3718738 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3718738 prefixEnd_3718738 := by exact prefixLift 3718738
  have htrace : WordTrace (prefixWord ++ tailWord_3718738) baseStart_3718738 baseEnd_3718738 := by
    simpa [prefixWord, tailWord_3718738, baseEnd_3718738] using wordTrace_append hprefix tailTrace_3718738
  have hstable : (prefixWord ++ tailWord_3718738).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3718738).length < 2 ^ (prefixWord ++ tailWord_3718738).sum := by decide
  have hdescent : baseEnd_3718738 < baseStart_3718738 := by decide
  rcases family_descends (prefixWord ++ tailWord_3718738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3718742 : List Nat := [5, 2, 2, 2, 1, 2, 1, 2, 1, 4]
def baseStart_3718742 : Nat := 118140960795 + 3718742 * 2 ^ 59
def prefixEnd_3718742 : Nat := 4983230072969 + 3 ^ 40 * 3718742 * 2
def baseEnd_3718742 : Nat := 1273001384041463092348549

theorem tailTrace_3718742 : CollatzResearch.WordTrace tailWord_3718742 prefixEnd_3718742 1273001384041463092348549 := by
  unfold tailWord_3718742
  simp only [CollatzResearch.WordTrace]
  refine ⟨8477103968352519963435905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 90422442329093546276649653 8477103968352519963435905)
  ·
    refine ⟨6357827976264389972576929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8477103968352519963435905 6357827976264389972576929)
    ·
      refine ⟨4768370982198292479432697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6357827976264389972576929 4768370982198292479432697)
      ·
        refine ⟨3576278236648719359574523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4768370982198292479432697 3576278236648719359574523)
        ·
          refine ⟨5364417354973079039361785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3576278236648719359574523 5364417354973079039361785)
          ·
            refine ⟨4023313016229809279521339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5364417354973079039361785 4023313016229809279521339)
            ·
              refine ⟨6034969524344713919282009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4023313016229809279521339 6034969524344713919282009)
              ·
                refine ⟨4526227143258535439461507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6034969524344713919282009 4526227143258535439461507)
                ·
                  refine ⟨6789340714887803159192261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4526227143258535439461507 6789340714887803159192261)
                  ·
                    refine ⟨1273001384041463092348549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6789340714887803159192261 1273001384041463092348549)
                    ·
                      rfl

theorem cell22_3718742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 2, 1, 2, 1, 4].length) (baseStart_3718742 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3718742 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3718742 prefixEnd_3718742 := by exact prefixLift 3718742
  have htrace : WordTrace (prefixWord ++ tailWord_3718742) baseStart_3718742 baseEnd_3718742 := by
    simpa [prefixWord, tailWord_3718742, baseEnd_3718742] using wordTrace_append hprefix tailTrace_3718742
  have hstable : (prefixWord ++ tailWord_3718742).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3718742).length < 2 ^ (prefixWord ++ tailWord_3718742).sum := by decide
  have hdescent : baseEnd_3718742 < baseStart_3718742 := by decide
  rcases family_descends (prefixWord ++ tailWord_3718742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3718779 : List Nat := [1, 1, 1, 1, 1, 4, 6, 2, 5]
def baseStart_3718779 : Nat := 118140960795 + 3718779 * 2 ^ 59
def prefixEnd_3718779 : Nat := 4983230072969 + 3 ^ 40 * 3718779 * 2
def baseEnd_3718779 : Nat := 424338016632535776391145

theorem tailTrace_3718779 : CollatzResearch.WordTrace tailWord_3718779 prefixEnd_3718779 424338016632535776391145 := by
  unfold tailWord_3718779
  simp only [CollatzResearch.WordTrace]
  refine ⟨135635012994506274734071391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90423341996337516489380927 135635012994506274734071391)
  ·
    refine ⟨203452519491759412101107087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135635012994506274734071391 203452519491759412101107087)
    ·
      refine ⟨305178779237639118151660631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203452519491759412101107087 305178779237639118151660631)
      ·
        refine ⟨457768168856458677227490947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 305178779237639118151660631 457768168856458677227490947)
        ·
          refine ⟨686652253284688015841236421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 457768168856458677227490947 686652253284688015841236421)
          ·
            refine ⟨128747297490879002970231829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 686652253284688015841236421 128747297490879002970231829)
            ·
              refine ⟨6035029569884953264229617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 128747297490879002970231829 6035029569884953264229617)
              ·
                refine ⟨4526272177413714948172213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6035029569884953264229617 4526272177413714948172213)
                ·
                  refine ⟨424338016632535776391145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4526272177413714948172213 424338016632535776391145)
                  ·
                    rfl

theorem cell22_3718779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 6, 2, 5].length) (baseStart_3718779 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3718779 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3718779 prefixEnd_3718779 := by exact prefixLift 3718779
  have htrace : WordTrace (prefixWord ++ tailWord_3718779) baseStart_3718779 baseEnd_3718779 := by
    simpa [prefixWord, tailWord_3718779, baseEnd_3718779] using wordTrace_append hprefix tailTrace_3718779
  have hstable : (prefixWord ++ tailWord_3718779).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3718779).length < 2 ^ (prefixWord ++ tailWord_3718779).sum := by decide
  have hdescent : baseEnd_3718779 < baseStart_3718779 := by decide
  rcases family_descends (prefixWord ++ tailWord_3718779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3718794 : List Nat := [3, 1, 2, 3, 2, 1, 1, 1, 1, 7]
def baseStart_3718794 : Nat := 118140960795 + 3718794 * 2 ^ 59
def prefixEnd_3718794 : Nat := 4983230072969 + 3 ^ 40 * 3718794 * 2
def baseEnd_3718794 : Nat := 1273019184704152290048389

theorem tailTrace_3718794 : CollatzResearch.WordTrace tailWord_3718794 prefixEnd_3718794 1273019184704152290048389 := by
  unfold tailWord_3718794
  simp only [CollatzResearch.WordTrace]
  refine ⟨33908890022362983073966859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90423706726301288197244957 33908890022362983073966859)
  ·
    refine ⟨50863335033544474610950289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33908890022362983073966859 50863335033544474610950289)
    ·
      refine ⟨38147501275158355958212717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50863335033544474610950289 38147501275158355958212717)
      ·
        refine ⟨14305312978184383484329769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38147501275158355958212717 14305312978184383484329769)
        ·
          refine ⟨10728984733638287613247327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14305312978184383484329769 10728984733638287613247327)
          ·
            refine ⟨16093477100457431419870991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10728984733638287613247327 16093477100457431419870991)
            ·
              refine ⟨24140215650686147129806487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16093477100457431419870991 24140215650686147129806487)
              ·
                refine ⟨36210323476029220694709731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24140215650686147129806487 36210323476029220694709731)
                ·
                  refine ⟨54315485214043831042064597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36210323476029220694709731 54315485214043831042064597)
                  ·
                    refine ⟨1273019184704152290048389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 54315485214043831042064597 1273019184704152290048389)
                    ·
                      rfl

theorem cell22_3718794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 1, 1, 1, 7].length) (baseStart_3718794 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3718794 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3718794 prefixEnd_3718794 := by exact prefixLift 3718794
  have htrace : WordTrace (prefixWord ++ tailWord_3718794) baseStart_3718794 baseEnd_3718794 := by
    simpa [prefixWord, tailWord_3718794, baseEnd_3718794] using wordTrace_append hprefix tailTrace_3718794
  have hstable : (prefixWord ++ tailWord_3718794).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3718794).length < 2 ^ (prefixWord ++ tailWord_3718794).sum := by decide
  have hdescent : baseEnd_3718794 < baseStart_3718794 := by decide
  rcases family_descends (prefixWord ++ tailWord_3718794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3718830 : List Nat := [4, 1, 4, 1, 2, 2, 1, 2, 5]
def baseStart_3718830 : Nat := 118140960795 + 3718830 * 2 ^ 59
def prefixEnd_3718830 : Nat := 4983230072969 + 3 ^ 40 * 3718830 * 2
def baseEnd_3718830 : Nat := 424343836079953398716093

theorem tailTrace_3718830 : CollatzResearch.WordTrace tailWord_3718830 prefixEnd_3718830 424343836079953398716093 := by
  unfold tailWord_3718830
  simp only [CollatzResearch.WordTrace]
  refine ⟨16954609139665188805522243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 90424582078214340296118629 16954609139665188805522243)
  ·
    refine ⟨25431913709497783208283365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16954609139665188805522243 25431913709497783208283365)
    ·
      refine ⟨4768483820530834351553131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25431913709497783208283365 4768483820530834351553131)
      ·
        refine ⟨7152725730796251527329697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4768483820530834351553131 7152725730796251527329697)
        ·
          refine ⟨5364544298097188645497273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7152725730796251527329697 5364544298097188645497273)
          ·
            refine ⟨4023408223572891484122955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5364544298097188645497273 4023408223572891484122955)
            ·
              refine ⟨6035112335359337226184433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4023408223572891484122955 6035112335359337226184433)
              ·
                refine ⟨4526334251519502919638325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6035112335359337226184433 4526334251519502919638325)
                ·
                  refine ⟨424343836079953398716093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4526334251519502919638325 424343836079953398716093)
                  ·
                    rfl

theorem cell22_3718830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 2, 1, 2, 5].length) (baseStart_3718830 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3718830 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3718830 prefixEnd_3718830 := by exact prefixLift 3718830
  have htrace : WordTrace (prefixWord ++ tailWord_3718830) baseStart_3718830 baseEnd_3718830 := by
    simpa [prefixWord, tailWord_3718830, baseEnd_3718830] using wordTrace_append hprefix tailTrace_3718830
  have hstable : (prefixWord ++ tailWord_3718830).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3718830).length < 2 ^ (prefixWord ++ tailWord_3718830).sum := by decide
  have hdescent : baseEnd_3718830 < baseStart_3718830 := by decide
  rcases family_descends (prefixWord ++ tailWord_3718830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3718841 : List Nat := [1, 2, 1, 4, 1, 1, 4, 4, 4]
def baseStart_3718841 : Nat := 118140960795 + 3718841 * 2 ^ 59
def prefixEnd_3718841 : Nat := 4983230072969 + 3 ^ 40 * 3718841 * 2
def baseEnd_3718841 : Nat := 424345091254886611374415

theorem tailTrace_3718841 : CollatzResearch.WordTrace tailWord_3718841 prefixEnd_3718841 424345091254886611374415 := by
  unfold tailWord_3718841
  simp only [CollatzResearch.WordTrace]
  refine ⟨135637274320281659322828377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90424849546854439548552251 135637274320281659322828377)
  ·
    refine ⟨101727955740211244492121283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135637274320281659322828377 101727955740211244492121283)
    ·
      refine ⟨152591933610316866738181925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101727955740211244492121283 152591933610316866738181925)
      ·
        refine ⟨28610987551934412513409111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 152591933610316866738181925 28610987551934412513409111)
        ·
          refine ⟨42916481327901618770113667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28610987551934412513409111 42916481327901618770113667)
          ·
            refine ⟨64374721991852428155170501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42916481327901618770113667 64374721991852428155170501)
            ·
              refine ⟨12070260373472330279094469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 64374721991852428155170501 12070260373472330279094469)
              ·
                refine ⟨2263173820026061927330213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12070260373472330279094469 2263173820026061927330213)
                ·
                  refine ⟨424345091254886611374415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2263173820026061927330213 424345091254886611374415)
                  ·
                    rfl

theorem cell22_3718841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 4, 4, 4].length) (baseStart_3718841 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3718841 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3718841 prefixEnd_3718841 := by exact prefixLift 3718841
  have htrace : WordTrace (prefixWord ++ tailWord_3718841) baseStart_3718841 baseEnd_3718841 := by
    simpa [prefixWord, tailWord_3718841, baseEnd_3718841] using wordTrace_append hprefix tailTrace_3718841
  have hstable : (prefixWord ++ tailWord_3718841).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3718841).length < 2 ^ (prefixWord ++ tailWord_3718841).sum := by decide
  have hdescent : baseEnd_3718841 < baseStart_3718841 := by decide
  rcases family_descends (prefixWord ++ tailWord_3718841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3718929 : List Nat := [1, 2, 2, 1, 1, 3, 1, 2, 4, 5]
def baseStart_3718929 : Nat := 118140960795 + 3718929 * 2 ^ 59
def prefixEnd_3718929 : Nat := 4983230072969 + 3 ^ 40 * 3718929 * 2
def baseEnd_3718929 : Nat := 1273065397963056937922975

theorem tailTrace_3718929 : CollatzResearch.WordTrace tailWord_3718929 prefixEnd_3718929 1273065397963056937922975 := by
  unfold tailWord_3718929
  simp only [CollatzResearch.WordTrace]
  refine ⟨135640483943962850352031841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90426989295975233568021227 135640483943962850352031841)
  ·
    refine ⟨101730362957972137764023881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135640483943962850352031841 101730362957972137764023881)
    ·
      refine ⟨76297772218479103323017911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101730362957972137764023881 76297772218479103323017911)
      ·
        refine ⟨114446658327718654984526867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76297772218479103323017911 114446658327718654984526867)
        ·
          refine ⟨171669987491577982476790301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114446658327718654984526867 171669987491577982476790301)
          ·
            refine ⟨64376245309341743428796363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 171669987491577982476790301 64376245309341743428796363)
            ·
              refine ⟨96564367964012615143194545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64376245309341743428796363 96564367964012615143194545)
              ·
                refine ⟨72423275973009461357395909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 96564367964012615143194545 72423275973009461357395909)
                ·
                  refine ⟨13579364244939274004511733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 72423275973009461357395909 13579364244939274004511733)
                  ·
                    refine ⟨1273065397963056937922975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13579364244939274004511733 1273065397963056937922975)
                    ·
                      rfl

theorem cell22_3718929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 5].length) (baseStart_3718929 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3718929 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3718929 prefixEnd_3718929 := by exact prefixLift 3718929
  have htrace : WordTrace (prefixWord ++ tailWord_3718929) baseStart_3718929 baseEnd_3718929 := by
    simpa [prefixWord, tailWord_3718929, baseEnd_3718929] using wordTrace_append hprefix tailTrace_3718929
  have hstable : (prefixWord ++ tailWord_3718929).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3718929).length < 2 ^ (prefixWord ++ tailWord_3718929).sum := by decide
  have hdescent : baseEnd_3718929 < baseStart_3718929 := by decide
  rcases family_descends (prefixWord ++ tailWord_3718929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3718946 : List Nat := [3, 3, 1, 1, 2, 1, 2, 2, 2, 5]
def baseStart_3718946 : Nat := 118140960795 + 3718946 * 2 ^ 59
def prefixEnd_3718946 : Nat := 4983230072969 + 3 ^ 40 * 3718946 * 2
def baseEnd_3718946 : Nat := 1273071217410474560247923

theorem tailTrace_3718946 : CollatzResearch.WordTrace tailWord_3718946 prefixEnd_3718946 1273071217410474560247923 := by
  unfold tailWord_3718946
  simp only [CollatzResearch.WordTrace]
  refine ⟨33910275996225315563850173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90427402656600841503600461 33910275996225315563850173)
  ·
    refine ⟨12716353498584493336443815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33910275996225315563850173 12716353498584493336443815)
    ·
      refine ⟨19074530247876740004665723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12716353498584493336443815 19074530247876740004665723)
      ·
        refine ⟨28611795371815110006998585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19074530247876740004665723 28611795371815110006998585)
        ·
          refine ⟨21458846528861332505248939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28611795371815110006998585 21458846528861332505248939)
          ·
            refine ⟨32188269793291998757873409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21458846528861332505248939 32188269793291998757873409)
            ·
              refine ⟨24141202344968999068405057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32188269793291998757873409 24141202344968999068405057)
              ·
                refine ⟨18105901758726749301303793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24141202344968999068405057 18105901758726749301303793)
                ·
                  refine ⟨13579426319045061975977845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18105901758726749301303793 13579426319045061975977845)
                  ·
                    refine ⟨1273071217410474560247923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13579426319045061975977845 1273071217410474560247923)
                    ·
                      rfl

theorem cell22_3718946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 2, 2, 2, 5].length) (baseStart_3718946 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3718946 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3718946 prefixEnd_3718946 := by exact prefixLift 3718946
  have htrace : WordTrace (prefixWord ++ tailWord_3718946) baseStart_3718946 baseEnd_3718946 := by
    simpa [prefixWord, tailWord_3718946, baseEnd_3718946] using wordTrace_append hprefix tailTrace_3718946
  have hstable : (prefixWord ++ tailWord_3718946).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3718946).length < 2 ^ (prefixWord ++ tailWord_3718946).sum := by decide
  have hdescent : baseEnd_3718946 < baseStart_3718946 := by decide
  rcases family_descends (prefixWord ++ tailWord_3718946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3718948 : List Nat := [2, 3, 1, 3, 2, 2, 2, 2, 5]
def baseStart_3718948 : Nat := 118140960795 + 3718948 * 2 ^ 59
def prefixEnd_3718948 : Nat := 4983230072969 + 3 ^ 40 * 3718948 * 2
def baseEnd_3718948 : Nat := 424357300683782407232639

theorem tailTrace_3718948 : CollatzResearch.WordTrace tailWord_3718948 prefixEnd_3718948 424357300683782407232639 := by
  unfold tailWord_3718948
  simp only [CollatzResearch.WordTrace]
  refine ⟨67820588465447008298486749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90427451287262677731315665 67820588465447008298486749)
  ·
    refine ⟨25432720674542628111932531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67820588465447008298486749 25432720674542628111932531)
    ·
      refine ⟨38149081011813942167898797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25432720674542628111932531 38149081011813942167898797)
      ·
        refine ⟨14305905379430228312962049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38149081011813942167898797 14305905379430228312962049)
        ·
          refine ⟨10729429034572671234721537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14305905379430228312962049 10729429034572671234721537)
          ·
            refine ⟨8047071775929503426041153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10729429034572671234721537 8047071775929503426041153)
            ·
              refine ⟨6035303831947127569530865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8047071775929503426041153 6035303831947127569530865)
              ·
                refine ⟨4526477873960345677148149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6035303831947127569530865 4526477873960345677148149)
                ·
                  refine ⟨424357300683782407232639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4526477873960345677148149 424357300683782407232639)
                  ·
                    rfl

theorem cell22_3718948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 2, 2, 5].length) (baseStart_3718948 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3718948 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3718948 prefixEnd_3718948 := by exact prefixLift 3718948
  have htrace : WordTrace (prefixWord ++ tailWord_3718948) baseStart_3718948 baseEnd_3718948 := by
    simpa [prefixWord, tailWord_3718948, baseEnd_3718948] using wordTrace_append hprefix tailTrace_3718948
  have hstable : (prefixWord ++ tailWord_3718948).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3718948).length < 2 ^ (prefixWord ++ tailWord_3718948).sum := by decide
  have hdescent : baseEnd_3718948 < baseStart_3718948 := by decide
  rcases family_descends (prefixWord ++ tailWord_3718948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3718952 : List Nat := [2, 1, 5, 1, 1, 2, 4, 2, 1, 3]
def baseStart_3718952 : Nat := 118140960795 + 3718952 * 2 ^ 59
def prefixEnd_3718952 : Nat := 4983230072969 + 3 ^ 40 * 3718952 * 2
def baseEnd_3718952 : Nat := 1273073271333092544597905

theorem tailTrace_3718952 : CollatzResearch.WordTrace tailWord_3718952 prefixEnd_3718952 1273073271333092544597905 := by
  unfold tailWord_3718952
  simp only [CollatzResearch.WordTrace]
  refine ⟨67820661411439762640059555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90427548548586350186746073 67820661411439762640059555)
  ·
    refine ⟨101730992117159643960089333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67820661411439762640059555 101730992117159643960089333)
    ·
      refine ⟨9537280510983716621258375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 101730992117159643960089333 9537280510983716621258375)
      ·
        refine ⟨14305920766475574931887563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9537280510983716621258375 14305920766475574931887563)
        ·
          refine ⟨21458881149713362397831345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14305920766475574931887563 21458881149713362397831345)
          ·
            refine ⟨16094160862285021798373509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21458881149713362397831345 16094160862285021798373509)
            ·
              refine ⟨3017655161678441587195033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16094160862285021798373509 3017655161678441587195033)
              ·
                refine ⟨2263241371258831190396275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3017655161678441587195033 2263241371258831190396275)
                ·
                  refine ⟨3394862056888246785594413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2263241371258831190396275 3394862056888246785594413)
                  ·
                    refine ⟨1273073271333092544597905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3394862056888246785594413 1273073271333092544597905)
                    ·
                      rfl

theorem cell22_3718952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 4, 2, 1, 3].length) (baseStart_3718952 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3718952 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3718952 prefixEnd_3718952 := by exact prefixLift 3718952
  have htrace : WordTrace (prefixWord ++ tailWord_3718952) baseStart_3718952 baseEnd_3718952 := by
    simpa [prefixWord, tailWord_3718952, baseEnd_3718952] using wordTrace_append hprefix tailTrace_3718952
  have hstable : (prefixWord ++ tailWord_3718952).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3718952).length < 2 ^ (prefixWord ++ tailWord_3718952).sum := by decide
  have hdescent : baseEnd_3718952 < baseStart_3718952 := by decide
  rcases family_descends (prefixWord ++ tailWord_3718952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3718961 : List Nat := [1, 2, 2, 3, 2, 2, 1, 2, 3, 4]
def baseStart_3718961 : Nat := 118140960795 + 3718961 * 2 ^ 59
def prefixEnd_3718961 : Nat := 4983230072969 + 3 ^ 40 * 3718961 * 2
def baseEnd_3718961 : Nat := 1273076352217019521122877

theorem tailTrace_3718961 : CollatzResearch.WordTrace tailWord_3718961 prefixEnd_3718961 1273076352217019521122877 := by
  unfold tailWord_3718961
  simp only [CollatzResearch.WordTrace]
  refine ⟨135641651079846919817196737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90427767386564613211464491 135641651079846919817196737)
  ·
    refine ⟨101731238309885189862897553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135641651079846919817196737 101731238309885189862897553)
    ·
      refine ⟨76298428732413892397173165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101731238309885189862897553 76298428732413892397173165)
      ·
        refine ⟨28611910774655209648939937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76298428732413892397173165 28611910774655209648939937)
        ·
          refine ⟨21458933080991407236704953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28611910774655209648939937 21458933080991407236704953)
          ·
            refine ⟨16094199810743555427528715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21458933080991407236704953 16094199810743555427528715)
            ·
              refine ⟨24141299716115333141293073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16094199810743555427528715 24141299716115333141293073)
              ·
                refine ⟨18105974787086499855969805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24141299716115333141293073 18105974787086499855969805)
                ·
                  refine ⟨6789740545157437445988677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18105974787086499855969805 6789740545157437445988677)
                  ·
                    refine ⟨1273076352217019521122877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6789740545157437445988677 1273076352217019521122877)
                    ·
                      rfl

theorem cell22_3718961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 1, 2, 3, 4].length) (baseStart_3718961 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3718961 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3718961 prefixEnd_3718961 := by exact prefixLift 3718961
  have htrace : WordTrace (prefixWord ++ tailWord_3718961) baseStart_3718961 baseEnd_3718961 := by
    simpa [prefixWord, tailWord_3718961, baseEnd_3718961] using wordTrace_append hprefix tailTrace_3718961
  have hstable : (prefixWord ++ tailWord_3718961).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3718961).length < 2 ^ (prefixWord ++ tailWord_3718961).sum := by decide
  have hdescent : baseEnd_3718961 < baseStart_3718961 := by decide
  rcases family_descends (prefixWord ++ tailWord_3718961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3718993 : List Nat := [1, 2, 2, 1, 5, 1, 1, 5, 4]
def baseStart_3718993 : Nat := 118140960795 + 3718993 * 2 ^ 59
def prefixEnd_3718993 : Nat := 4983230072969 + 3 ^ 40 * 3718993 * 2
def baseEnd_3718993 : Nat := 424362435490327368107593

theorem tailTrace_3718993 : CollatzResearch.WordTrace tailWord_3718993 prefixEnd_3718993 424362435490327368107593 := by
  unfold tailWord_3718993
  simp only [CollatzResearch.WordTrace]
  refine ⟨135642818215730989282361633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90428545477153992854907755 135642818215730989282361633)
  ·
    refine ⟨101732113661798241961771225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135642818215730989282361633 101732113661798241961771225)
    ·
      refine ⟨76299085246348681471328419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101732113661798241961771225 76299085246348681471328419)
      ·
        refine ⟨114448627869523022206992629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76299085246348681471328419 114448627869523022206992629)
        ·
          refine ⟨10729558862767783331905559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 114448627869523022206992629 10729558862767783331905559)
          ·
            refine ⟨16094338294151674997858339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10729558862767783331905559 16094338294151674997858339)
            ·
              refine ⟨24141507441227512496787509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16094338294151674997858339 24141507441227512496787509)
              ·
                refine ⟨2263266322615079296573829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24141507441227512496787509 2263266322615079296573829)
                ·
                  refine ⟨424362435490327368107593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2263266322615079296573829 424362435490327368107593)
                  ·
                    rfl

theorem cell22_3718993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 1, 5, 4].length) (baseStart_3718993 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3718993 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3718993 prefixEnd_3718993 := by exact prefixLift 3718993
  have htrace : WordTrace (prefixWord ++ tailWord_3718993) baseStart_3718993 baseEnd_3718993 := by
    simpa [prefixWord, tailWord_3718993, baseEnd_3718993] using wordTrace_append hprefix tailTrace_3718993
  have hstable : (prefixWord ++ tailWord_3718993).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3718993).length < 2 ^ (prefixWord ++ tailWord_3718993).sum := by decide
  have hdescent : baseEnd_3718993 < baseStart_3718993 := by decide
  rcases family_descends (prefixWord ++ tailWord_3718993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3719008 : List Nat := [2, 1, 1, 3, 3, 3, 1, 1, 4, 3]
def baseStart_3719008 : Nat := 118140960795 + 3719008 * 2 ^ 59
def prefixEnd_3719008 : Nat := 4983230072969 + 3 ^ 40 * 3719008 * 2
def baseEnd_3719008 : Nat := 1273092441277527065197733

theorem tailTrace_3719008 : CollatzResearch.WordTrace tailWord_3719008 prefixEnd_3719008 1273092441277527065197733 := by
  unfold tailWord_3719008
  simp only [CollatzResearch.WordTrace]
  refine ⟨67821682655338323422078839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90428910207117764562771785 67821682655338323422078839)
  ·
    refine ⟨101732523983007485133118259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67821682655338323422078839 101732523983007485133118259)
    ·
      refine ⟨152598785974511227699677389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101732523983007485133118259 152598785974511227699677389)
      ·
        refine ⟨57224544740441710387379021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 152598785974511227699677389 57224544740441710387379021)
        ·
          refine ⟨21459204277665641395267133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57224544740441710387379021 21459204277665641395267133)
          ·
            refine ⟨8047201604124615523225175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21459204277665641395267133 8047201604124615523225175)
            ·
              refine ⟨12070802406186923284837763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8047201604124615523225175 12070802406186923284837763)
              ·
                refine ⟨18106203609280384927256645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12070802406186923284837763 18106203609280384927256645)
                ·
                  refine ⟨3394913176740072173860621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18106203609280384927256645 3394913176740072173860621)
                  ·
                    refine ⟨1273092441277527065197733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3394913176740072173860621 1273092441277527065197733)
                    ·
                      rfl

theorem cell22_3719008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 1, 1, 4, 3].length) (baseStart_3719008 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3719008 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3719008 prefixEnd_3719008 := by exact prefixLift 3719008
  have htrace : WordTrace (prefixWord ++ tailWord_3719008) baseStart_3719008 baseEnd_3719008 := by
    simpa [prefixWord, tailWord_3719008, baseEnd_3719008] using wordTrace_append hprefix tailTrace_3719008
  have hstable : (prefixWord ++ tailWord_3719008).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3719008).length < 2 ^ (prefixWord ++ tailWord_3719008).sum := by decide
  have hdescent : baseEnd_3719008 < baseStart_3719008 := by decide
  rcases family_descends (prefixWord ++ tailWord_3719008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3719010 : List Nat := [3, 3, 2, 1, 2, 1, 2, 4, 4]
def baseStart_3719010 : Nat := 118140960795 + 3719010 * 2 ^ 59
def prefixEnd_3719010 : Nat := 4983230072969 + 3 ^ 40 * 3719010 * 2
def baseEnd_3719010 : Nat := 424364375306133242215909

theorem tailTrace_3719010 : CollatzResearch.WordTrace tailWord_3719010 prefixEnd_3719010 424364375306133242215909 := by
  unfold tailWord_3719010
  simp only [CollatzResearch.WordTrace]
  refine ⟨33910859564167350296432621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90428958837779600790486989 33910859564167350296432621)
  ·
    refine ⟨12716572336562756361162233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33910859564167350296432621 12716572336562756361162233)
    ·
      refine ⟨9537429252422067270871675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12716572336562756361162233 9537429252422067270871675)
      ·
        refine ⟨14306143878633100906307513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9537429252422067270871675 14306143878633100906307513)
        ·
          refine ⟨10729607908974825679730635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14306143878633100906307513 10729607908974825679730635)
          ·
            refine ⟨16094411863462238519595953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10729607908974825679730635 16094411863462238519595953)
            ·
              refine ⟨12070808897596678889696965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16094411863462238519595953 12070808897596678889696965)
              ·
                refine ⟨2263276668299377291818181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12070808897596678889696965 2263276668299377291818181)
                ·
                  refine ⟨424364375306133242215909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2263276668299377291818181 424364375306133242215909)
                  ·
                    rfl

theorem cell22_3719010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 2, 4, 4].length) (baseStart_3719010 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3719010 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3719010 prefixEnd_3719010 := by exact prefixLift 3719010
  have htrace : WordTrace (prefixWord ++ tailWord_3719010) baseStart_3719010 baseEnd_3719010 := by
    simpa [prefixWord, tailWord_3719010, baseEnd_3719010] using wordTrace_append hprefix tailTrace_3719010
  have hstable : (prefixWord ++ tailWord_3719010).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3719010).length < 2 ^ (prefixWord ++ tailWord_3719010).sum := by decide
  have hdescent : baseEnd_3719010 < baseStart_3719010 := by decide
  rcases family_descends (prefixWord ++ tailWord_3719010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3719025 : List Nat := [1, 2, 2, 2, 1, 3, 5, 1, 2, 3]
def baseStart_3719025 : Nat := 118140960795 + 3719025 * 2 ^ 59
def prefixEnd_3719025 : Nat := 4983230072969 + 3 ^ 40 * 3719025 * 2
def baseEnd_3719025 : Nat := 1273098260724944687522681

theorem tailTrace_3719025 : CollatzResearch.WordTrace tailWord_3719025 prefixEnd_3719025 1273098260724944687522681 := by
  unfold tailWord_3719025
  simp only [CollatzResearch.WordTrace]
  refine ⟨135643985351615058747526529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90429323567743372498351019 135643985351615058747526529)
  ·
    refine ⟨101732989013711294060644897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135643985351615058747526529 101732989013711294060644897)
    ·
      refine ⟨76299741760283470545483673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101732989013711294060644897 76299741760283470545483673)
      ·
        refine ⟨57224806320212602909112755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76299741760283470545483673 57224806320212602909112755)
        ·
          refine ⟨85837209480318904363669133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57224806320212602909112755 85837209480318904363669133)
          ·
            refine ⟨32188953555119589136375925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 85837209480318904363669133 32188953555119589136375925)
            ·
              refine ⟨3017714395792461481535243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 32188953555119589136375925 3017714395792461481535243)
              ·
                refine ⟨4526571593688692222302865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3017714395792461481535243 4526571593688692222302865)
                ·
                  refine ⟨3394928695266519166727149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4526571593688692222302865 3394928695266519166727149)
                  ·
                    refine ⟨1273098260724944687522681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3394928695266519166727149 1273098260724944687522681)
                    ·
                      rfl

theorem cell22_3719025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 5, 1, 2, 3].length) (baseStart_3719025 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3719025 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3719025 prefixEnd_3719025 := by exact prefixLift 3719025
  have htrace : WordTrace (prefixWord ++ tailWord_3719025) baseStart_3719025 baseEnd_3719025 := by
    simpa [prefixWord, tailWord_3719025, baseEnd_3719025] using wordTrace_append hprefix tailTrace_3719025
  have hstable : (prefixWord ++ tailWord_3719025).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3719025).length < 2 ^ (prefixWord ++ tailWord_3719025).sum := by decide
  have hdescent : baseEnd_3719025 < baseStart_3719025 := by decide
  rcases family_descends (prefixWord ++ tailWord_3719025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3719171 : List Nat := [1, 1, 1, 3, 2, 1, 1, 2, 1, 9]
def baseStart_3719171 : Nat := 118140960795 + 3719171 * 2 ^ 59
def prefixEnd_3719171 : Nat := 4983230072969 + 3 ^ 40 * 3719171 * 2
def baseEnd_3719171 : Nat := 1273148239508648973372233

theorem tailTrace_3719171 : CollatzResearch.WordTrace tailWord_3719171 prefixEnd_3719171 1273148239508648973372233 := by
  unfold tailWord_3719171
  simp only [CollatzResearch.WordTrace]
  refine ⟨135649310409086125682341367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90432873606057417121560911 135649310409086125682341367)
  ·
    refine ⟨203473965613629188523512051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135649310409086125682341367 203473965613629188523512051)
    ·
      refine ⟨305210948420443782785268077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203473965613629188523512051 305210948420443782785268077)
      ·
        refine ⟨114454105657666418544475529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 305210948420443782785268077 114454105657666418544475529)
        ·
          refine ⟨85840579243249813908356647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114454105657666418544475529 85840579243249813908356647)
          ·
            refine ⟨128760868864874720862534971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85840579243249813908356647 128760868864874720862534971)
            ·
              refine ⟨193141303297312081293802457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 128760868864874720862534971 193141303297312081293802457)
              ·
                refine ⟨144855977472984060970351843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 193141303297312081293802457 144855977472984060970351843)
                ·
                  refine ⟨217283966209476091455527765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 144855977472984060970351843 217283966209476091455527765)
                  ·
                    refine ⟨1273148239508648973372233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 217283966209476091455527765 1273148239508648973372233)
                    ·
                      rfl

theorem cell22_3719171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 2, 1, 9].length) (baseStart_3719171 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3719171 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3719171 prefixEnd_3719171 := by exact prefixLift 3719171
  have htrace : WordTrace (prefixWord ++ tailWord_3719171) baseStart_3719171 baseEnd_3719171 := by
    simpa [prefixWord, tailWord_3719171, baseEnd_3719171] using wordTrace_append hprefix tailTrace_3719171
  have hstable : (prefixWord ++ tailWord_3719171).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3719171).length < 2 ^ (prefixWord ++ tailWord_3719171).sum := by decide
  have hdescent : baseEnd_3719171 < baseStart_3719171 := by decide
  rcases family_descends (prefixWord ++ tailWord_3719171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3719205 : List Nat := [1, 3, 1, 2, 2, 3, 2, 2, 3, 3]
def baseStart_3719205 : Nat := 118140960795 + 3719205 * 2 ^ 59
def prefixEnd_3719205 : Nat := 4983230072969 + 3 ^ 40 * 3719205 * 2
def baseEnd_3719205 : Nat := 1273159878403484218022129

theorem tailTrace_3719205 : CollatzResearch.WordTrace tailWord_3719205 prefixEnd_3719205 1273159878403484218022129 := by
  unfold tailWord_3719205
  simp only [CollatzResearch.WordTrace]
  refine ⟨135650550490962949489079069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90433700327308632992719379 135650550490962949489079069)
  ·
    refine ⟨50868956434111106058404651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135650550490962949489079069 50868956434111106058404651)
    ·
      refine ⟨76303434651166659087606977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50868956434111106058404651 76303434651166659087606977)
      ·
        refine ⟨57227575988374994315705233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76303434651166659087606977 57227575988374994315705233)
        ·
          refine ⟨42920681991281245736778925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57227575988374994315705233 42920681991281245736778925)
          ·
            refine ⟨16095255746730467151292097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42920681991281245736778925 16095255746730467151292097)
            ·
              refine ⟨12071441810047850363469073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16095255746730467151292097 12071441810047850363469073)
              ·
                refine ⟨9053581357535887772601805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12071441810047850363469073 9053581357535887772601805)
                ·
                  refine ⟨3395093009075957914725677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9053581357535887772601805 3395093009075957914725677)
                  ·
                    refine ⟨1273159878403484218022129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3395093009075957914725677 1273159878403484218022129)
                    ·
                      rfl

theorem cell22_3719205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 2, 2, 3, 3].length) (baseStart_3719205 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3719205 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3719205 prefixEnd_3719205 := by exact prefixLift 3719205
  have htrace : WordTrace (prefixWord ++ tailWord_3719205) baseStart_3719205 baseEnd_3719205 := by
    simpa [prefixWord, tailWord_3719205, baseEnd_3719205] using wordTrace_append hprefix tailTrace_3719205
  have hstable : (prefixWord ++ tailWord_3719205).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3719205).length < 2 ^ (prefixWord ++ tailWord_3719205).sum := by decide
  have hdescent : baseEnd_3719205 < baseStart_3719205 := by decide
  rcases family_descends (prefixWord ++ tailWord_3719205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3719218 : List Nat := [3, 2, 1, 1, 2, 3, 1, 2, 7]
def baseStart_3719218 : Nat := 118140960795 + 3719218 * 2 ^ 59
def prefixEnd_3719218 : Nat := 4983230072969 + 3 ^ 40 * 3719218 * 2
def baseEnd_3719218 : Nat := 424388109523052172482363

theorem tailTrace_3719218 : CollatzResearch.WordTrace tailWord_3719218 prefixEnd_3719218 424388109523052172482363 := by
  unfold tailWord_3719218
  simp only [CollatzResearch.WordTrace]
  refine ⟨33912756159978963177325577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90434016426610568472868205 33912756159978963177325577)
  ·
    refine ⟨25434567119984222382994183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33912756159978963177325577 25434567119984222382994183)
    ·
      refine ⟨38151850679976333574491275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25434567119984222382994183 38151850679976333574491275)
      ·
        refine ⟨57227776019964500361736913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38151850679976333574491275 57227776019964500361736913)
        ·
          refine ⟨42920832014973375271302685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57227776019964500361736913 42920832014973375271302685)
          ·
            refine ⟨16095312005615015726738507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42920832014973375271302685 16095312005615015726738507)
            ·
              refine ⟨24142968008422523590107761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16095312005615015726738507 24142968008422523590107761)
              ·
                refine ⟨18107226006316892692580821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24142968008422523590107761 18107226006316892692580821)
                ·
                  refine ⟨424388109523052172482363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18107226006316892692580821 424388109523052172482363)
                  ·
                    rfl

theorem cell22_3719218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 1, 2, 7].length) (baseStart_3719218 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3719218 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3719218 prefixEnd_3719218 := by exact prefixLift 3719218
  have htrace : WordTrace (prefixWord ++ tailWord_3719218) baseStart_3719218 baseEnd_3719218 := by
    simpa [prefixWord, tailWord_3719218, baseEnd_3719218] using wordTrace_append hprefix tailTrace_3719218
  have hstable : (prefixWord ++ tailWord_3719218).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3719218).length < 2 ^ (prefixWord ++ tailWord_3719218).sum := by decide
  have hdescent : baseEnd_3719218 < baseStart_3719218 := by decide
  rcases family_descends (prefixWord ++ tailWord_3719218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3719239 : List Nat := [1, 1, 4, 1, 3, 1, 5, 2, 1, 3]
def baseStart_3719239 : Nat := 118140960795 + 3719239 * 2 ^ 59
def prefixEnd_3719239 : Nat := 4983230072969 + 3 ^ 40 * 3719239 * 2
def baseEnd_3719239 : Nat := 1273171517298319462672025

theorem tailTrace_3719239 : CollatzResearch.WordTrace tailWord_3719239 prefixEnd_3719239 1273171517298319462672025 := by
  unfold tailWord_3719239
  simp only [CollatzResearch.WordTrace]
  refine ⟨135651790572839773295816771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90434527048559848863877847 135651790572839773295816771)
  ·
    refine ⟨203477685859259659943725157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135651790572839773295816771 203477685859259659943725157)
    ·
      refine ⟨38152066098611186239448467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 203477685859259659943725157 38152066098611186239448467)
      ·
        refine ⟨57228099147916779359172701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38152066098611186239448467 57228099147916779359172701)
        ·
          refine ⟨21460537180468792259689763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57228099147916779359172701 21460537180468792259689763)
          ·
            refine ⟨32190805770703188389534645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21460537180468792259689763 32190805770703188389534645)
            ·
              refine ⟨3017888041003423911518873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 32190805770703188389534645 3017888041003423911518873)
              ·
                refine ⟨2263416030752567933639155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3017888041003423911518873 2263416030752567933639155)
                ·
                  refine ⟨3395124046128851900458733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2263416030752567933639155 3395124046128851900458733)
                  ·
                    refine ⟨1273171517298319462672025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3395124046128851900458733 1273171517298319462672025)
                    ·
                      rfl

theorem cell22_3719239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 5, 2, 1, 3].length) (baseStart_3719239 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3719239 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3719239 prefixEnd_3719239 := by exact prefixLift 3719239
  have htrace : WordTrace (prefixWord ++ tailWord_3719239) baseStart_3719239 baseEnd_3719239 := by
    simpa [prefixWord, tailWord_3719239, baseEnd_3719239] using wordTrace_append hprefix tailTrace_3719239
  have hstable : (prefixWord ++ tailWord_3719239).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3719239).length < 2 ^ (prefixWord ++ tailWord_3719239).sum := by decide
  have hdescent : baseEnd_3719239 < baseStart_3719239 := by decide
  rcases family_descends (prefixWord ++ tailWord_3719239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3719327 : List Nat := [1, 1, 2, 6, 1, 1, 3, 1, 2, 4]
def baseStart_3719327 : Nat := 118140960795 + 3719327 * 2 ^ 59
def prefixEnd_3719327 : Nat := 4983230072969 + 3 ^ 40 * 3719327 * 2
def baseEnd_3719327 : Nat := 1273201641496716566471755

theorem tailTrace_3719327 : CollatzResearch.WordTrace tailWord_3719327 prefixEnd_3719327 1273201641496716566471755 := by
  unfold tailWord_3719327
  simp only [CollatzResearch.WordTrace]
  refine ⟨135655000196520964325020235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90436666797680642883346823 135655000196520964325020235)
  ·
    refine ⟨203482500294781446487530353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135655000196520964325020235 203482500294781446487530353)
    ·
      refine ⟨152611875221086084865647765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 203482500294781446487530353 152611875221086084865647765)
      ·
        refine ⟨7153681650988410228077239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 152611875221086084865647765 7153681650988410228077239)
        ·
          refine ⟨10730522476482615342115859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7153681650988410228077239 10730522476482615342115859)
          ·
            refine ⟨16095783714723923013173789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10730522476482615342115859 16095783714723923013173789)
            ·
              refine ⟨6035918893021471129940171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16095783714723923013173789 6035918893021471129940171)
              ·
                refine ⟨9053878339532206694910257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6035918893021471129940171 9053878339532206694910257)
                ·
                  refine ⟨6790408754649155021182693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9053878339532206694910257 6790408754649155021182693)
                  ·
                    refine ⟨1273201641496716566471755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6790408754649155021182693 1273201641496716566471755)
                    ·
                      rfl

theorem cell22_3719327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 3, 1, 2, 4].length) (baseStart_3719327 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3719327 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3719327 prefixEnd_3719327 := by exact prefixLift 3719327
  have htrace : WordTrace (prefixWord ++ tailWord_3719327) baseStart_3719327 baseEnd_3719327 := by
    simpa [prefixWord, tailWord_3719327, baseEnd_3719327] using wordTrace_append hprefix tailTrace_3719327
  have hstable : (prefixWord ++ tailWord_3719327).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3719327).length < 2 ^ (prefixWord ++ tailWord_3719327).sum := by decide
  have hdescent : baseEnd_3719327 < baseStart_3719327 := by decide
  rcases family_descends (prefixWord ++ tailWord_3719327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3719445 : List Nat := [1, 3, 2, 1, 2, 1, 2, 3, 1, 6]
def baseStart_3719445 : Nat := 118140960795 + 3719445 * 2 ^ 59
def prefixEnd_3719445 : Nat := 4983230072969 + 3 ^ 40 * 3719445 * 2
def baseEnd_3719445 : Nat := 1273242035308203592021393

theorem tailTrace_3719445 : CollatzResearch.WordTrace tailWord_3719445 prefixEnd_3719445 1273242035308203592021393 := by
  unfold tailWord_3719445
  simp only [CollatzResearch.WordTrace]
  refine ⟨135659304010093470477815789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90439536006728980318543859 135659304010093470477815789)
  ·
    refine ⟨50872239003785051429180921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135659304010093470477815789 50872239003785051429180921)
    ·
      refine ⟨38154179252838788571885691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50872239003785051429180921 38154179252838788571885691)
      ·
        refine ⟨57231268879258182857828537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38154179252838788571885691 57231268879258182857828537)
        ·
          refine ⟨42923451659443637143371403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57231268879258182857828537 42923451659443637143371403)
          ·
            refine ⟨64385177489165455715057105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42923451659443637143371403 64385177489165455715057105)
            ·
              refine ⟨48288883116874091786292829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64385177489165455715057105 48288883116874091786292829)
              ·
                refine ⟨18108331168827784419859811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48288883116874091786292829 18108331168827784419859811)
                ·
                  refine ⟨27162496753241676629789717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18108331168827784419859811 27162496753241676629789717)
                  ·
                    refine ⟨1273242035308203592021393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27162496753241676629789717 1273242035308203592021393)
                    ·
                      rfl

theorem cell22_3719445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 3, 1, 6].length) (baseStart_3719445 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3719445 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3719445 prefixEnd_3719445 := by exact prefixLift 3719445
  have htrace : WordTrace (prefixWord ++ tailWord_3719445) baseStart_3719445 baseEnd_3719445 := by
    simpa [prefixWord, tailWord_3719445, baseEnd_3719445] using wordTrace_append hprefix tailTrace_3719445
  have hstable : (prefixWord ++ tailWord_3719445).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3719445).length < 2 ^ (prefixWord ++ tailWord_3719445).sum := by decide
  have hdescent : baseEnd_3719445 < baseStart_3719445 := by decide
  rcases family_descends (prefixWord ++ tailWord_3719445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3719447 : List Nat := [1, 1, 3, 4, 1, 3, 1, 2, 1, 5]
def baseStart_3719447 : Nat := 118140960795 + 3719447 * 2 ^ 59
def prefixEnd_3719447 : Nat := 4983230072969 + 3 ^ 40 * 3719447 * 2
def baseEnd_3719447 : Nat := 1273242719949076253471387

theorem tailTrace_3719447 : CollatzResearch.WordTrace tailWord_3719447 prefixEnd_3719447 1273242719949076253471387 := by
  unfold tailWord_3719447
  simp only [CollatzResearch.WordTrace]
  refine ⟨135659376956086224819388595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90439584637390816546259063 135659376956086224819388595)
  ·
    refine ⟨203489065434129337229082893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135659376956086224819388595 203489065434129337229082893)
    ·
      refine ⟨76308399537798501460906085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 203489065434129337229082893 76308399537798501460906085)
      ·
        refine ⟨14307824913337219023919891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 76308399537798501460906085 14307824913337219023919891)
        ·
          refine ⟨21461737370005828535879837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14307824913337219023919891 21461737370005828535879837)
          ·
            refine ⟨8048151513752185700954939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21461737370005828535879837 8048151513752185700954939)
            ·
              refine ⟨12072227270628278551432409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8048151513752185700954939 12072227270628278551432409)
              ·
                refine ⟨9054170452971208913574307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12072227270628278551432409 9054170452971208913574307)
                ·
                  refine ⟨13581255679456813370361461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9054170452971208913574307 13581255679456813370361461)
                  ·
                    refine ⟨1273242719949076253471387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13581255679456813370361461 1273242719949076253471387)
                    ·
                      rfl

theorem cell22_3719447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 1, 2, 1, 5].length) (baseStart_3719447 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3719447 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3719447 prefixEnd_3719447 := by exact prefixLift 3719447
  have htrace : WordTrace (prefixWord ++ tailWord_3719447) baseStart_3719447 baseEnd_3719447 := by
    simpa [prefixWord, tailWord_3719447, baseEnd_3719447] using wordTrace_append hprefix tailTrace_3719447
  have hstable : (prefixWord ++ tailWord_3719447).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3719447).length < 2 ^ (prefixWord ++ tailWord_3719447).sum := by decide
  have hdescent : baseEnd_3719447 < baseStart_3719447 := by decide
  rcases family_descends (prefixWord ++ tailWord_3719447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3719460 : List Nat := [2, 3, 1, 3, 1, 12]
def baseStart_3719460 : Nat := 118140960795 + 3719460 * 2 ^ 59
def prefixEnd_3719460 : Nat := 4983230072969 + 3 ^ 40 * 3719460 * 2
def baseEnd_3719460 : Nat := 15719100865614179665387

theorem tailTrace_3719460 : CollatzResearch.WordTrace tailWord_3719460 prefixEnd_3719460 15719100865614179665387 := by
  unfold tailWord_3719460
  simp only [CollatzResearch.WordTrace]
  refine ⟨67829925552519564019805917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90439900736692752026407889 67829925552519564019805917)
  ·
    refine ⟨25436222082194836507427219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67829925552519564019805917 25436222082194836507427219)
    ·
      refine ⟨38154333123292254761140829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25436222082194836507427219 38154333123292254761140829)
      ·
        refine ⟨14307874921234595535427811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38154333123292254761140829 14307874921234595535427811)
        ·
          refine ⟨21461812381851893303141717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14307874921234595535427811 21461812381851893303141717)
          ·
            refine ⟨15719100865614179665387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 21461812381851893303141717 15719100865614179665387)
            ·
              rfl

theorem cell22_3719460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 12].length) (baseStart_3719460 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3719460 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3719460 prefixEnd_3719460 := by exact prefixLift 3719460
  have htrace : WordTrace (prefixWord ++ tailWord_3719460) baseStart_3719460 baseEnd_3719460 := by
    simpa [prefixWord, tailWord_3719460, baseEnd_3719460] using wordTrace_append hprefix tailTrace_3719460
  have hstable : (prefixWord ++ tailWord_3719460).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3719460).length < 2 ^ (prefixWord ++ tailWord_3719460).sum := by decide
  have hdescent : baseEnd_3719460 < baseStart_3719460 := by decide
  rcases family_descends (prefixWord ++ tailWord_3719460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3719466 : List Nat := [3, 1, 4, 2, 2, 1, 1, 4, 4]
def baseStart_3719466 : Nat := 118140960795 + 3719466 * 2 ^ 59
def prefixEnd_3719466 : Nat := 4983230072969 + 3 ^ 40 * 3719466 * 2
def baseEnd_3719466 : Nat := 424416408012455512415443

theorem tailTrace_3719466 : CollatzResearch.WordTrace tailWord_3719466 prefixEnd_3719466 424416408012455512415443 := by
  unfold tailWord_3719466
  simp only [CollatzResearch.WordTrace]
  refine ⟨33915017485754347766082563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90440046628678260709553501 33915017485754347766082563)
  ·
    refine ⟨50872526228631521649123845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33915017485754347766082563 50872526228631521649123845)
    ·
      refine ⟨9538598667868410309210721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50872526228631521649123845 9538598667868410309210721)
      ·
        refine ⟨7153949000901307731908041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9538598667868410309210721 7153949000901307731908041)
        ·
          refine ⟨5365461750675980798931031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7153949000901307731908041 5365461750675980798931031)
          ·
            refine ⟨8048192626013971198396547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5365461750675980798931031 8048192626013971198396547)
            ·
              refine ⟨12072288939020956797594821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8048192626013971198396547 12072288939020956797594821)
              ·
                refine ⟨2263554176066429399549029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12072288939020956797594821 2263554176066429399549029)
                ·
                  refine ⟨424416408012455512415443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2263554176066429399549029 424416408012455512415443)
                  ·
                    rfl

theorem cell22_3719466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 1, 4, 4].length) (baseStart_3719466 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3719466 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3719466 prefixEnd_3719466 := by exact prefixLift 3719466
  have htrace : WordTrace (prefixWord ++ tailWord_3719466) baseStart_3719466 baseEnd_3719466 := by
    simpa [prefixWord, tailWord_3719466, baseEnd_3719466] using wordTrace_append hprefix tailTrace_3719466
  have hstable : (prefixWord ++ tailWord_3719466).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3719466).length < 2 ^ (prefixWord ++ tailWord_3719466).sum := by decide
  have hdescent : baseEnd_3719466 < baseStart_3719466 := by decide
  rcases family_descends (prefixWord ++ tailWord_3719466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3719535 : List Nat := [1, 1, 2, 1, 3, 1, 2, 1, 2, 8]
def baseStart_3719535 : Nat := 118140960795 + 3719535 * 2 ^ 59
def prefixEnd_3719535 : Nat := 4983230072969 + 3 ^ 40 * 3719535 * 2
def baseEnd_3719535 : Nat := 1273272844147473357271117

theorem tailTrace_3719535 : CollatzResearch.WordTrace tailWord_3719535 prefixEnd_3719535 1273272844147473357271117 := by
  unfold tailWord_3719535
  simp only [CollatzResearch.WordTrace]
  refine ⟨135662586579767415848592059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90441724386511610565728039 135662586579767415848592059)
  ·
    refine ⟨203493879869651123772888089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135662586579767415848592059 203493879869651123772888089)
    ·
      refine ⟨152620409902238342829666067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 203493879869651123772888089 152620409902238342829666067)
      ·
        refine ⟨228930614853357514244499101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152620409902238342829666067 228930614853357514244499101)
        ·
          refine ⟨85848980570009067841687163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 228930614853357514244499101 85848980570009067841687163)
          ·
            refine ⟨128773470855013601762530745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85848980570009067841687163 128773470855013601762530745)
            ·
              refine ⟨96580103141260201321898059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 128773470855013601762530745 96580103141260201321898059)
              ·
                refine ⟨144870154711890301982847089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96580103141260201321898059 144870154711890301982847089)
                ·
                  refine ⟨108652616033917726487135317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 144870154711890301982847089 108652616033917726487135317)
                  ·
                    refine ⟨1273272844147473357271117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 108652616033917726487135317 1273272844147473357271117)
                    ·
                      rfl

theorem cell22_3719535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 1, 2, 8].length) (baseStart_3719535 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3719535 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3719535 prefixEnd_3719535 := by exact prefixLift 3719535
  have htrace : WordTrace (prefixWord ++ tailWord_3719535) baseStart_3719535 baseEnd_3719535 := by
    simpa [prefixWord, tailWord_3719535, baseEnd_3719535] using wordTrace_append hprefix tailTrace_3719535
  have hstable : (prefixWord ++ tailWord_3719535).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3719535).length < 2 ^ (prefixWord ++ tailWord_3719535).sum := by decide
  have hdescent : baseEnd_3719535 < baseStart_3719535 := by decide
  rcases family_descends (prefixWord ++ tailWord_3719535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3719584 : List Nat := [2, 1, 1, 4, 1, 5, 1, 1, 6]
def baseStart_3719584 : Nat := 118140960795 + 3719584 * 2 ^ 59
def prefixEnd_3719584 : Nat := 4983230072969 + 3 ^ 40 * 3719584 * 2
def baseEnd_3719584 : Nat := 424429872616284520931989

theorem tailTrace_3719584 : CollatzResearch.WordTrace tailWord_3719584 prefixEnd_3719584 424429872616284520931989 := by
  unfold tailWord_3719584
  simp only [CollatzResearch.WordTrace]
  refine ⟨67832186878294948608562903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90442915837726598144750537 67832186878294948608562903)
  ·
    refine ⟨101748280317442422912844355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67832186878294948608562903 101748280317442422912844355)
    ·
      refine ⟨152622420476163634369266533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101748280317442422912844355 152622420476163634369266533)
      ·
        refine ⟨28616703839280681444237475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 152622420476163634369266533 28616703839280681444237475)
        ·
          refine ⟨42925055758921022166356213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28616703839280681444237475 42925055758921022166356213)
          ·
            refine ⟨4024223977398845828095895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 42925055758921022166356213 4024223977398845828095895)
            ·
              refine ⟨6036335966098268742143843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4024223977398845828095895 6036335966098268742143843)
              ·
                refine ⟨9054503949147403113215765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6036335966098268742143843 9054503949147403113215765)
                ·
                  refine ⟨424429872616284520931989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9054503949147403113215765 424429872616284520931989)
                  ·
                    rfl

theorem cell22_3719584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 5, 1, 1, 6].length) (baseStart_3719584 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3719584 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3719584 prefixEnd_3719584 := by exact prefixLift 3719584
  have htrace : WordTrace (prefixWord ++ tailWord_3719584) baseStart_3719584 baseEnd_3719584 := by
    simpa [prefixWord, tailWord_3719584, baseEnd_3719584] using wordTrace_append hprefix tailTrace_3719584
  have hstable : (prefixWord ++ tailWord_3719584).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3719584).length < 2 ^ (prefixWord ++ tailWord_3719584).sum := by decide
  have hdescent : baseEnd_3719584 < baseStart_3719584 := by decide
  rcases family_descends (prefixWord ++ tailWord_3719584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3719614 : List Nat := [4, 2, 1, 1, 1, 1, 3, 3, 2, 4]
def baseStart_3719614 : Nat := 118140960795 + 3719614 * 2 ^ 59
def prefixEnd_3719614 : Nat := 4983230072969 + 3 ^ 40 * 3719614 * 2
def baseEnd_3719614 : Nat := 1273299887461943484545875

theorem tailTrace_3719614 : CollatzResearch.WordTrace tailWord_3719614 prefixEnd_3719614 1273299887461943484545875 := by
  unfold tailWord_3719614
  simp only [CollatzResearch.WordTrace]
  refine ⟨16958183493310151542589737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 90443645297654141560478597 16958183493310151542589737)
  ·
    refine ⟨12718637619982613656942303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16958183493310151542589737 12718637619982613656942303)
    ·
      refine ⟨19077956429973920485413455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12718637619982613656942303 19077956429973920485413455)
      ·
        refine ⟨28616934644960880728120183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19077956429973920485413455 28616934644960880728120183)
        ·
          refine ⟨42925401967441321092180275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28616934644960880728120183 42925401967441321092180275)
          ·
            refine ⟨64388102951161981638270413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42925401967441321092180275 64388102951161981638270413)
            ·
              refine ⟨24145538606685743114351405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64388102951161981638270413 24145538606685743114351405)
              ·
                refine ⟨9054576977507153667881777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24145538606685743114351405 9054576977507153667881777)
                ·
                  refine ⟨6790932733130365250911333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9054576977507153667881777 6790932733130365250911333)
                  ·
                    refine ⟨1273299887461943484545875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6790932733130365250911333 1273299887461943484545875)
                    ·
                      rfl

theorem cell22_3719614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 3, 3, 2, 4].length) (baseStart_3719614 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3719614 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3719614 prefixEnd_3719614 := by exact prefixLift 3719614
  have htrace : WordTrace (prefixWord ++ tailWord_3719614) baseStart_3719614 baseEnd_3719614 := by
    simpa [prefixWord, tailWord_3719614, baseEnd_3719614] using wordTrace_append hprefix tailTrace_3719614
  have hstable : (prefixWord ++ tailWord_3719614).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3719614).length < 2 ^ (prefixWord ++ tailWord_3719614).sum := by decide
  have hdescent : baseEnd_3719614 < baseStart_3719614 := by decide
  rcases family_descends (prefixWord ++ tailWord_3719614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3719642 : List Nat := [3, 1, 1, 2, 3, 1, 1, 1, 1, 8]
def baseStart_3719642 : Nat := 118140960795 + 3719642 * 2 ^ 59
def prefixEnd_3719642 : Nat := 4983230072969 + 3 ^ 40 * 3719642 * 2
def baseEnd_3719642 : Nat := 1273309472434160744845789

theorem tailTrace_3719642 : CollatzResearch.WordTrace tailWord_3719642 prefixEnd_3719642 1273309472434160744845789 := by
  unfold tailWord_3719642
  simp only [CollatzResearch.WordTrace]
  refine ⟨33916622297594943280684295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90444326126919848748491453 33916622297594943280684295)
  ·
    refine ⟨50874933446392414921026443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33916622297594943280684295 50874933446392414921026443)
    ·
      refine ⟨76312400169588622381539665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50874933446392414921026443 76312400169588622381539665)
      ·
        refine ⟨57234300127191466786154749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76312400169588622381539665 57234300127191466786154749)
        ·
          refine ⟨21462862547696800044808031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57234300127191466786154749 21462862547696800044808031)
          ·
            refine ⟨32194293821545200067212047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21462862547696800044808031 32194293821545200067212047)
            ·
              refine ⟨48291440732317800100818071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32194293821545200067212047 48291440732317800100818071)
              ·
                refine ⟨72437161098476700151227107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48291440732317800100818071 72437161098476700151227107)
                ·
                  refine ⟨108655741647715050226840661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 72437161098476700151227107 108655741647715050226840661)
                  ·
                    refine ⟨1273309472434160744845789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 108655741647715050226840661 1273309472434160744845789)
                    ·
                      rfl

theorem cell22_3719642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 1, 1, 8].length) (baseStart_3719642 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3719642 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3719642 prefixEnd_3719642 := by exact prefixLift 3719642
  have htrace : WordTrace (prefixWord ++ tailWord_3719642) baseStart_3719642 baseEnd_3719642 := by
    simpa [prefixWord, tailWord_3719642, baseEnd_3719642] using wordTrace_append hprefix tailTrace_3719642
  have hstable : (prefixWord ++ tailWord_3719642).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3719642).length < 2 ^ (prefixWord ++ tailWord_3719642).sum := by decide
  have hdescent : baseEnd_3719642 < baseStart_3719642 := by decide
  rcases family_descends (prefixWord ++ tailWord_3719642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3719661 : List Nat := [1, 5, 1, 3, 1, 1, 1, 1, 5, 3]
def baseStart_3719661 : Nat := 118140960795 + 3719661 * 2 ^ 59
def prefixEnd_3719661 : Nat := 4983230072969 + 3 ^ 40 * 3719661 * 2
def baseEnd_3719661 : Nat := 1273315976522451028620731

theorem tailTrace_3719661 : CollatzResearch.WordTrace tailWord_3719661 prefixEnd_3719661 1273315976522451028620731 := by
  unfold tailWord_3719661
  simp only [CollatzResearch.WordTrace]
  refine ⟨135667182177310939367678837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90444788118207292911785891 135667182177310939367678837)
  ·
    refine ⟨12718798329122900565719891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 135667182177310939367678837 12718798329122900565719891)
    ·
      refine ⟨19078197493684350848579837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12718798329122900565719891 19078197493684350848579837)
      ·
        refine ⟨7154324060131631568217439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19078197493684350848579837 7154324060131631568217439)
        ·
          refine ⟨10731486090197447352326159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7154324060131631568217439 10731486090197447352326159)
          ·
            refine ⟨16097229135296171028489239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10731486090197447352326159 16097229135296171028489239)
            ·
              refine ⟨24145843702944256542733859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16097229135296171028489239 24145843702944256542733859)
              ·
                refine ⟨36218765554416384814100789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24145843702944256542733859 36218765554416384814100789)
                ·
                  refine ⟨3395509270726536076321949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 36218765554416384814100789 3395509270726536076321949)
                  ·
                    refine ⟨1273315976522451028620731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3395509270726536076321949 1273315976522451028620731)
                    ·
                      rfl

theorem cell22_3719661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 1, 1, 5, 3].length) (baseStart_3719661 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3719661 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3719661 prefixEnd_3719661 := by exact prefixLift 3719661
  have htrace : WordTrace (prefixWord ++ tailWord_3719661) baseStart_3719661 baseEnd_3719661 := by
    simpa [prefixWord, tailWord_3719661, baseEnd_3719661] using wordTrace_append hprefix tailTrace_3719661
  have hstable : (prefixWord ++ tailWord_3719661).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3719661).length < 2 ^ (prefixWord ++ tailWord_3719661).sum := by decide
  have hdescent : baseEnd_3719661 < baseStart_3719661 := by decide
  rcases family_descends (prefixWord ++ tailWord_3719661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3719672 : List Nat := [2, 1, 2, 1, 1, 4, 1, 2, 1, 7]
def baseStart_3719672 : Nat := 118140960795 + 3719672 * 2 ^ 59
def prefixEnd_3719672 : Nat := 4983230072969 + 3 ^ 40 * 3719672 * 2
def baseEnd_3719672 : Nat := 1273319742047250666595697

theorem tailTrace_3719672 : CollatzResearch.WordTrace tailWord_3719672 prefixEnd_3719672 1273319742047250666595697 := by
  unfold tailWord_3719672
  simp only [CollatzResearch.WordTrace]
  refine ⟨67833791690135544123164635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90445055586847392164219513 67833791690135544123164635)
  ·
    refine ⟨101750687535203316184746953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67833791690135544123164635 101750687535203316184746953)
    ·
      refine ⟨76313015651402487138560215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101750687535203316184746953 76313015651402487138560215)
      ·
        refine ⟨114469523477103730707840323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76313015651402487138560215 114469523477103730707840323)
        ·
          refine ⟨171704285215655596061760485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114469523477103730707840323 171704285215655596061760485)
          ·
            refine ⟨32194553477935424261580091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 171704285215655596061760485 32194553477935424261580091)
            ·
              refine ⟨48291830216903136392370137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32194553477935424261580091 48291830216903136392370137)
              ·
                refine ⟨36218872662677352294277603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48291830216903136392370137 36218872662677352294277603)
                ·
                  refine ⟨54328308994016028441416405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36218872662677352294277603 54328308994016028441416405)
                  ·
                    refine ⟨1273319742047250666595697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 54328308994016028441416405 1273319742047250666595697)
                    ·
                      rfl

theorem cell22_3719672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 2, 1, 7].length) (baseStart_3719672 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3719672 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3719672 prefixEnd_3719672 := by exact prefixLift 3719672
  have htrace : WordTrace (prefixWord ++ tailWord_3719672) baseStart_3719672 baseEnd_3719672 := by
    simpa [prefixWord, tailWord_3719672, baseEnd_3719672] using wordTrace_append hprefix tailTrace_3719672
  have hstable : (prefixWord ++ tailWord_3719672).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3719672).length < 2 ^ (prefixWord ++ tailWord_3719672).sum := by decide
  have hdescent : baseEnd_3719672 < baseStart_3719672 := by decide
  rcases family_descends (prefixWord ++ tailWord_3719672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3719691 : List Nat := [1, 1, 1, 1, 7, 3, 1, 2, 5]
def baseStart_3719691 : Nat := 118140960795 + 3719691 * 2 ^ 59
def prefixEnd_3719691 : Nat := 4983230072969 + 3 ^ 40 * 3719691 * 2
def baseEnd_3719691 : Nat := 424442082045180316790213

theorem tailTrace_3719691 : CollatzResearch.WordTrace tailWord_3719691 prefixEnd_3719691 424442082045180316790213 := by
  unfold tailWord_3719691
  simp only [CollatzResearch.WordTrace]
  refine ⟨135668276367202254491270927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90445517578134836327513951 135668276367202254491270927)
  ·
    refine ⟨203502414550803381736906391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135668276367202254491270927 203502414550803381736906391)
    ·
      refine ⟨305253621826205072605359587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203502414550803381736906391 305253621826205072605359587)
      ·
        refine ⟨457880432739307608908039381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 305253621826205072605359587 457880432739307608908039381)
        ·
          refine ⟨10731572642327522083782173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 457880432739307608908039381 10731572642327522083782173)
          ·
            refine ⟨4024339740872820781418315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10731572642327522083782173 4024339740872820781418315)
            ·
              refine ⟨6036509611309231172127473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4024339740872820781418315 6036509611309231172127473)
              ·
                refine ⟨4527382208481923379095605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6036509611309231172127473 4527382208481923379095605)
                ·
                  refine ⟨424442082045180316790213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4527382208481923379095605 424442082045180316790213)
                  ·
                    rfl

theorem cell22_3719691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 3, 1, 2, 5].length) (baseStart_3719691 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3719691 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3719691 prefixEnd_3719691 := by exact prefixLift 3719691
  have htrace : WordTrace (prefixWord ++ tailWord_3719691) baseStart_3719691 baseEnd_3719691 := by
    simpa [prefixWord, tailWord_3719691, baseEnd_3719691] using wordTrace_append hprefix tailTrace_3719691
  have hstable : (prefixWord ++ tailWord_3719691).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3719691).length < 2 ^ (prefixWord ++ tailWord_3719691).sum := by decide
  have hdescent : baseEnd_3719691 < baseStart_3719691 := by decide
  rcases family_descends (prefixWord ++ tailWord_3719691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3719749 : List Nat := [1, 3, 1, 1, 1, 5, 1, 1, 4, 4]
def baseStart_3719749 : Nat := 118140960795 + 3719749 * 2 ^ 59
def prefixEnd_3719749 : Nat := 4983230072969 + 3 ^ 40 * 3719749 * 2
def baseEnd_3719749 : Nat := 1273346100720848132420461

theorem tailTrace_3719749 : CollatzResearch.WordTrace tailWord_3719749 prefixEnd_3719749 1273346100720848132420461 := by
  unfold tailWord_3719749
  simp only [CollatzResearch.WordTrace]
  refine ⟨135670391800992130396882301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90446927867328086931254867 135670391800992130396882301)
  ·
    refine ⟨50876396925372048898830863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135670391800992130396882301 50876396925372048898830863)
    ·
      refine ⟨76314595388058073348246295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50876396925372048898830863 76314595388058073348246295)
      ·
        refine ⟨114471893082087110022369443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76314595388058073348246295 114471893082087110022369443)
        ·
          refine ⟨171707839623130665033554165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114471893082087110022369443 171707839623130665033554165)
          ·
            refine ⟨16097609964668499846895703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 171707839623130665033554165 16097609964668499846895703)
            ·
              refine ⟨24146414947002749770343555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16097609964668499846895703 24146414947002749770343555)
              ·
                refine ⟨36219622420504124655515333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24146414947002749770343555 36219622420504124655515333)
                ·
                  refine ⟨6791179203844523372909125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36219622420504124655515333 6791179203844523372909125)
                  ·
                    refine ⟨1273346100720848132420461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6791179203844523372909125 1273346100720848132420461)
                    ·
                      rfl

theorem cell22_3719749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 1, 1, 4, 4].length) (baseStart_3719749 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3719749 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3719749 prefixEnd_3719749 := by exact prefixLift 3719749
  have htrace : WordTrace (prefixWord ++ tailWord_3719749) baseStart_3719749 baseEnd_3719749 := by
    simpa [prefixWord, tailWord_3719749, baseEnd_3719749] using wordTrace_append hprefix tailTrace_3719749
  have hstable : (prefixWord ++ tailWord_3719749).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3719749).length < 2 ^ (prefixWord ++ tailWord_3719749).sum := by decide
  have hdescent : baseEnd_3719749 < baseStart_3719749 := by decide
  rcases family_descends (prefixWord ++ tailWord_3719749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3719751 : List Nat := [1, 1, 4, 1, 4, 1, 2, 1, 4, 3]
def baseStart_3719751 : Nat := 118140960795 + 3719751 * 2 ^ 59
def prefixEnd_3719751 : Nat := 4983230072969 + 3 ^ 40 * 3719751 * 2
def baseEnd_3719751 : Nat := 1273346785361720793870455

theorem tailTrace_3719751 : CollatzResearch.WordTrace tailWord_3719751 prefixEnd_3719751 1273346785361720793870455 := by
  unfold tailWord_3719751
  simp only [CollatzResearch.WordTrace]
  refine ⟨135670464746984884738455107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90446976497989923158970071 135670464746984884738455107)
  ·
    refine ⟨203505697120477327107682661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135670464746984884738455107 203505697120477327107682661)
    ·
      refine ⟨38157318210089498832690499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 203505697120477327107682661 38157318210089498832690499)
      ·
        refine ⟨57235977315134248249035749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38157318210089498832690499 57235977315134248249035749)
        ·
          refine ⟨10731745746587671546694203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 57235977315134248249035749 10731745746587671546694203)
          ·
            refine ⟨16097618619881507320041305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10731745746587671546694203 16097618619881507320041305)
            ·
              refine ⟨12073213964911130490030979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16097618619881507320041305 12073213964911130490030979)
              ·
                refine ⟨18109820947366695735046469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12073213964911130490030979 18109820947366695735046469)
                ·
                  refine ⟨3395591427631255450321213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18109820947366695735046469 3395591427631255450321213)
                  ·
                    refine ⟨1273346785361720793870455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3395591427631255450321213 1273346785361720793870455)
                    ·
                      rfl

theorem cell22_3719751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 2, 1, 4, 3].length) (baseStart_3719751 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3719751 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3719751 prefixEnd_3719751 := by exact prefixLift 3719751
  have htrace : WordTrace (prefixWord ++ tailWord_3719751) baseStart_3719751 baseEnd_3719751 := by
    simpa [prefixWord, tailWord_3719751, baseEnd_3719751] using wordTrace_append hprefix tailTrace_3719751
  have hstable : (prefixWord ++ tailWord_3719751).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3719751).length < 2 ^ (prefixWord ++ tailWord_3719751).sum := by decide
  have hdescent : baseEnd_3719751 < baseStart_3719751 := by decide
  rcases family_descends (prefixWord ++ tailWord_3719751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3719764 : List Nat := [2, 4, 1, 1, 1, 3, 1, 9]
def baseStart_3719764 : Nat := 118140960795 + 3719764 * 2 ^ 59
def prefixEnd_3719764 : Nat := 4983230072969 + 3 ^ 40 * 3719764 * 2
def baseEnd_3719764 : Nat := 141483470614154788143935

theorem tailTrace_3719764 : CollatzResearch.WordTrace tailWord_3719764 prefixEnd_3719764 141483470614154788143935 := by
  unfold tailWord_3719764
  simp only [CollatzResearch.WordTrace]
  refine ⟨67835469447968893979339173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90447292597291858639118897 67835469447968893979339173)
  ·
    refine ⟨12719150521494167621126095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 67835469447968893979339173 12719150521494167621126095)
    ·
      refine ⟨19078725782241251431689143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12719150521494167621126095 19078725782241251431689143)
      ·
        refine ⟨28618088673361877147533715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19078725782241251431689143 28618088673361877147533715)
        ·
          refine ⟨42927133010042815721300573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28618088673361877147533715 42927133010042815721300573)
          ·
            refine ⟨16097674878766055895487715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42927133010042815721300573 16097674878766055895487715)
            ·
              refine ⟨24146512318149083843231573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16097674878766055895487715 24146512318149083843231573)
              ·
                refine ⟨141483470614154788143935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 24146512318149083843231573 141483470614154788143935)
                ·
                  rfl

theorem cell22_3719764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 1, 9].length) (baseStart_3719764 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3719764 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3719764 prefixEnd_3719764 := by exact prefixLift 3719764
  have htrace : WordTrace (prefixWord ++ tailWord_3719764) baseStart_3719764 baseEnd_3719764 := by
    simpa [prefixWord, tailWord_3719764, baseEnd_3719764] using wordTrace_append hprefix tailTrace_3719764
  have hstable : (prefixWord ++ tailWord_3719764).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3719764).length < 2 ^ (prefixWord ++ tailWord_3719764).sum := by decide
  have hdescent : baseEnd_3719764 < baseStart_3719764 := by decide
  rcases family_descends (prefixWord ++ tailWord_3719764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3719768 : List Nat := [2, 1, 2, 2, 1, 2, 6, 1, 2, 3]
def baseStart_3719768 : Nat := 118140960795 + 3719768 * 2 ^ 59
def prefixEnd_3719768 : Nat := 4983230072969 + 3 ^ 40 * 3719768 * 2
def baseEnd_3719768 : Nat := 1273352604809138416195403

theorem tailTrace_3719768 : CollatzResearch.WordTrace tailWord_3719768 prefixEnd_3719768 1273352604809138416195403 := by
  unfold tailWord_3719768
  simp only [CollatzResearch.WordTrace]
  refine ⟨67835542393961648320911979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90447389858615531094549305 67835542393961648320911979)
  ·
    refine ⟨101753313590942472481367969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67835542393961648320911979 101753313590942472481367969)
    ·
      refine ⟨76314985193206854361025977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101753313590942472481367969 76314985193206854361025977)
      ·
        refine ⟨57236238894905140770769483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76314985193206854361025977 57236238894905140770769483)
        ·
          refine ⟨85854358342357711156154225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57236238894905140770769483 85854358342357711156154225)
          ·
            refine ⟨64390768756768283367115669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85854358342357711156154225 64390768756768283367115669)
            ·
              refine ⟨3018317285473513282833547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 64390768756768283367115669 3018317285473513282833547)
              ·
                refine ⟨4527475928210269924250321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3018317285473513282833547 4527475928210269924250321)
                ·
                  refine ⟨3395606946157702443187741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4527475928210269924250321 3395606946157702443187741)
                  ·
                    refine ⟨1273352604809138416195403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3395606946157702443187741 1273352604809138416195403)
                    ·
                      rfl

theorem cell22_3719768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 6, 1, 2, 3].length) (baseStart_3719768 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3719768 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3719768 prefixEnd_3719768 := by exact prefixLift 3719768
  have htrace : WordTrace (prefixWord ++ tailWord_3719768) baseStart_3719768 baseEnd_3719768 := by
    simpa [prefixWord, tailWord_3719768, baseEnd_3719768] using wordTrace_append hprefix tailTrace_3719768
  have hstable : (prefixWord ++ tailWord_3719768).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3719768).length < 2 ^ (prefixWord ++ tailWord_3719768).sum := by decide
  have hdescent : baseEnd_3719768 < baseStart_3719768 := by decide
  rcases family_descends (prefixWord ++ tailWord_3719768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3719871 : List Nat := [1, 1, 2, 2, 2, 5, 2, 1, 6]
def baseStart_3719871 : Nat := 118140960795 + 3719871 * 2 ^ 59
def prefixEnd_3719871 : Nat := 4983230072969 + 3 ^ 40 * 3719871 * 2
def baseEnd_3719871 : Nat := 424462621271360160290029

theorem tailTrace_3719871 : CollatzResearch.WordTrace tailWord_3719871 prefixEnd_3719871 424462621271360160290029 := by
  unfold tailWord_3719871
  simp only [CollatzResearch.WordTrace]
  refine ⟨135674841506550145232823467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90449894337700096821882311 135674841506550145232823467)
  ·
    refine ⟨203512262259825217849235201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135674841506550145232823467 203512262259825217849235201)
    ·
      refine ⟨152634196694868913386926401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 203512262259825217849235201 152634196694868913386926401)
      ·
        refine ⟨114475647521151685040194801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152634196694868913386926401 114475647521151685040194801)
        ·
          refine ⟨85856735640863763780146101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114475647521151685040194801 85856735640863763780146101)
          ·
            refine ⟨8049068966330977854388697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 85856735640863763780146101 8049068966330977854388697)
            ·
              refine ⟨6036801724748233390791523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8049068966330977854388697 6036801724748233390791523)
              ·
                refine ⟨9055202587122350086187285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6036801724748233390791523 9055202587122350086187285)
                ·
                  refine ⟨424462621271360160290029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9055202587122350086187285 424462621271360160290029)
                  ·
                    rfl

theorem cell22_3719871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 2, 1, 6].length) (baseStart_3719871 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3719871 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3719871 prefixEnd_3719871 := by exact prefixLift 3719871
  have htrace : WordTrace (prefixWord ++ tailWord_3719871) baseStart_3719871 baseEnd_3719871 := by
    simpa [prefixWord, tailWord_3719871, baseEnd_3719871] using wordTrace_append hprefix tailTrace_3719871
  have hstable : (prefixWord ++ tailWord_3719871).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3719871).length < 2 ^ (prefixWord ++ tailWord_3719871).sum := by decide
  have hdescent : baseEnd_3719871 < baseStart_3719871 := by decide
  rcases family_descends (prefixWord ++ tailWord_3719871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3719890 : List Nat := [3, 2, 2, 2, 3, 1, 2, 2, 1, 4]
def baseStart_3719890 : Nat := 118140960795 + 3719890 * 2 ^ 59
def prefixEnd_3719890 : Nat := 4983230072969 + 3 ^ 40 * 3719890 * 2
def baseEnd_3719890 : Nat := 1273394367902370764645029

theorem tailTrace_3719890 : CollatzResearch.WordTrace tailWord_3719890 prefixEnd_3719890 1273394367902370764645029 := by
  unfold tailWord_3719890
  simp only [CollatzResearch.WordTrace]
  refine ⟨33918883623370327869441281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90450356328987540985176749 33918883623370327869441281)
  ·
    refine ⟨25439162717527745902080961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33918883623370327869441281 25439162717527745902080961)
    ·
      refine ⟨19079372038145809426560721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25439162717527745902080961 19079372038145809426560721)
      ·
        refine ⟨14309529028609357069920541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19079372038145809426560721 14309529028609357069920541)
        ·
          refine ⟨5366073385728508901220203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14309529028609357069920541 5366073385728508901220203)
          ·
            refine ⟨8049110078592763351830305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5366073385728508901220203 8049110078592763351830305)
            ·
              refine ⟨6036832558944572513872729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8049110078592763351830305 6036832558944572513872729)
              ·
                refine ⟨4527624419208429385404547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6036832558944572513872729 4527624419208429385404547)
                ·
                  refine ⟨6791436628812644078106821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4527624419208429385404547 6791436628812644078106821)
                  ·
                    refine ⟨1273394367902370764645029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6791436628812644078106821 1273394367902370764645029)
                    ·
                      rfl

theorem cell22_3719890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 2, 2, 1, 4].length) (baseStart_3719890 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3719890 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3719890 prefixEnd_3719890 := by exact prefixLift 3719890
  have htrace : WordTrace (prefixWord ++ tailWord_3719890) baseStart_3719890 baseEnd_3719890 := by
    simpa [prefixWord, tailWord_3719890, baseEnd_3719890] using wordTrace_append hprefix tailTrace_3719890
  have hstable : (prefixWord ++ tailWord_3719890).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3719890).length < 2 ^ (prefixWord ++ tailWord_3719890).sum := by decide
  have hdescent : baseEnd_3719890 < baseStart_3719890 := by decide
  rcases family_descends (prefixWord ++ tailWord_3719890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3719905 : List Nat := [1, 2, 3, 1, 4, 3, 1, 3, 4]
def baseStart_3719905 : Nat := 118140960795 + 3719905 * 2 ^ 59
def prefixEnd_3719905 : Nat := 4983230072969 + 3 ^ 40 * 3719905 * 2
def baseEnd_3719905 : Nat := 424466500902971908506661

theorem tailTrace_3719905 : CollatzResearch.WordTrace tailWord_3719905 prefixEnd_3719905 424466500902971908506661 := by
  unfold tailWord_3719905
  simp only [CollatzResearch.WordTrace]
  refine ⟨135676081588426969039561169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90450721058951312693040779 135676081588426969039561169)
  ·
    refine ⟨101757061191320226779670877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135676081588426969039561169 101757061191320226779670877)
    ·
      refine ⟨38158897946745085042376579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101757061191320226779670877 38158897946745085042376579)
      ·
        refine ⟨57238346920117627563564869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38158897946745085042376579 57238346920117627563564869)
        ·
          refine ⟨10732190047522055168168413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 57238346920117627563564869 10732190047522055168168413)
          ·
            refine ⟨4024571267820770688063155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10732190047522055168168413 4024571267820770688063155)
            ·
              refine ⟨6036856901731156032094733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4024571267820770688063155 6036856901731156032094733)
              ·
                refine ⟨2263821338149183512035525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6036856901731156032094733 2263821338149183512035525)
                ·
                  refine ⟨424466500902971908506661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2263821338149183512035525 424466500902971908506661)
                  ·
                    rfl

theorem cell22_3719905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 3, 1, 3, 4].length) (baseStart_3719905 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3719905 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3719905 prefixEnd_3719905 := by exact prefixLift 3719905
  have htrace : WordTrace (prefixWord ++ tailWord_3719905) baseStart_3719905 baseEnd_3719905 := by
    simpa [prefixWord, tailWord_3719905, baseEnd_3719905] using wordTrace_append hprefix tailTrace_3719905
  have hstable : (prefixWord ++ tailWord_3719905).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3719905).length < 2 ^ (prefixWord ++ tailWord_3719905).sum := by decide
  have hdescent : baseEnd_3719905 < baseStart_3719905 := by decide
  rcases family_descends (prefixWord ++ tailWord_3719905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3719918 : List Nat := [4, 1, 2, 1, 1, 4, 1, 2, 2, 4]
def baseStart_3719918 : Nat := 118140960795 + 3719918 * 2 ^ 59
def prefixEnd_3719918 : Nat := 4983230072969 + 3 ^ 40 * 3719918 * 2
def baseEnd_3719918 : Nat := 1273403952874588024944943

theorem tailTrace_3719918 : CollatzResearch.WordTrace tailWord_3719918 prefixEnd_3719918 1273403952874588024944943 := by
  unfold tailWord_3719918
  simp only [CollatzResearch.WordTrace]
  refine ⟨16959569467172484032473051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 90451037158253248173189605 16959569467172484032473051)
  ·
    refine ⟨25439354200758726048709577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16959569467172484032473051 25439354200758726048709577)
    ·
      refine ⟨19079515650569044536532183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25439354200758726048709577 19079515650569044536532183)
      ·
        refine ⟨28619273475853566804798275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19079515650569044536532183 28619273475853566804798275)
        ·
          refine ⟨42928910213780350207197413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28619273475853566804798275 42928910213780350207197413)
          ·
            refine ⟨8049170665083815663849515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42928910213780350207197413 8049170665083815663849515)
            ·
              refine ⟨12073755997625723495774273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8049170665083815663849515 12073755997625723495774273)
              ·
                refine ⟨9055316998219292621830705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12073755997625723495774273 9055316998219292621830705)
                ·
                  refine ⟨6791487748664469466373029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9055316998219292621830705 6791487748664469466373029)
                  ·
                    refine ⟨1273403952874588024944943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6791487748664469466373029 1273403952874588024944943)
                    ·
                      rfl

theorem cell22_3719918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 1, 2, 2, 4].length) (baseStart_3719918 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3719918 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3719918 prefixEnd_3719918 := by exact prefixLift 3719918
  have htrace : WordTrace (prefixWord ++ tailWord_3719918) baseStart_3719918 baseEnd_3719918 := by
    simpa [prefixWord, tailWord_3719918, baseEnd_3719918] using wordTrace_append hprefix tailTrace_3719918
  have hstable : (prefixWord ++ tailWord_3719918).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3719918).length < 2 ^ (prefixWord ++ tailWord_3719918).sum := by decide
  have hdescent : baseEnd_3719918 < baseStart_3719918 := by decide
  rcases family_descends (prefixWord ++ tailWord_3719918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3719991 : List Nat := [1, 1, 3, 1, 2, 1, 3, 1, 5, 4]
def baseStart_3719991 : Nat := 118140960795 + 3719991 * 2 ^ 59
def prefixEnd_3719991 : Nat := 4983230072969 + 3 ^ 40 * 3719991 * 2
def baseEnd_3719991 : Nat := 1273428942266440167869719

theorem tailTrace_3719991 : CollatzResearch.WordTrace tailWord_3719991 prefixEnd_3719991 1273428942266440167869719 := by
  unfold tailWord_3719991
  simp only [CollatzResearch.WordTrace]
  refine ⟨135679218266115405727191827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90452812177410270484794551 135679218266115405727191827)
  ·
    refine ⟨203518827399173108590787741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135679218266115405727191827 203518827399173108590787741)
    ·
      refine ⟨76319560274689915721545403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 203518827399173108590787741 76319560274689915721545403)
      ·
        refine ⟨114479340412034873582318105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76319560274689915721545403 114479340412034873582318105)
        ·
          refine ⟨85859505309026155186738579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114479340412034873582318105 85859505309026155186738579)
          ·
            refine ⟨128789257963539232780107869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85859505309026155186738579 128789257963539232780107869)
            ·
              refine ⟨48295971736327212292540451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 128789257963539232780107869 48295971736327212292540451)
              ·
                refine ⟨72443957604490818438810677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48295971736327212292540451 72443957604490818438810677)
                ·
                  refine ⟨6791621025421014228638501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 72443957604490818438810677 6791621025421014228638501)
                  ·
                    refine ⟨1273428942266440167869719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6791621025421014228638501 1273428942266440167869719)
                    ·
                      rfl

theorem cell22_3719991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 1, 5, 4].length) (baseStart_3719991 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3719991 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3719991 prefixEnd_3719991 := by exact prefixLift 3719991
  have htrace : WordTrace (prefixWord ++ tailWord_3719991) baseStart_3719991 baseEnd_3719991 := by
    simpa [prefixWord, tailWord_3719991, baseEnd_3719991] using wordTrace_append hprefix tailTrace_3719991
  have hstable : (prefixWord ++ tailWord_3719991).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3719991).length < 2 ^ (prefixWord ++ tailWord_3719991).sum := by decide
  have hdescent : baseEnd_3719991 < baseStart_3719991 := by decide
  rcases family_descends (prefixWord ++ tailWord_3719991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3720008 : List Nat := [2, 1, 3, 1, 1, 3, 2, 4, 1, 4]
def baseStart_3720008 : Nat := 118140960795 + 3720008 * 2 ^ 59
def prefixEnd_3720008 : Nat := 4983230072969 + 3 ^ 40 * 3720008 * 2
def baseEnd_3720008 : Nat := 1273434761713857790194667

theorem tailTrace_3720008 : CollatzResearch.WordTrace tailWord_3720008 prefixEnd_3720008 1273434761713857790194667 := by
  unfold tailWord_3720008
  simp only [CollatzResearch.WordTrace]
  refine ⟨67839919153526908815280339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90453225538035878420373785 67839919153526908815280339)
  ·
    refine ⟨101759878730290363222920509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67839919153526908815280339 101759878730290363222920509)
    ·
      refine ⟨38159954523858886208595191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101759878730290363222920509 38159954523858886208595191)
      ·
        refine ⟨57239931785788329312892787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38159954523858886208595191 57239931785788329312892787)
        ·
          refine ⟨85859897678682493969339181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57239931785788329312892787 85859897678682493969339181)
          ·
            refine ⟨32197461629505935238502193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 85859897678682493969339181 32197461629505935238502193)
            ·
              refine ⟨24148096222129451428876645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32197461629505935238502193 24148096222129451428876645)
              ·
                refine ⟨4527768041649272142914371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24148096222129451428876645 4527768041649272142914371)
                ·
                  refine ⟨6791652062473908214371557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4527768041649272142914371 6791652062473908214371557)
                  ·
                    refine ⟨1273434761713857790194667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6791652062473908214371557 1273434761713857790194667)
                    ·
                      rfl

theorem cell22_3720008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 2, 4, 1, 4].length) (baseStart_3720008 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3720008 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3720008 prefixEnd_3720008 := by exact prefixLift 3720008
  have htrace : WordTrace (prefixWord ++ tailWord_3720008) baseStart_3720008 baseEnd_3720008 := by
    simpa [prefixWord, tailWord_3720008, baseEnd_3720008] using wordTrace_append hprefix tailTrace_3720008
  have hstable : (prefixWord ++ tailWord_3720008).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3720008).length < 2 ^ (prefixWord ++ tailWord_3720008).sum := by decide
  have hdescent : baseEnd_3720008 < baseStart_3720008 := by decide
  rcases family_descends (prefixWord ++ tailWord_3720008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3720025 : List Nat := [1, 2, 1, 2, 2, 4, 4, 1, 1, 4]
def baseStart_3720025 : Nat := 118140960795 + 3720025 * 2 ^ 59
def prefixEnd_3720025 : Nat := 4983230072969 + 3 ^ 40 * 3720025 * 2
def baseEnd_3720025 : Nat := 1273440581161275412519615

theorem tailTrace_3720025 : CollatzResearch.WordTrace tailWord_3720025 prefixEnd_3720025 1273440581161275412519615 := by
  unfold tailWord_3720025
  simp only [CollatzResearch.WordTrace]
  refine ⟨135680458347992229533929529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90453638898661486355953019 135680458347992229533929529)
  ·
    refine ⟨101760343760994172150447147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135680458347992229533929529 101760343760994172150447147)
    ·
      refine ⟨152640515641491258225670721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101760343760994172150447147 152640515641491258225670721)
      ·
        refine ⟨114480386731118443669253041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152640515641491258225670721 114480386731118443669253041)
        ·
          refine ⟨85860290048338832751939781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114480386731118443669253041 85860290048338832751939781)
          ·
            refine ⟨16098804384063531140988709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 85860290048338832751939781 16098804384063531140988709)
            ·
              refine ⟨3018525822011912088935383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16098804384063531140988709 3018525822011912088935383)
              ·
                refine ⟨4527788733017868133403075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3018525822011912088935383 4527788733017868133403075)
                ·
                  refine ⟨6791683099526802200104613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4527788733017868133403075 6791683099526802200104613)
                  ·
                    refine ⟨1273440581161275412519615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6791683099526802200104613 1273440581161275412519615)
                    ·
                      rfl

theorem cell22_3720025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 4, 1, 1, 4].length) (baseStart_3720025 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3720025 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3720025 prefixEnd_3720025 := by exact prefixLift 3720025
  have htrace : WordTrace (prefixWord ++ tailWord_3720025) baseStart_3720025 baseEnd_3720025 := by
    simpa [prefixWord, tailWord_3720025, baseEnd_3720025] using wordTrace_append hprefix tailTrace_3720025
  have hstable : (prefixWord ++ tailWord_3720025).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3720025).length < 2 ^ (prefixWord ++ tailWord_3720025).sum := by decide
  have hdescent : baseEnd_3720025 < baseStart_3720025 := by decide
  rcases family_descends (prefixWord ++ tailWord_3720025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3720040 : List Nat := [2, 1, 4, 2, 1, 2, 2, 4, 4]
def baseStart_3720040 : Nat := 118140960795 + 3720040 * 2 ^ 59
def prefixEnd_3720040 : Nat := 4983230072969 + 3 ^ 40 * 3720040 * 2
def baseEnd_3720040 : Nat := 424481905322606791131523

theorem tailTrace_3720040 : CollatzResearch.WordTrace tailWord_3720040 prefixEnd_3720040 424481905322606791131523 := by
  unfold tailWord_3720040
  simp only [CollatzResearch.WordTrace]
  refine ⟨67840502721468943547862787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90454003628625258063817049 67840502721468943547862787)
  ·
    refine ⟨101760754082203415321794181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67840502721468943547862787 101760754082203415321794181)
    ·
      refine ⟨19080141390413140372836409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 101760754082203415321794181 19080141390413140372836409)
      ·
        refine ⟨14310106042809855279627307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19080141390413140372836409 14310106042809855279627307)
        ·
          refine ⟨21465159064214782919440961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14310106042809855279627307 21465159064214782919440961)
          ·
            refine ⟨16098869298161087189580721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21465159064214782919440961 16098869298161087189580721)
            ·
              refine ⟨12074151973620815392185541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16098869298161087189580721 12074151973620815392185541)
              ·
                refine ⟨2263903495053902886034789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12074151973620815392185541 2263903495053902886034789)
                ·
                  refine ⟨424481905322606791131523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2263903495053902886034789 424481905322606791131523)
                  ·
                    rfl

theorem cell22_3720040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 2, 4, 4].length) (baseStart_3720040 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3720040 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3720040 prefixEnd_3720040 := by exact prefixLift 3720040
  have htrace : WordTrace (prefixWord ++ tailWord_3720040) baseStart_3720040 baseEnd_3720040 := by
    simpa [prefixWord, tailWord_3720040, baseEnd_3720040] using wordTrace_append hprefix tailTrace_3720040
  have hstable : (prefixWord ++ tailWord_3720040).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3720040).length < 2 ^ (prefixWord ++ tailWord_3720040).sum := by decide
  have hdescent : baseEnd_3720040 < baseStart_3720040 := by decide
  rcases family_descends (prefixWord ++ tailWord_3720040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3720053 : List Nat := [1, 3, 4, 1, 1, 2, 1, 2, 1, 6]
def baseStart_3720053 : Nat := 118140960795 + 3720053 * 2 ^ 59
def prefixEnd_3720053 : Nat := 4983230072969 + 3 ^ 40 * 3720053 * 2
def baseEnd_3720053 : Nat := 1273450166133492672819529

theorem tailTrace_3720053 : CollatzResearch.WordTrace tailWord_3720053 prefixEnd_3720053 1273450166133492672819529 := by
  unfold tailWord_3720053
  simp only [CollatzResearch.WordTrace]
  refine ⟨135681479591890790315948813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90454319727927193543965875 135681479591890790315948813)
  ·
    refine ⟨50880554846959046368480805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135681479591890790315948813 50880554846959046368480805)
    ·
      refine ⟨9540104033804821194090151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50880554846959046368480805 9540104033804821194090151)
      ·
        refine ⟨14310156050707231791135227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9540104033804821194090151 14310156050707231791135227)
        ·
          refine ⟨21465234076060847686702841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14310156050707231791135227 21465234076060847686702841)
          ·
            refine ⟨16098925557045635765027131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21465234076060847686702841 16098925557045635765027131)
            ·
              refine ⟨24148388335568453647540697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16098925557045635765027131 24148388335568453647540697)
              ·
                refine ⟨18111291251676340235655523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24148388335568453647540697 18111291251676340235655523)
                ·
                  refine ⟨27166936877514510353483285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18111291251676340235655523 27166936877514510353483285)
                  ·
                    refine ⟨1273450166133492672819529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27166936877514510353483285 1273450166133492672819529)
                    ·
                      rfl

theorem cell22_3720053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 1, 2, 1, 6].length) (baseStart_3720053 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3720053 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3720053 prefixEnd_3720053 := by exact prefixLift 3720053
  have htrace : WordTrace (prefixWord ++ tailWord_3720053) baseStart_3720053 baseEnd_3720053 := by
    simpa [prefixWord, tailWord_3720053, baseEnd_3720053] using wordTrace_append hprefix tailTrace_3720053
  have hstable : (prefixWord ++ tailWord_3720053).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3720053).length < 2 ^ (prefixWord ++ tailWord_3720053).sum := by decide
  have hdescent : baseEnd_3720053 < baseStart_3720053 := by decide
  rcases family_descends (prefixWord ++ tailWord_3720053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3720081 : List Nat := [1, 2, 2, 1, 1, 1, 3, 2, 1, 8]
def baseStart_3720081 : Nat := 118140960795 + 3720081 * 2 ^ 59
def prefixEnd_3720081 : Nat := 4983230072969 + 3 ^ 40 * 3720081 * 2
def baseEnd_3720081 : Nat := 1273459751105709933119443

theorem tailTrace_3720081 : CollatzResearch.WordTrace tailWord_3720081 prefixEnd_3720081 1273459751105709933119443 := by
  unfold tailWord_3720081
  simp only [CollatzResearch.WordTrace]
  refine ⟨135682500835789351097968097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90455000557192900731978731 135682500835789351097968097)
  ·
    refine ⟨101761875626842013323476073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135682500835789351097968097 101761875626842013323476073)
    ·
      refine ⟨76321406720131509992607055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101761875626842013323476073 76321406720131509992607055)
      ·
        refine ⟨114482110080197264988910583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76321406720131509992607055 114482110080197264988910583)
        ·
          refine ⟨171723165120295897483365875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114482110080197264988910583 171723165120295897483365875)
          ·
            refine ⟨257584747680443846225048813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 171723165120295897483365875 257584747680443846225048813)
            ·
              refine ⟨96594280380166442334393305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 257584747680443846225048813 96594280380166442334393305)
              ·
                refine ⟨72445710285124831750794979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 96594280380166442334393305 72445710285124831750794979)
                ·
                  refine ⟨108668565427687247626192469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 72445710285124831750794979 108668565427687247626192469)
                  ·
                    refine ⟨1273459751105709933119443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 108668565427687247626192469 1273459751105709933119443)
                    ·
                      rfl

theorem cell22_3720081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 8].length) (baseStart_3720081 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3720081 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3720081 prefixEnd_3720081 := by exact prefixLift 3720081
  have htrace : WordTrace (prefixWord ++ tailWord_3720081) baseStart_3720081 baseEnd_3720081 := by
    simpa [prefixWord, tailWord_3720081, baseEnd_3720081] using wordTrace_append hprefix tailTrace_3720081
  have hstable : (prefixWord ++ tailWord_3720081).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3720081).length < 2 ^ (prefixWord ++ tailWord_3720081).sum := by decide
  have hdescent : baseEnd_3720081 < baseStart_3720081 := by decide
  rcases family_descends (prefixWord ++ tailWord_3720081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3720162 : List Nat := [3, 3, 3, 1, 1, 2, 1, 1, 2, 5]
def baseStart_3720162 : Nat := 118140960795 + 3720162 * 2 ^ 59
def prefixEnd_3720162 : Nat := 4983230072969 + 3 ^ 40 * 3720162 * 2
def baseEnd_3720162 : Nat := 1273487479061052721844195

theorem tailTrace_3720162 : CollatzResearch.WordTrace tailWord_3720162 prefixEnd_3720162 1273487479061052721844195 := by
  unfold tailWord_3720162
  simp only [CollatzResearch.WordTrace]
  refine ⟨33921363787123975482916685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90456970098997267954444493 33921363787123975482916685)
  ·
    refine ⟨12720511420171490806093757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33921363787123975482916685 12720511420171490806093757)
    ·
      refine ⟨4770191782564309052285159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12720511420171490806093757 4770191782564309052285159)
      ·
        refine ⟨7155287673846463578427739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4770191782564309052285159 7155287673846463578427739)
        ·
          refine ⟨10732931510769695367641609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7155287673846463578427739 10732931510769695367641609)
          ·
            refine ⟨8049698633077271525731207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10732931510769695367641609 8049698633077271525731207)
            ·
              refine ⟨12074547949615907288596811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8049698633077271525731207 12074547949615907288596811)
              ·
                refine ⟨18111821924423860932895217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12074547949615907288596811 18111821924423860932895217)
                ·
                  refine ⟨13583866443317895699671413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18111821924423860932895217 13583866443317895699671413)
                  ·
                    refine ⟨1273487479061052721844195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13583866443317895699671413 1273487479061052721844195)
                    ·
                      rfl

theorem cell22_3720162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 1, 1, 2, 5].length) (baseStart_3720162 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3720162 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3720162 prefixEnd_3720162 := by exact prefixLift 3720162
  have htrace : WordTrace (prefixWord ++ tailWord_3720162) baseStart_3720162 baseEnd_3720162 := by
    simpa [prefixWord, tailWord_3720162, baseEnd_3720162] using wordTrace_append hprefix tailTrace_3720162
  have hstable : (prefixWord ++ tailWord_3720162).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3720162).length < 2 ^ (prefixWord ++ tailWord_3720162).sum := by decide
  have hdescent : baseEnd_3720162 < baseStart_3720162 := by decide
  rcases family_descends (prefixWord ++ tailWord_3720162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3720203 : List Nat := [1, 1, 1, 1, 6, 3, 9]
def baseStart_3720203 : Nat := 118140960795 + 3720203 * 2 ^ 59
def prefixEnd_3720203 : Nat := 4983230072969 + 3 ^ 40 * 3720203 * 2
def baseEnd_3720203 : Nat := 47166722748108973391447

theorem tailTrace_3720203 : CollatzResearch.WordTrace tailWord_3720203 prefixEnd_3720203 47166722748108973391447 := by
  unfold tailWord_3720203
  simp only [CollatzResearch.WordTrace]
  refine ⟨135686950541347365933909263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90457967027564910622606175 135686950541347365933909263)
  ·
    refine ⟨203530425812021048900863895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135686950541347365933909263 203530425812021048900863895)
    ·
      refine ⟨305295638718031573351295843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203530425812021048900863895 305295638718031573351295843)
      ·
        refine ⟨457943458077047360026943765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 305295638718031573351295843 457943458077047360026943765)
        ·
          refine ⟨21466099597361595001262989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 457943458077047360026943765 21466099597361595001262989)
          ·
            refine ⟨8049787349010598125473621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21466099597361595001262989 8049787349010598125473621)
            ·
              refine ⟨47166722748108973391447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8049787349010598125473621 47166722748108973391447)
              ·
                rfl

theorem cell22_3720203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 9].length) (baseStart_3720203 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3720203 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3720203 prefixEnd_3720203 := by exact prefixLift 3720203
  have htrace : WordTrace (prefixWord ++ tailWord_3720203) baseStart_3720203 baseEnd_3720203 := by
    simpa [prefixWord, tailWord_3720203, baseEnd_3720203] using wordTrace_append hprefix tailTrace_3720203
  have hstable : (prefixWord ++ tailWord_3720203).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3720203).length < 2 ^ (prefixWord ++ tailWord_3720203).sum := by decide
  have hdescent : baseEnd_3720203 < baseStart_3720203 := by decide
  rcases family_descends (prefixWord ++ tailWord_3720203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3720224 : List Nat := [2, 1, 1, 7, 1, 2, 1, 1, 1, 5]
def baseStart_3720224 : Nat := 118140960795 + 3720224 * 2 ^ 59
def prefixEnd_3720224 : Nat := 4983230072969 + 3 ^ 40 * 3720224 * 2
def baseEnd_3720224 : Nat := 1273508702928105226794005

theorem tailTrace_3720224 : CollatzResearch.WordTrace tailWord_3720224 prefixEnd_3720224 1273508702928105226794005 := by
  unfold tailWord_3720224
  simp only [CollatzResearch.WordTrace]
  refine ⟨67843858237135643260211863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90458477649514191013615817 67843858237135643260211863)
  ·
    refine ⟨101765787355703464890317795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67843858237135643260211863 101765787355703464890317795)
    ·
      refine ⟨152648681033555197335476693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101765787355703464890317795 152648681033555197335476693)
      ·
        refine ⟨3577703461723949937550235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 152648681033555197335476693 3577703461723949937550235)
        ·
          refine ⟨5366555192585924906325353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3577703461723949937550235 5366555192585924906325353)
          ·
            refine ⟨4024916394439443679744015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5366555192585924906325353 4024916394439443679744015)
            ·
              refine ⟨6037374591659165519616023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4024916394439443679744015 6037374591659165519616023)
              ·
                refine ⟨9056061887488748279424035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6037374591659165519616023 9056061887488748279424035)
                ·
                  refine ⟨13584092831233122419136053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9056061887488748279424035 13584092831233122419136053)
                  ·
                    refine ⟨1273508702928105226794005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13584092831233122419136053 1273508702928105226794005)
                    ·
                      rfl

theorem cell22_3720224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 2, 1, 1, 1, 5].length) (baseStart_3720224 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3720224 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3720224 prefixEnd_3720224 := by exact prefixLift 3720224
  have htrace : WordTrace (prefixWord ++ tailWord_3720224) baseStart_3720224 baseEnd_3720224 := by
    simpa [prefixWord, tailWord_3720224, baseEnd_3720224] using wordTrace_append hprefix tailTrace_3720224
  have hstable : (prefixWord ++ tailWord_3720224).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3720224).length < 2 ^ (prefixWord ++ tailWord_3720224).sum := by decide
  have hdescent : baseEnd_3720224 < baseStart_3720224 := by decide
  rcases family_descends (prefixWord ++ tailWord_3720224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3720235 : List Nat := [1, 1, 1, 1, 2, 1, 5, 4, 3, 3]
def baseStart_3720235 : Nat := 118140960795 + 3720235 * 2 ^ 59
def prefixEnd_3720235 : Nat := 4983230072969 + 3 ^ 40 * 3720235 * 2
def baseEnd_3720235 : Nat := 1273512468452904864768971

theorem tailTrace_3720235 : CollatzResearch.WordTrace tailWord_3720235 prefixEnd_3720235 1273512468452904864768971 := by
  unfold tailWord_3720235
  simp only [CollatzResearch.WordTrace]
  refine ⟨135688117677231435399074159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90458745118154290266049439 135688117677231435399074159)
  ·
    refine ⟨203532176515847153098611239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135688117677231435399074159 203532176515847153098611239)
    ·
      refine ⟨305298264773770729647916859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203532176515847153098611239 305298264773770729647916859)
      ·
        refine ⟨457947397160656094471875289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 305298264773770729647916859 457947397160656094471875289)
        ·
          refine ⟨343460547870492070853906467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 457947397160656094471875289 343460547870492070853906467)
          ·
            refine ⟨515190821805738106280859701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 343460547870492070853906467 515190821805738106280859701)
            ·
              refine ⟨48299139544287947463830597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 515190821805738106280859701 48299139544287947463830597)
              ·
                refine ⟨9056088664553990149468237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48299139544287947463830597 9056088664553990149468237)
                ·
                  refine ⟨3396033249207746306050589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9056088664553990149468237 3396033249207746306050589)
                  ·
                    refine ⟨1273512468452904864768971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3396033249207746306050589 1273512468452904864768971)
                    ·
                      rfl

theorem cell22_3720235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 4, 3, 3].length) (baseStart_3720235 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3720235 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3720235 prefixEnd_3720235 := by exact prefixLift 3720235
  have htrace : WordTrace (prefixWord ++ tailWord_3720235) baseStart_3720235 baseEnd_3720235 := by
    simpa [prefixWord, tailWord_3720235, baseEnd_3720235] using wordTrace_append hprefix tailTrace_3720235
  have hstable : (prefixWord ++ tailWord_3720235).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3720235).length < 2 ^ (prefixWord ++ tailWord_3720235).sum := by decide
  have hdescent : baseEnd_3720235 < baseStart_3720235 := by decide
  rcases family_descends (prefixWord ++ tailWord_3720235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3720269 : List Nat := [1, 6, 1, 1, 1, 2, 3, 1, 3, 3]
def baseStart_3720269 : Nat := 118140960795 + 3720269 * 2 ^ 59
def prefixEnd_3720269 : Nat := 4983230072969 + 3 ^ 40 * 3720269 * 2
def baseEnd_3720269 : Nat := 1273524107347740109418867

theorem tailTrace_3720269 : CollatzResearch.WordTrace tailWord_3720269 prefixEnd_3720269 1273524107347740109418867 := by
  unfold tailWord_3720269
  simp only [CollatzResearch.WordTrace]
  refine ⟨135689357759108259205811861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90459571839405506137207907 135689357759108259205811861)
  ·
    refine ⟨6360438644958199650272431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 135689357759108259205811861 6360438644958199650272431)
    ·
      refine ⟨9540657967437299475408647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6360438644958199650272431 9540657967437299475408647)
      ·
        refine ⟨14310986951155949213112971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9540657967437299475408647 14310986951155949213112971)
        ·
          refine ⟨21466480426733923819669457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14310986951155949213112971 21466480426733923819669457)
          ·
            refine ⟨16099860320050442864752093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21466480426733923819669457 16099860320050442864752093)
            ·
              refine ⟨6037447620018916074282035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16099860320050442864752093 6037447620018916074282035)
              ·
                refine ⟨9056171430028374111423053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6037447620018916074282035 9056171430028374111423053)
                ·
                  refine ⟨3396064286260640291783645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9056171430028374111423053 3396064286260640291783645)
                  ·
                    refine ⟨1273524107347740109418867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3396064286260640291783645 1273524107347740109418867)
                    ·
                      rfl

theorem cell22_3720269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 3, 1, 3, 3].length) (baseStart_3720269 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3720269 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3720269 prefixEnd_3720269 := by exact prefixLift 3720269
  have htrace : WordTrace (prefixWord ++ tailWord_3720269) baseStart_3720269 baseEnd_3720269 := by
    simpa [prefixWord, tailWord_3720269, baseEnd_3720269] using wordTrace_append hprefix tailTrace_3720269
  have hstable : (prefixWord ++ tailWord_3720269).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3720269).length < 2 ^ (prefixWord ++ tailWord_3720269).sum := by decide
  have hdescent : baseEnd_3720269 < baseStart_3720269 := by decide
  rcases family_descends (prefixWord ++ tailWord_3720269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3720357 : List Nat := [1, 3, 1, 2, 1, 4, 3, 1, 2, 4]
def baseStart_3720357 : Nat := 118140960795 + 3720357 * 2 ^ 59
def prefixEnd_3720357 : Nat := 4983230072969 + 3 ^ 40 * 3720357 * 2
def baseEnd_3720357 : Nat := 1273554231546137213218597

theorem tailTrace_3720357 : CollatzResearch.WordTrace tailWord_3720357 prefixEnd_3720357 1273554231546137213218597 := by
  unfold tailWord_3720357
  simp only [CollatzResearch.WordTrace]
  refine ⟨135692567382789450235015325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90461711588526300156676883 135692567382789450235015325)
  ·
    refine ⟨50884712768546043838130747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135692567382789450235015325 50884712768546043838130747)
    ·
      refine ⟨76327069152819065757196121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50884712768546043838130747 76327069152819065757196121)
      ·
        refine ⟨57245301864614299317897091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76327069152819065757196121 57245301864614299317897091)
        ·
          refine ⟨85867952796921448976845637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57245301864614299317897091 85867952796921448976845637)
          ·
            refine ⟨16100241149422771683158557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 85867952796921448976845637 16100241149422771683158557)
            ·
              refine ⟨6037590431033539381184459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16100241149422771683158557 6037590431033539381184459)
              ·
                refine ⟨9056385646550309071776689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6037590431033539381184459 9056385646550309071776689)
                ·
                  refine ⟨6792289234912731803832517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9056385646550309071776689 6792289234912731803832517)
                  ·
                    refine ⟨1273554231546137213218597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6792289234912731803832517 1273554231546137213218597)
                    ·
                      rfl

theorem cell22_3720357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 3, 1, 2, 4].length) (baseStart_3720357 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3720357 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3720357 prefixEnd_3720357 := by exact prefixLift 3720357
  have htrace : WordTrace (prefixWord ++ tailWord_3720357) baseStart_3720357 baseEnd_3720357 := by
    simpa [prefixWord, tailWord_3720357, baseEnd_3720357] using wordTrace_append hprefix tailTrace_3720357
  have hstable : (prefixWord ++ tailWord_3720357).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3720357).length < 2 ^ (prefixWord ++ tailWord_3720357).sum := by decide
  have hdescent : baseEnd_3720357 < baseStart_3720357 := by decide
  rcases family_descends (prefixWord ++ tailWord_3720357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3720415 : List Nat := [1, 1, 2, 3, 2, 1, 2, 2, 1, 7]
def baseStart_3720415 : Nat := 118140960795 + 3720415 * 2 ^ 59
def prefixEnd_3720415 : Nat := 4983230072969 + 3 ^ 40 * 3720415 * 2
def baseEnd_3720415 : Nat := 1273574086131444395268419

theorem tailTrace_3720415 : CollatzResearch.WordTrace tailWord_3720415 prefixEnd_3720415 1273574086131444395268419 := by
  unfold tailWord_3720415
  simp only [CollatzResearch.WordTrace]
  refine ⟨135694682816579326140626699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90463121877719550760417799 135694682816579326140626699)
  ·
    refine ⟨203542024224868989210940049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135694682816579326140626699 203542024224868989210940049)
    ·
      refine ⟨152656518168651741908205037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 203542024224868989210940049 152656518168651741908205037)
      ·
        refine ⟨57246194313244403215576889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 152656518168651741908205037 57246194313244403215576889)
        ·
          refine ⟨42934645734933302411682667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57246194313244403215576889 42934645734933302411682667)
          ·
            refine ⟨64401968602399953617524001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42934645734933302411682667 64401968602399953617524001)
            ·
              refine ⟨48301476451799965213143001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64401968602399953617524001 48301476451799965213143001)
              ·
                refine ⟨36226107338849973909857251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48301476451799965213143001 36226107338849973909857251)
                ·
                  refine ⟨54339161008274960864785877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36226107338849973909857251 54339161008274960864785877)
                  ·
                    refine ⟨1273574086131444395268419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 54339161008274960864785877 1273574086131444395268419)
                    ·
                      rfl

theorem cell22_3720415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 2, 1, 7].length) (baseStart_3720415 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3720415 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3720415 prefixEnd_3720415 := by exact prefixLift 3720415
  have htrace : WordTrace (prefixWord ++ tailWord_3720415) baseStart_3720415 baseEnd_3720415 := by
    simpa [prefixWord, tailWord_3720415, baseEnd_3720415] using wordTrace_append hprefix tailTrace_3720415
  have hstable : (prefixWord ++ tailWord_3720415).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3720415).length < 2 ^ (prefixWord ++ tailWord_3720415).sum := by decide
  have hdescent : baseEnd_3720415 < baseStart_3720415 := by decide
  rcases family_descends (prefixWord ++ tailWord_3720415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3720524 : List Nat := [2, 2, 1, 3, 2, 3, 3, 6]
def baseStart_3720524 : Nat := 118140960795 + 3720524 * 2 ^ 59
def prefixEnd_3720524 : Nat := 4983230072969 + 3 ^ 40 * 3720524 * 2
def baseEnd_3720524 : Nat := 141512377673222716032565

theorem tailTrace_3720524 : CollatzResearch.WordTrace tailWord_3720524 prefixEnd_3720524 141512377673222716032565 := by
  unfold tailWord_3720524
  simp only [CollatzResearch.WordTrace]
  refine ⟨67849329186592218878172313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90465772248789625170896417 67849329186592218878172313)
  ·
    refine ⟨50886996889944164158629235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67849329186592218878172313 50886996889944164158629235)
    ·
      refine ⟨76330495334916246237943853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50886996889944164158629235 76330495334916246237943853)
      ·
        refine ⟨28623935750593592339228945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76330495334916246237943853 28623935750593592339228945)
        ·
          refine ⟨21467951812945194254421709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28623935750593592339228945 21467951812945194254421709)
          ·
            refine ⟨8050481929854447845408141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21467951812945194254421709 8050481929854447845408141)
            ·
              refine ⟨3018930723695417942028053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8050481929854447845408141 3018930723695417942028053)
              ·
                refine ⟨141512377673222716032565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3018930723695417942028053 141512377673222716032565)
                ·
                  rfl

theorem cell22_3720524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 3, 6].length) (baseStart_3720524 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3720524 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3720524 prefixEnd_3720524 := by exact prefixLift 3720524
  have htrace : WordTrace (prefixWord ++ tailWord_3720524) baseStart_3720524 baseEnd_3720524 := by
    simpa [prefixWord, tailWord_3720524, baseEnd_3720524] using wordTrace_append hprefix tailTrace_3720524
  have hstable : (prefixWord ++ tailWord_3720524).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3720524).length < 2 ^ (prefixWord ++ tailWord_3720524).sum := by decide
  have hdescent : baseEnd_3720524 < baseStart_3720524 := by decide
  rcases family_descends (prefixWord ++ tailWord_3720524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3720556 : List Nat := [2, 2, 1, 1, 5, 2, 2, 1, 3, 3]
def baseStart_3720556 : Nat := 118140960795 + 3720556 * 2 ^ 59
def prefixEnd_3720556 : Nat := 4983230072969 + 3 ^ 40 * 3720556 * 2
def baseEnd_3720556 : Nat := 1273622353312967027492987

theorem tailTrace_3720556 : CollatzResearch.WordTrace tailWord_3720556 prefixEnd_3720556 1273622353312967027492987 := by
  unfold tailWord_3720556
  simp only [CollatzResearch.WordTrace]
  refine ⟨67849912754534253610754761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90466550339379004814339681 67849912754534253610754761)
  ·
    refine ⟨50887434565900690208066071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67849912754534253610754761 50887434565900690208066071)
    ·
      refine ⟨76331151848851035312099107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50887434565900690208066071 76331151848851035312099107)
      ·
        refine ⟨114496727773276552968148661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76331151848851035312099107 114496727773276552968148661)
        ·
          refine ⟨10734068228744676840763937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 114496727773276552968148661 10734068228744676840763937)
          ·
            refine ⟨8050551171558507630572953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10734068228744676840763937 8050551171558507630572953)
            ·
              refine ⟨6037913378668880722929715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8050551171558507630572953 6037913378668880722929715)
              ·
                refine ⟨9056870068003321084394573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6037913378668880722929715 9056870068003321084394573)
                ·
                  refine ⟨3396326275501245406647965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9056870068003321084394573 3396326275501245406647965)
                  ·
                    refine ⟨1273622353312967027492987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3396326275501245406647965 1273622353312967027492987)
                    ·
                      rfl

theorem cell22_3720556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 3, 3].length) (baseStart_3720556 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3720556 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3720556 prefixEnd_3720556 := by exact prefixLift 3720556
  have htrace : WordTrace (prefixWord ++ tailWord_3720556) baseStart_3720556 baseEnd_3720556 := by
    simpa [prefixWord, tailWord_3720556, baseEnd_3720556] using wordTrace_append hprefix tailTrace_3720556
  have hstable : (prefixWord ++ tailWord_3720556).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3720556).length < 2 ^ (prefixWord ++ tailWord_3720556).sum := by decide
  have hdescent : baseEnd_3720556 < baseStart_3720556 := by decide
  rcases family_descends (prefixWord ++ tailWord_3720556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3720567 : List Nat := [1, 1, 3, 1, 1, 2, 3, 3, 2, 5]
def baseStart_3720567 : Nat := 118140960795 + 3720567 * 2 ^ 59
def prefixEnd_3720567 : Nat := 4983230072969 + 3 ^ 40 * 3720567 * 2
def baseEnd_3720567 : Nat := 1273626118837766665467953

theorem tailTrace_3720567 : CollatzResearch.WordTrace tailWord_3720567 prefixEnd_3720567 1273626118837766665467953 := by
  unfold tailWord_3720567
  simp only [CollatzResearch.WordTrace]
  refine ⟨135700226712028656100159955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90466817808019104066773303 135700226712028656100159955)
  ·
    refine ⟨203550340068042984150239933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135700226712028656100159955 203550340068042984150239933)
    ·
      refine ⟨76331377525516119056339975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 203550340068042984150239933 76331377525516119056339975)
      ·
        refine ⟨114497066288274178584509963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76331377525516119056339975 114497066288274178584509963)
        ·
          refine ⟨171745599432411267876764945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114497066288274178584509963 171745599432411267876764945)
          ·
            refine ⟨128809199574308450907573709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 171745599432411267876764945 128809199574308450907573709)
            ·
              refine ⟨48303449840365669090340141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 128809199574308450907573709 48303449840365669090340141)
              ·
                refine ⟨18113793690137125908877553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48303449840365669090340141 18113793690137125908877553)
                ·
                  refine ⟨13585345267602844431658165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18113793690137125908877553 13585345267602844431658165)
                  ·
                    refine ⟨1273626118837766665467953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13585345267602844431658165 1273626118837766665467953)
                    ·
                      rfl

theorem cell22_3720567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 3, 2, 5].length) (baseStart_3720567 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3720567 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3720567 prefixEnd_3720567 := by exact prefixLift 3720567
  have htrace : WordTrace (prefixWord ++ tailWord_3720567) baseStart_3720567 baseEnd_3720567 := by
    simpa [prefixWord, tailWord_3720567, baseEnd_3720567] using wordTrace_append hprefix tailTrace_3720567
  have hstable : (prefixWord ++ tailWord_3720567).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3720567).length < 2 ^ (prefixWord ++ tailWord_3720567).sum := by decide
  have hdescent : baseEnd_3720567 < baseStart_3720567 := by decide
  rcases family_descends (prefixWord ++ tailWord_3720567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3720597 : List Nat := [1, 3, 2, 1, 1, 2, 2, 2, 8]
def baseStart_3720597 : Nat := 118140960795 + 3720597 * 2 ^ 59
def prefixEnd_3720597 : Nat := 4983230072969 + 3 ^ 40 * 3720597 * 2
def baseEnd_3720597 : Nat := 424545462816952195739287

theorem tailTrace_3720597 : CollatzResearch.WordTrace tailWord_3720597 prefixEnd_3720597 424545462816952195739287 := by
  unfold tailWord_3720597
  simp only [CollatzResearch.WordTrace]
  refine ⟨135701320901919971223752045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90467547267946647482501363 135701320901919971223752045)
  ·
    refine ⟨50887995338219989208907017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135701320901919971223752045 50887995338219989208907017)
    ·
      refine ⟨38165996503664991906680263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50887995338219989208907017 38165996503664991906680263)
      ·
        refine ⟨57248994755497487860020395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38165996503664991906680263 57248994755497487860020395)
        ·
          refine ⟨85873492133246231790030593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57248994755497487860020395 85873492133246231790030593)
          ·
            refine ⟨64405119099934673842522945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85873492133246231790030593 64405119099934673842522945)
            ·
              refine ⟨48303839324951005381892209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64405119099934673842522945 48303839324951005381892209)
              ·
                refine ⟨36227879493713254036419157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48303839324951005381892209 36227879493713254036419157)
                ·
                  refine ⟨424545462816952195739287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 36227879493713254036419157 424545462816952195739287)
                  ·
                    rfl

theorem cell22_3720597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 2, 8].length) (baseStart_3720597 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3720597 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3720597 prefixEnd_3720597 := by exact prefixLift 3720597
  have htrace : WordTrace (prefixWord ++ tailWord_3720597) baseStart_3720597 baseEnd_3720597 := by
    simpa [prefixWord, tailWord_3720597, baseEnd_3720597] using wordTrace_append hprefix tailTrace_3720597
  have hstable : (prefixWord ++ tailWord_3720597).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3720597).length < 2 ^ (prefixWord ++ tailWord_3720597).sum := by decide
  have hdescent : baseEnd_3720597 < baseStart_3720597 := by decide
  rcases family_descends (prefixWord ++ tailWord_3720597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3720627 : List Nat := [1, 1, 1, 2, 3, 1, 1, 3, 3, 6]
def baseStart_3720627 : Nat := 118140960795 + 3720627 * 2 ^ 59
def prefixEnd_3720627 : Nat := 4983230072969 + 3 ^ 40 * 3720627 * 2
def baseEnd_3720627 : Nat := 1273646658063946508967769

theorem tailTrace_3720627 : CollatzResearch.WordTrace tailWord_3720627 prefixEnd_3720627 1273646658063946508967769 := by
  unfold tailWord_3720627
  simp only [CollatzResearch.WordTrace]
  refine ⟨135702415091811286347344135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90468276727874190898229423 135702415091811286347344135)
  ·
    refine ⟨203553622637716929521016203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135702415091811286347344135 203553622637716929521016203)
    ·
      refine ⟨305330433956575394281524305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203553622637716929521016203 305330433956575394281524305)
      ·
        refine ⟨228997825467431545711143229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 305330433956575394281524305 228997825467431545711143229)
        ·
          refine ⟨85874184550286829641678711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 228997825467431545711143229 85874184550286829641678711)
          ·
            refine ⟨128811276825430244462518067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85874184550286829641678711 128811276825430244462518067)
            ·
              refine ⟨193216915238145366693777101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 128811276825430244462518067 193216915238145366693777101)
              ·
                refine ⟨72456343214304512510166413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 193216915238145366693777101 72456343214304512510166413)
                ·
                  refine ⟨27171128705364192191312405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 72456343214304512510166413 27171128705364192191312405)
                  ·
                    refine ⟨1273646658063946508967769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27171128705364192191312405 1273646658063946508967769)
                    ·
                      rfl

theorem cell22_3720627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 3, 3, 6].length) (baseStart_3720627 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3720627 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3720627 prefixEnd_3720627 := by exact prefixLift 3720627
  have htrace : WordTrace (prefixWord ++ tailWord_3720627) baseStart_3720627 baseEnd_3720627 := by
    simpa [prefixWord, tailWord_3720627, baseEnd_3720627] using wordTrace_append hprefix tailTrace_3720627
  have hstable : (prefixWord ++ tailWord_3720627).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3720627).length < 2 ^ (prefixWord ++ tailWord_3720627).sum := by decide
  have hdescent : baseEnd_3720627 < baseStart_3720627 := by decide
  rcases family_descends (prefixWord ++ tailWord_3720627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3720633 : List Nat := [1, 2, 1, 4, 4, 2, 1, 2, 1, 4]
def baseStart_3720633 : Nat := 118140960795 + 3720633 * 2 ^ 59
def prefixEnd_3720633 : Nat := 4983230072969 + 3 ^ 40 * 3720633 * 2
def baseEnd_3720633 : Nat := 1273648711986564493317751

theorem tailTrace_3720633 : CollatzResearch.WordTrace tailWord_3720633 prefixEnd_3720633 1273648711986564493317751 := by
  unfold tailWord_3720633
  simp only [CollatzResearch.WordTrace]
  refine ⟨135702633929789549372062553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90468422619859699581375035 135702633929789549372062553)
  ·
    refine ⟨101776975447342162029046915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135702633929789549372062553 101776975447342162029046915)
    ·
      refine ⟨152665463171013243043570373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101776975447342162029046915 152665463171013243043570373)
      ·
        refine ⟨28624774344564983070669445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 152665463171013243043570373 28624774344564983070669445)
        ·
          refine ⟨5367145189605934325750521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28624774344564983070669445 5367145189605934325750521)
          ·
            refine ⟨4025358892204450744312891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5367145189605934325750521 4025358892204450744312891)
            ·
              refine ⟨6038038338306676116469337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4025358892204450744312891 6038038338306676116469337)
              ·
                refine ⟨4528528753730007087352003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6038038338306676116469337 4528528753730007087352003)
                ·
                  refine ⟨6792793130595010631028005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4528528753730007087352003 6792793130595010631028005)
                  ·
                    refine ⟨1273648711986564493317751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6792793130595010631028005 1273648711986564493317751)
                    ·
                      rfl

theorem cell22_3720633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 2, 1, 2, 1, 4].length) (baseStart_3720633 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3720633 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3720633 prefixEnd_3720633 := by exact prefixLift 3720633
  have htrace : WordTrace (prefixWord ++ tailWord_3720633) baseStart_3720633 baseEnd_3720633 := by
    simpa [prefixWord, tailWord_3720633, baseEnd_3720633] using wordTrace_append hprefix tailTrace_3720633
  have hstable : (prefixWord ++ tailWord_3720633).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3720633).length < 2 ^ (prefixWord ++ tailWord_3720633).sum := by decide
  have hdescent : baseEnd_3720633 < baseStart_3720633 := by decide
  rcases family_descends (prefixWord ++ tailWord_3720633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3720693 : List Nat := [1, 3, 5, 1, 1, 2, 3, 6]
def baseStart_3720693 : Nat := 118140960795 + 3720693 * 2 ^ 59
def prefixEnd_3720693 : Nat := 4983230072969 + 3 ^ 40 * 3720693 * 2
def baseEnd_3720693 : Nat := 141518805690304926313063

theorem tailTrace_3720693 : CollatzResearch.WordTrace tailWord_3720693 prefixEnd_3720693 141518805690304926313063 := by
  unfold tailWord_3720693
  simp only [CollatzResearch.WordTrace]
  refine ⟨135704822309572179619246733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90469881539714786412831155 135704822309572179619246733)
  ·
    refine ⟨50889308366089567357217525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135704822309572179619246733 50889308366089567357217525)
    ·
      refine ⟨4770872659320896939739143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 50889308366089567357217525 4770872659320896939739143)
      ·
        refine ⟨7156308988981345409608715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4770872659320896939739143 7156308988981345409608715)
        ·
          refine ⟨10734463483472018114413073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7156308988981345409608715 10734463483472018114413073)
          ·
            refine ⟨8050847612604013585809805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10734463483472018114413073 8050847612604013585809805)
            ·
              refine ⟨3019067854726505094678677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8050847612604013585809805 3019067854726505094678677)
              ·
                refine ⟨141518805690304926313063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3019067854726505094678677 141518805690304926313063)
                ·
                  rfl

theorem cell22_3720693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 3, 6].length) (baseStart_3720693 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3720693 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3720693 prefixEnd_3720693 := by exact prefixLift 3720693
  have htrace : WordTrace (prefixWord ++ tailWord_3720693) baseStart_3720693 baseEnd_3720693 := by
    simpa [prefixWord, tailWord_3720693, baseEnd_3720693] using wordTrace_append hprefix tailTrace_3720693
  have hstable : (prefixWord ++ tailWord_3720693).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3720693).length < 2 ^ (prefixWord ++ tailWord_3720693).sum := by decide
  have hdescent : baseEnd_3720693 < baseStart_3720693 := by decide
  rcases family_descends (prefixWord ++ tailWord_3720693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3720710 : List Nat := [6, 2, 1, 1, 2, 1, 9]
def baseStart_3720710 : Nat := 118140960795 + 3720710 * 2 ^ 59
def prefixEnd_3720710 : Nat := 4983230072969 + 3 ^ 40 * 3720710 * 2
def baseEnd_3720710 : Nat := 47173150765191183671945

theorem tailTrace_3720710 : CollatzResearch.WordTrace tailWord_3720710 prefixEnd_3720710 47173150765191183671945 := by
  unfold tailWord_3720710
  simp only [CollatzResearch.WordTrace]
  refine ⟨4240795073453455985081737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 90470294900340394348410389 4240795073453455985081737)
  ·
    refine ⟨3180596305090091988811303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4240795073453455985081737 3180596305090091988811303)
    ·
      refine ⟨4770894457635137983216955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3180596305090091988811303 4770894457635137983216955)
      ·
        refine ⟨7156341686452706974825433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4770894457635137983216955 7156341686452706974825433)
        ·
          refine ⟨5367256264839530231119075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7156341686452706974825433 5367256264839530231119075)
          ·
            refine ⟨8050884397259295346678613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5367256264839530231119075 8050884397259295346678613)
            ·
              refine ⟨47173150765191183671945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8050884397259295346678613 47173150765191183671945)
              ·
                rfl

theorem cell22_3720710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 9].length) (baseStart_3720710 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3720710 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3720710 prefixEnd_3720710 := by exact prefixLift 3720710
  have htrace : WordTrace (prefixWord ++ tailWord_3720710) baseStart_3720710 baseEnd_3720710 := by
    simpa [prefixWord, tailWord_3720710, baseEnd_3720710] using wordTrace_append hprefix tailTrace_3720710
  have hstable : (prefixWord ++ tailWord_3720710).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3720710).length < 2 ^ (prefixWord ++ tailWord_3720710).sum := by decide
  have hdescent : baseEnd_3720710 < baseStart_3720710 := by decide
  rcases family_descends (prefixWord ++ tailWord_3720710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3720736 : List Nat := [2, 1, 1, 6, 1, 1, 2, 1, 2, 5]
def baseStart_3720736 : Nat := 118140960795 + 3720736 * 2 ^ 59
def prefixEnd_3720736 : Nat := 4983230072969 + 3 ^ 40 * 3720736 * 2
def baseEnd_3720736 : Nat := 1273683970991506557992435

theorem tailTrace_3720736 : CollatzResearch.WordTrace tailWord_3720736 prefixEnd_3720736 1273683970991506557992435 := by
  unfold tailWord_3720736
  simp only [CollatzResearch.WordTrace]
  refine ⟨67853195324208198981531031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90470927098944265308708041 67853195324208198981531031)
  ·
    refine ⟨101779792986312298472296547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67853195324208198981531031 101779792986312298472296547)
    ·
      refine ⟨152669689479468447708444821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101779792986312298472296547 152669689479468447708444821)
      ·
        refine ⟨7156391694350083486333351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 152669689479468447708444821 7156391694350083486333351)
        ·
          refine ⟨10734587541525125229500027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7156391694350083486333351 10734587541525125229500027)
          ·
            refine ⟨16101881312287687844250041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10734587541525125229500027 16101881312287687844250041)
            ·
              refine ⟨12076410984215765883187531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16101881312287687844250041 12076410984215765883187531)
              ·
                refine ⟨18114616476323648824781297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12076410984215765883187531 18114616476323648824781297)
                ·
                  refine ⟨13585962357242736618585973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18114616476323648824781297 13585962357242736618585973)
                  ·
                    refine ⟨1273683970991506557992435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13585962357242736618585973 1273683970991506557992435)
                    ·
                      rfl

theorem cell22_3720736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 2, 1, 2, 5].length) (baseStart_3720736 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3720736 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3720736 prefixEnd_3720736 := by exact prefixLift 3720736
  have htrace : WordTrace (prefixWord ++ tailWord_3720736) baseStart_3720736 baseEnd_3720736 := by
    simpa [prefixWord, tailWord_3720736, baseEnd_3720736] using wordTrace_append hprefix tailTrace_3720736
  have hstable : (prefixWord ++ tailWord_3720736).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3720736).length < 2 ^ (prefixWord ++ tailWord_3720736).sum := by decide
  have hdescent : baseEnd_3720736 < baseStart_3720736 := by decide
  rcases family_descends (prefixWord ++ tailWord_3720736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3720809 : List Nat := [1, 2, 1, 1, 1, 4, 2, 1, 2, 7]
def baseStart_3720809 : Nat := 118140960795 + 3720809 * 2 ^ 59
def prefixEnd_3720809 : Nat := 4983230072969 + 3 ^ 40 * 3720809 * 2
def baseEnd_3720809 : Nat := 1273708960383358700917211

theorem tailTrace_3720809 : CollatzResearch.WordTrace tailWord_3720809 prefixEnd_3720809 1273708960383358700917211 := by
  unfold tailWord_3720809
  simp only [CollatzResearch.WordTrace]
  refine ⟨135709053177151931430469481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90472702118101287620312987 135709053177151931430469481)
  ·
    refine ⟨101781789882863948572852111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135709053177151931430469481 101781789882863948572852111)
    ·
      refine ⟨152672684824295922859278167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101781789882863948572852111 152672684824295922859278167)
      ·
        refine ⟨229009027236443884288917251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152672684824295922859278167 229009027236443884288917251)
        ·
          refine ⟨343513540854665826433375877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 229009027236443884288917251 343513540854665826433375877)
          ·
            refine ⟨64408788910249842456257977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 343513540854665826433375877 64408788910249842456257977)
            ·
              refine ⟨48306591682687381842193483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64408788910249842456257977 48306591682687381842193483)
              ·
                refine ⟨72459887524031072763290225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48306591682687381842193483 72459887524031072763290225)
                ·
                  refine ⟨54344915643023304572467669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 72459887524031072763290225 54344915643023304572467669)
                  ·
                    refine ⟨1273708960383358700917211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 54344915643023304572467669 1273708960383358700917211)
                    ·
                      rfl

theorem cell22_3720809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 1, 2, 7].length) (baseStart_3720809 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3720809 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3720809 prefixEnd_3720809 := by exact prefixLift 3720809
  have htrace : WordTrace (prefixWord ++ tailWord_3720809) baseStart_3720809 baseEnd_3720809 := by
    simpa [prefixWord, tailWord_3720809, baseEnd_3720809] using wordTrace_append hprefix tailTrace_3720809
  have hstable : (prefixWord ++ tailWord_3720809).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3720809).length < 2 ^ (prefixWord ++ tailWord_3720809).sum := by decide
  have hdescent : baseEnd_3720809 < baseStart_3720809 := by decide
  rcases family_descends (prefixWord ++ tailWord_3720809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3720824 : List Nat := [2, 1, 2, 1, 1, 1, 2, 1, 3, 8]
def baseStart_3720824 : Nat := 118140960795 + 3720824 * 2 ^ 59
def prefixEnd_3720824 : Nat := 4983230072969 + 3 ^ 40 * 3720824 * 2
def baseEnd_3720824 : Nat := 1273714095189903661792165

theorem tailTrace_3720824 : CollatzResearch.WordTrace tailWord_3720824 prefixEnd_3720824 1273714095189903661792165 := by
  unfold tailWord_3720824
  simp only [CollatzResearch.WordTrace]
  refine ⟨67854800136048794496132763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90473066848065059328177017 67854800136048794496132763)
  ·
    refine ⟨101782200204073191744199145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67854800136048794496132763 101782200204073191744199145)
    ·
      refine ⟨76336650153054893808149359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101782200204073191744199145 76336650153054893808149359)
      ·
        refine ⟨114504975229582340712224039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76336650153054893808149359 114504975229582340712224039)
        ·
          refine ⟨171757462844373511068336059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114504975229582340712224039 171757462844373511068336059)
          ·
            refine ⟨257636194266560266602504089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 171757462844373511068336059 257636194266560266602504089)
            ·
              refine ⟨193227145699920199951878067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 257636194266560266602504089 193227145699920199951878067)
              ·
                refine ⟨289840718549880299927817101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 193227145699920199951878067 289840718549880299927817101)
                ·
                  refine ⟨108690269456205112472931413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 289840718549880299927817101 108690269456205112472931413)
                  ·
                    refine ⟨1273714095189903661792165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 108690269456205112472931413 1273714095189903661792165)
                    ·
                      rfl

theorem cell22_3720824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 1, 3, 8].length) (baseStart_3720824 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3720824 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3720824 prefixEnd_3720824 := by exact prefixLift 3720824
  have htrace : WordTrace (prefixWord ++ tailWord_3720824) baseStart_3720824 baseEnd_3720824 := by
    simpa [prefixWord, tailWord_3720824, baseEnd_3720824] using wordTrace_append hprefix tailTrace_3720824
  have hstable : (prefixWord ++ tailWord_3720824).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3720824).length < 2 ^ (prefixWord ++ tailWord_3720824).sum := by decide
  have hdescent : baseEnd_3720824 < baseStart_3720824 := by decide
  rcases family_descends (prefixWord ++ tailWord_3720824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3720826 : List Nat := [3, 1, 1, 1, 1, 1, 1, 3, 7, 3]
def baseStart_3720826 : Nat := 118140960795 + 3720826 * 2 ^ 59
def prefixEnd_3720826 : Nat := 4983230072969 + 3 ^ 40 * 3720826 * 2
def baseEnd_3720826 : Nat := 1273714779830776323242159

theorem tailTrace_3720826 : CollatzResearch.WordTrace tailWord_3720826 prefixEnd_3720826 1273714779830776323242159 := by
  unfold tailWord_3720826
  simp only [CollatzResearch.WordTrace]
  refine ⟨33927418304522585833459583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90473115478726895555892221 33927418304522585833459583)
  ·
    refine ⟨50891127456783878750189375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33927418304522585833459583 50891127456783878750189375)
    ·
      refine ⟨76336691185175818125284063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50891127456783878750189375 76336691185175818125284063)
      ·
        refine ⟨114505036777763727187926095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76336691185175818125284063 114505036777763727187926095)
        ·
          refine ⟨171757555166645590781889143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114505036777763727187926095 171757555166645590781889143)
          ·
            refine ⟨257636332749968386172833715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 171757555166645590781889143 257636332749968386172833715)
            ·
              refine ⟨386454499124952579259250573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 257636332749968386172833715 386454499124952579259250573)
              ·
                refine ⟨144920437171857217222218965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 386454499124952579259250573 144920437171857217222218965)
                ·
                  refine ⟨3396572746215403528645757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 144920437171857217222218965 3396572746215403528645757)
                  ·
                    refine ⟨1273714779830776323242159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3396572746215403528645757 1273714779830776323242159)
                    ·
                      rfl

theorem cell22_3720826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 3, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 3, 7, 3].length) (baseStart_3720826 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3720826 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3720826 prefixEnd_3720826 := by exact prefixLift 3720826
  have htrace : WordTrace (prefixWord ++ tailWord_3720826) baseStart_3720826 baseEnd_3720826 := by
    simpa [prefixWord, tailWord_3720826, baseEnd_3720826] using wordTrace_append hprefix tailTrace_3720826
  have hstable : (prefixWord ++ tailWord_3720826).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3720826).length < 2 ^ (prefixWord ++ tailWord_3720826).sum := by decide
  have hdescent : baseEnd_3720826 < baseStart_3720826 := by decide
  rcases family_descends (prefixWord ++ tailWord_3720826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3720860 : List Nat := [2, 2, 3, 2, 3, 1, 1, 2, 3, 3]
def baseStart_3720860 : Nat := 118140960795 + 3720860 * 2 ^ 59
def prefixEnd_3720860 : Nat := 4983230072969 + 3 ^ 40 * 3720860 * 2
def baseEnd_3720860 : Nat := 1273726418725611567892055

theorem tailTrace_3720860 : CollatzResearch.WordTrace tailWord_3720860 prefixEnd_3720860 1273726418725611567892055 := by
  unfold tailWord_3720860
  simp only [CollatzResearch.WordTrace]
  refine ⟨67855456649983583570288017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90473942199978111427050689 67855456649983583570288017)
  ·
    refine ⟨50891592487487687677716013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67855456649983583570288017 50891592487487687677716013)
    ·
      refine ⟨19084347182807882879143505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50891592487487687677716013 19084347182807882879143505)
      ·
        refine ⟨14313260387105912159357629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19084347182807882879143505 14313260387105912159357629)
        ·
          refine ⟨5367472645164717059759111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14313260387105912159357629 5367472645164717059759111)
          ·
            refine ⟨8051208967747075589638667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5367472645164717059759111 8051208967747075589638667)
            ·
              refine ⟨12076813451620613384458001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8051208967747075589638667 12076813451620613384458001)
              ·
                refine ⟨9057610088715460038343501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12076813451620613384458001 9057610088715460038343501)
                ·
                  refine ⟨3396603783268297514378813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9057610088715460038343501 3396603783268297514378813)
                  ·
                    refine ⟨1273726418725611567892055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3396603783268297514378813 1273726418725611567892055)
                    ·
                      rfl

theorem cell22_3720860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 1, 2, 3, 3].length) (baseStart_3720860 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3720860 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3720860 prefixEnd_3720860 := by exact prefixLift 3720860
  have htrace : WordTrace (prefixWord ++ tailWord_3720860) baseStart_3720860 baseEnd_3720860 := by
    simpa [prefixWord, tailWord_3720860, baseEnd_3720860] using wordTrace_append hprefix tailTrace_3720860
  have hstable : (prefixWord ++ tailWord_3720860).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3720860).length < 2 ^ (prefixWord ++ tailWord_3720860).sum := by decide
  have hdescent : baseEnd_3720860 < baseStart_3720860 := by decide
  rcases family_descends (prefixWord ++ tailWord_3720860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3720877 : List Nat := [1, 5, 2, 1, 1, 1, 4, 3, 1, 3]
def baseStart_3720877 : Nat := 118140960795 + 3720877 * 2 ^ 59
def prefixEnd_3720877 : Nat := 4983230072969 + 3 ^ 40 * 3720877 * 2
def baseEnd_3720877 : Nat := 1273732238173029190217003

theorem tailTrace_3720877 : CollatzResearch.WordTrace tailWord_3720877 prefixEnd_3720877 1273732238173029190217003 := by
  unfold tailWord_3720877
  simp only [CollatzResearch.WordTrace]
  refine ⟨135711533340905579043944885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90474355560603719362629923 135711533340905579043944885)
  ·
    refine ⟨12722956250709898035369833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 135711533340905579043944885 12722956250709898035369833)
    ·
      refine ⟨9542217188032423526527375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12722956250709898035369833 9542217188032423526527375)
      ·
        refine ⟨14313325782048635289791063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9542217188032423526527375 14313325782048635289791063)
        ·
          refine ⟨21469988673072952934686595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14313325782048635289791063 21469988673072952934686595)
          ·
            refine ⟨32204983009609429402029893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21469988673072952934686595 32204983009609429402029893)
            ·
              refine ⟨6038434314301768012880605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32204983009609429402029893 6038434314301768012880605)
              ·
                refine ⟨2264412867863163004830227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6038434314301768012880605 2264412867863163004830227)
                ·
                  refine ⟨3396619301794744507245341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2264412867863163004830227 3396619301794744507245341)
                  ·
                    refine ⟨1273732238173029190217003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3396619301794744507245341 1273732238173029190217003)
                    ·
                      rfl

theorem cell22_3720877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 4, 3, 1, 3].length) (baseStart_3720877 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3720877 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3720877 prefixEnd_3720877 := by exact prefixLift 3720877
  have htrace : WordTrace (prefixWord ++ tailWord_3720877) baseStart_3720877 baseEnd_3720877 := by
    simpa [prefixWord, tailWord_3720877, baseEnd_3720877] using wordTrace_append hprefix tailTrace_3720877
  have hstable : (prefixWord ++ tailWord_3720877).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3720877).length < 2 ^ (prefixWord ++ tailWord_3720877).sum := by decide
  have hdescent : baseEnd_3720877 < baseStart_3720877 := by decide
  rcases family_descends (prefixWord ++ tailWord_3720877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3720933 : List Nat := [1, 3, 1, 4, 1, 1, 1, 1, 6, 3]
def baseStart_3720933 : Nat := 118140960795 + 3720933 * 2 ^ 59
def prefixEnd_3720933 : Nat := 4983230072969 + 3 ^ 40 * 3720933 * 2
def baseEnd_3720933 : Nat := 1273751408117463710816831

theorem tailTrace_3720933 : CollatzResearch.WordTrace tailWord_3720933 prefixEnd_3720933 1273751408117463710816831 := by
  unfold tailWord_3720933
  simp only [CollatzResearch.WordTrace]
  refine ⟨135713575828702700607983453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90475717219135133738655635 135713575828702700607983453)
  ·
    refine ⟨50892590935763512727993795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135713575828702700607983453 50892590935763512727993795)
    ·
      refine ⟨76338886403645269091990693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50892590935763512727993795 76338886403645269091990693)
      ·
        refine ⟨14313541200683487954748255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 76338886403645269091990693 14313541200683487954748255)
        ·
          refine ⟨21470311801025231932122383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14313541200683487954748255 21470311801025231932122383)
          ·
            refine ⟨32205467701537847898183575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21470311801025231932122383 32205467701537847898183575)
            ·
              refine ⟨48308201552306771847275363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32205467701537847898183575 48308201552306771847275363)
              ·
                refine ⟨72462302328460157770913045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48308201552306771847275363 72462302328460157770913045)
                ·
                  refine ⟨3396670421646569895511549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 72462302328460157770913045 3396670421646569895511549)
                  ·
                    refine ⟨1273751408117463710816831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3396670421646569895511549 1273751408117463710816831)
                    ·
                      rfl

theorem cell22_3720933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 1, 6, 3].length) (baseStart_3720933 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3720933 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3720933 prefixEnd_3720933 := by exact prefixLift 3720933
  have htrace : WordTrace (prefixWord ++ tailWord_3720933) baseStart_3720933 baseEnd_3720933 := by
    simpa [prefixWord, tailWord_3720933, baseEnd_3720933] using wordTrace_append hprefix tailTrace_3720933
  have hstable : (prefixWord ++ tailWord_3720933).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3720933).length < 2 ^ (prefixWord ++ tailWord_3720933).sum := by decide
  have hdescent : baseEnd_3720933 < baseStart_3720933 := by decide
  rcases family_descends (prefixWord ++ tailWord_3720933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3720950 : List Nat := [5, 1, 1, 1, 1, 3, 2, 1, 4, 3]
def baseStart_3720950 : Nat := 118140960795 + 3720950 * 2 ^ 59
def prefixEnd_3720950 : Nat := 4983230072969 + 3 ^ 40 * 3720950 * 2
def baseEnd_3720950 : Nat := 1273757227564881333141779

theorem tailTrace_3720950 : CollatzResearch.WordTrace tailWord_3720950 prefixEnd_3720950 1273757227564881333141779 := by
  unfold tailWord_3720950
  simp only [CollatzResearch.WordTrace]
  refine ⟨8482137241852569531959519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 90476130579760741674234869 8482137241852569531959519)
  ·
    refine ⟨12723205862778854297939279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8482137241852569531959519 12723205862778854297939279)
    ·
      refine ⟨19084808794168281446908919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12723205862778854297939279 19084808794168281446908919)
      ·
        refine ⟨28627213191252422170363379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19084808794168281446908919 28627213191252422170363379)
        ·
          refine ⟨42940819786878633255545069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28627213191252422170363379 42940819786878633255545069)
          ·
            refine ⟨16102807420079487470829401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42940819786878633255545069 16102807420079487470829401)
            ·
              refine ⟨12077105565059615603122051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16102807420079487470829401 12077105565059615603122051)
              ·
                refine ⟨18115658347589423404683077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12077105565059615603122051 18115658347589423404683077)
                ·
                  refine ⟨3396685940173016888378077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18115658347589423404683077 3396685940173016888378077)
                  ·
                    refine ⟨1273757227564881333141779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3396685940173016888378077 1273757227564881333141779)
                    ·
                      rfl

theorem cell22_3720950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 2, 1, 4, 3].length) (baseStart_3720950 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3720950 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3720950 prefixEnd_3720950 := by exact prefixLift 3720950
  have htrace : WordTrace (prefixWord ++ tailWord_3720950) baseStart_3720950 baseEnd_3720950 := by
    simpa [prefixWord, tailWord_3720950, baseEnd_3720950] using wordTrace_append hprefix tailTrace_3720950
  have hstable : (prefixWord ++ tailWord_3720950).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3720950).length < 2 ^ (prefixWord ++ tailWord_3720950).sum := by decide
  have hdescent : baseEnd_3720950 < baseStart_3720950 := by decide
  rcases family_descends (prefixWord ++ tailWord_3720950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3720967 : List Nat := [1, 1, 4, 4, 2, 1, 1, 3, 2, 3]
def baseStart_3720967 : Nat := 118140960795 + 3720967 * 2 ^ 59
def prefixEnd_3720967 : Nat := 4983230072969 + 3 ^ 40 * 3720967 * 2
def baseEnd_3720967 : Nat := 1273763047012298955466727

theorem tailTrace_3720967 : CollatzResearch.WordTrace tailWord_3720967 prefixEnd_3720967 1273763047012298955466727 := by
  unfold tailWord_3720967
  simp only [CollatzResearch.WordTrace]
  refine ⟨135714815910579524414721155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90476543940386349609814103 135714815910579524414721155)
  ·
    refine ⟨203572223865869286622081733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135714815910579524414721155 203572223865869286622081733)
    ·
      refine ⟨38169791974850491241640325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 203572223865869286622081733 38169791974850491241640325)
      ·
        refine ⟨7156835995284467107807561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38169791974850491241640325 7156835995284467107807561)
        ·
          refine ⟨5367626996463350330855671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7156835995284467107807561 5367626996463350330855671)
          ·
            refine ⟨8051440494695025496283507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5367626996463350330855671 8051440494695025496283507)
            ·
              refine ⟨12077160742042538244425261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8051440494695025496283507 12077160742042538244425261)
              ·
                refine ⟨4528935278265951841659473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12077160742042538244425261 4528935278265951841659473)
                ·
                  refine ⟨3396701458699463881244605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4528935278265951841659473 3396701458699463881244605)
                  ·
                    refine ⟨1273763047012298955466727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3396701458699463881244605 1273763047012298955466727)
                    ·
                      rfl

theorem cell22_3720967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 1, 3, 2, 3].length) (baseStart_3720967 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3720967 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3720967 prefixEnd_3720967 := by exact prefixLift 3720967
  have htrace : WordTrace (prefixWord ++ tailWord_3720967) baseStart_3720967 baseEnd_3720967 := by
    simpa [prefixWord, tailWord_3720967, baseEnd_3720967] using wordTrace_append hprefix tailTrace_3720967
  have hstable : (prefixWord ++ tailWord_3720967).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3720967).length < 2 ^ (prefixWord ++ tailWord_3720967).sum := by decide
  have hdescent : baseEnd_3720967 < baseStart_3720967 := by decide
  rcases family_descends (prefixWord ++ tailWord_3720967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3721055 : List Nat := [1, 1, 2, 3, 1, 5, 1, 3, 1, 4]
def baseStart_3721055 : Nat := 118140960795 + 3721055 * 2 ^ 59
def prefixEnd_3721055 : Nat := 4983230072969 + 3 ^ 40 * 3721055 * 2
def baseEnd_3721055 : Nat := 1273793171210696059266457

theorem tailTrace_3721055 : CollatzResearch.WordTrace tailWord_3721055 prefixEnd_3721055 1273793171210696059266457 := by
  unfold tailWord_3721055
  simp only [CollatzResearch.WordTrace]
  refine ⟨135718025534260715443924619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90478683689507143629283079 135718025534260715443924619)
  ·
    refine ⟨203577038301391073165886929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135718025534260715443924619 203577038301391073165886929)
    ·
      refine ⟨152682778726043304874415197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 203577038301391073165886929 152682778726043304874415197)
      ·
        refine ⟨57256042022266239327905699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 152682778726043304874415197 57256042022266239327905699)
        ·
          refine ⟨85884063033399358991858549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57256042022266239327905699 85884063033399358991858549)
          ·
            refine ⟨8051630909381189905486739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 85884063033399358991858549 8051630909381189905486739)
            ·
              refine ⟨12077446364071784858230109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8051630909381189905486739 12077446364071784858230109)
              ·
                refine ⟨4529042386526919321836291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12077446364071784858230109 4529042386526919321836291)
                ·
                  refine ⟨6793563579790378982754437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4529042386526919321836291 6793563579790378982754437)
                  ·
                    refine ⟨1273793171210696059266457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6793563579790378982754437 1273793171210696059266457)
                    ·
                      rfl

theorem cell22_3721055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 1, 3, 1, 4].length) (baseStart_3721055 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3721055 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3721055 prefixEnd_3721055 := by exact prefixLift 3721055
  have htrace : WordTrace (prefixWord ++ tailWord_3721055) baseStart_3721055 baseEnd_3721055 := by
    simpa [prefixWord, tailWord_3721055, baseEnd_3721055] using wordTrace_append hprefix tailTrace_3721055
  have hstable : (prefixWord ++ tailWord_3721055).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3721055).length < 2 ^ (prefixWord ++ tailWord_3721055).sum := by decide
  have hdescent : baseEnd_3721055 < baseStart_3721055 := by decide
  rcases family_descends (prefixWord ++ tailWord_3721055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3721070 : List Nat := [4, 1, 2, 3, 1, 1, 1, 3, 6]
def baseStart_3721070 : Nat := 118140960795 + 3721070 * 2 ^ 59
def prefixEnd_3721070 : Nat := 4983230072969 + 3 ^ 40 * 3721070 * 2
def baseEnd_3721070 : Nat := 424599435339080340047137

theorem tailTrace_3721070 : CollatzResearch.WordTrace tailWord_3721070 prefixEnd_3721070 424599435339080340047137 := by
  unfold tailWord_3721070
  simp only [CollatzResearch.WordTrace]
  refine ⟨16964821578650796625715083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 90479048419470915337147109 16964821578650796625715083)
  ·
    refine ⟨25447232367976194938572625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16964821578650796625715083 25447232367976194938572625)
    ·
      refine ⟨19085424275982146203929469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25447232367976194938572625 19085424275982146203929469)
      ·
        refine ⟨7157034103493304826473551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19085424275982146203929469 7157034103493304826473551)
        ·
          refine ⟨10735551155239957239710327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7157034103493304826473551 10735551155239957239710327)
          ·
            refine ⟨16103326732859935859565491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10735551155239957239710327 16103326732859935859565491)
            ·
              refine ⟨24154990099289903789348237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16103326732859935859565491 24154990099289903789348237)
              ·
                refine ⟨9058121287233713921005589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24154990099289903789348237 9058121287233713921005589)
                ·
                  refine ⟨424599435339080340047137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9058121287233713921005589 424599435339080340047137)
                  ·
                    rfl

theorem cell22_3721070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 1, 3, 6].length) (baseStart_3721070 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3721070 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3721070 prefixEnd_3721070 := by exact prefixLift 3721070
  have htrace : WordTrace (prefixWord ++ tailWord_3721070) baseStart_3721070 baseEnd_3721070 := by
    simpa [prefixWord, tailWord_3721070, baseEnd_3721070] using wordTrace_append hprefix tailTrace_3721070
  have hstable : (prefixWord ++ tailWord_3721070).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3721070).length < 2 ^ (prefixWord ++ tailWord_3721070).sum := by decide
  have hdescent : baseEnd_3721070 < baseStart_3721070 := by decide
  rcases family_descends (prefixWord ++ tailWord_3721070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3721089 : List Nat := [1, 2, 4, 4, 1, 1, 2, 2, 1, 4]
def baseStart_3721089 : Nat := 118140960795 + 3721089 * 2 ^ 59
def prefixEnd_3721089 : Nat := 4983230072969 + 3 ^ 40 * 3721089 * 2
def baseEnd_3721089 : Nat := 1273804810105531303916353

theorem tailTrace_3721089 : CollatzResearch.WordTrace tailWord_3721089 prefixEnd_3721089 1273804810105531303916353 := by
  unfold tailWord_3721089
  simp only [CollatzResearch.WordTrace]
  refine ⟨135719265616137539250662321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90479510410758359500441547 135719265616137539250662321)
  ·
    refine ⟨101789449212103154437996741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135719265616137539250662321 101789449212103154437996741)
    ·
      refine ⟨19085521727269341457124389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 101789449212103154437996741 19085521727269341457124389)
      ·
        refine ⟨3578535323863001523210823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19085521727269341457124389 3578535323863001523210823)
        ·
          refine ⟨5367802985794502284816235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3578535323863001523210823 5367802985794502284816235)
          ·
            refine ⟨8051704478691753427224353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5367802985794502284816235 8051704478691753427224353)
            ·
              refine ⟨6038778359018815070418265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8051704478691753427224353 6038778359018815070418265)
              ·
                refine ⟨4529083769264111302813699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6038778359018815070418265 4529083769264111302813699)
                ·
                  refine ⟨6793625653896166954220549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4529083769264111302813699 6793625653896166954220549)
                  ·
                    refine ⟨1273804810105531303916353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6793625653896166954220549 1273804810105531303916353)
                    ·
                      rfl

theorem cell22_3721089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 2, 2, 1, 4].length) (baseStart_3721089 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3721089 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3721089 prefixEnd_3721089 := by exact prefixLift 3721089
  have htrace : WordTrace (prefixWord ++ tailWord_3721089) baseStart_3721089 baseEnd_3721089 := by
    simpa [prefixWord, tailWord_3721089, baseEnd_3721089] using wordTrace_append hprefix tailTrace_3721089
  have hstable : (prefixWord ++ tailWord_3721089).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3721089).length < 2 ^ (prefixWord ++ tailWord_3721089).sum := by decide
  have hdescent : baseEnd_3721089 < baseStart_3721089 := by decide
  rcases family_descends (prefixWord ++ tailWord_3721089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3721177 : List Nat := [1, 2, 1, 2, 6, 1, 2, 2, 5]
def baseStart_3721177 : Nat := 118140960795 + 3721177 * 2 ^ 59
def prefixEnd_3721177 : Nat := 4983230072969 + 3 ^ 40 * 3721177 * 2
def baseEnd_3721177 : Nat := 424611644767976135905361

theorem tailTrace_3721177 : CollatzResearch.WordTrace tailWord_3721177 prefixEnd_3721177 424611644767976135905361 := by
  unfold tailWord_3721177
  simp only [CollatzResearch.WordTrace]
  refine ⟨135722475239818730279865785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90481650159879153519910523 135722475239818730279865785)
  ·
    refine ⟨101791856429864047709899339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135722475239818730279865785 101791856429864047709899339)
    ·
      refine ⟨152687784644796071564849009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101791856429864047709899339 152687784644796071564849009)
      ·
        refine ⟨114515838483597053673636757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152687784644796071564849009 114515838483597053673636757)
        ·
          refine ⟨5367929928918611890951723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 114515838483597053673636757 5367929928918611890951723)
          ·
            refine ⟨8051894893377917836427585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5367929928918611890951723 8051894893377917836427585)
            ·
              refine ⟨6038921170033438377320689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8051894893377917836427585 6038921170033438377320689)
              ·
                refine ⟨4529190877525078782990517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6038921170033438377320689 4529190877525078782990517)
                ·
                  refine ⟨424611644767976135905361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4529190877525078782990517 424611644767976135905361)
                  ·
                    rfl

theorem cell22_3721177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 2, 2, 5].length) (baseStart_3721177 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3721177 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3721177 prefixEnd_3721177 := by exact prefixLift 3721177
  have htrace : WordTrace (prefixWord ++ tailWord_3721177) baseStart_3721177 baseEnd_3721177 := by
    simpa [prefixWord, tailWord_3721177, baseEnd_3721177] using wordTrace_append hprefix tailTrace_3721177
  have hstable : (prefixWord ++ tailWord_3721177).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3721177).length < 2 ^ (prefixWord ++ tailWord_3721177).sum := by decide
  have hdescent : baseEnd_3721177 < baseStart_3721177 := by decide
  rcases family_descends (prefixWord ++ tailWord_3721177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3721181 : List Nat := [1, 4, 3, 1, 3, 1, 1, 4, 1, 3]
def baseStart_3721181 : Nat := 118140960795 + 3721181 * 2 ^ 59
def prefixEnd_3721181 : Nat := 4983230072969 + 3 ^ 40 * 3721181 * 2
def baseEnd_3721181 : Nat := 1273836303585673730616071

theorem tailTrace_3721181 : CollatzResearch.WordTrace tailWord_3721181 prefixEnd_3721181 1273836303585673730616071 := by
  unfold tailWord_3721181
  simp only [CollatzResearch.WordTrace]
  refine ⟨135722621131804238963011397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90481747421202825975340931 135722621131804238963011397)
  ·
    refine ⟨25447991462213294805564637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 135722621131804238963011397 25447991462213294805564637)
    ·
      refine ⟨9542996798329985552086739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25447991462213294805564637 9542996798329985552086739)
      ·
        refine ⟨14314495197494978328130109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9542996798329985552086739 14314495197494978328130109)
        ·
          refine ⟨5367935699060616873048791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14314495197494978328130109 5367935699060616873048791)
          ·
            refine ⟨8051903548590925309573187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5367935699060616873048791 8051903548590925309573187)
            ·
              refine ⟨12077855322886387964359781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8051903548590925309573187 12077855322886387964359781)
              ·
                refine ⟨2264597873041197743317459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12077855322886387964359781 2264597873041197743317459)
                ·
                  refine ⟨3396896809561796614976189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2264597873041197743317459 3396896809561796614976189)
                  ·
                    refine ⟨1273836303585673730616071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3396896809561796614976189 1273836303585673730616071)
                    ·
                      rfl

theorem cell22_3721181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 1, 4, 1, 3].length) (baseStart_3721181 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3721181 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3721181 prefixEnd_3721181 := by exact prefixLift 3721181
  have htrace : WordTrace (prefixWord ++ tailWord_3721181) baseStart_3721181 baseEnd_3721181 := by
    simpa [prefixWord, tailWord_3721181, baseEnd_3721181] using wordTrace_append hprefix tailTrace_3721181
  have hstable : (prefixWord ++ tailWord_3721181).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3721181).length < 2 ^ (prefixWord ++ tailWord_3721181).sum := by decide
  have hdescent : baseEnd_3721181 < baseStart_3721181 := by decide
  rcases family_descends (prefixWord ++ tailWord_3721181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3721235 : List Nat := [1, 1, 1, 2, 1, 4, 2, 4, 2, 4]
def baseStart_3721235 : Nat := 118140960795 + 3721235 * 2 ^ 59
def prefixEnd_3721235 : Nat := 4983230072969 + 3 ^ 40 * 3721235 * 2
def baseEnd_3721235 : Nat := 1273854788889235589765905

theorem tailTrace_3721235 : CollatzResearch.WordTrace tailWord_3721235 prefixEnd_3721235 1273854788889235589765905 := by
  unfold tailWord_3721235
  simp only [CollatzResearch.WordTrace]
  refine ⟨135724590673608606185477159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90483060449072404123651439 135724590673608606185477159)
  ·
    refine ⟨203586886010412909278215739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135724590673608606185477159 203586886010412909278215739)
    ·
      refine ⟨305380329015619363917323609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203586886010412909278215739 305380329015619363917323609)
      ·
        refine ⟨229035246761714522937992707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 305380329015619363917323609 229035246761714522937992707)
        ·
          refine ⟨343552870142571784406989061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 229035246761714522937992707 343552870142571784406989061)
          ·
            refine ⟨64416163151732209576310449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 343552870142571784406989061 64416163151732209576310449)
            ·
              refine ⟨48312122363799157182232837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64416163151732209576310449 48312122363799157182232837)
              ·
                refine ⟨9058522943212341971668657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48312122363799157182232837 9058522943212341971668657)
                ·
                  refine ⟨6793892207409256478751493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9058522943212341971668657 6793892207409256478751493)
                  ·
                    refine ⟨1273854788889235589765905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6793892207409256478751493 1273854788889235589765905)
                    ·
                      rfl

theorem cell22_3721235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 4, 2, 4].length) (baseStart_3721235 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3721235 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3721235 prefixEnd_3721235 := by exact prefixLift 3721235
  have htrace : WordTrace (prefixWord ++ tailWord_3721235) baseStart_3721235 baseEnd_3721235 := by
    simpa [prefixWord, tailWord_3721235, baseEnd_3721235] using wordTrace_append hprefix tailTrace_3721235
  have hstable : (prefixWord ++ tailWord_3721235).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3721235).length < 2 ^ (prefixWord ++ tailWord_3721235).sum := by decide
  have hdescent : baseEnd_3721235 < baseStart_3721235 := by decide
  rcases family_descends (prefixWord ++ tailWord_3721235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3721250 : List Nat := [3, 3, 1, 1, 1, 2, 2, 9]
def baseStart_3721250 : Nat := 118140960795 + 3721250 * 2 ^ 59
def prefixEnd_3721250 : Nat := 4983230072969 + 3 ^ 40 * 3721250 * 2
def baseEnd_3721250 : Nat := 141539991521753394515651

theorem tailTrace_3721250 : CollatzResearch.WordTrace tailWord_3721250 prefixEnd_3721250 141539991521753394515651 := by
  unfold tailWord_3721250
  simp only [CollatzResearch.WordTrace]
  refine ⟨33931284442138565936818301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90483425179036175831515469 33931284442138565936818301)
  ·
    refine ⟨12724231665801962226306863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33931284442138565936818301 12724231665801962226306863)
    ·
      refine ⟨19086347498702943339460295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12724231665801962226306863 19086347498702943339460295)
      ·
        refine ⟨28629521248054415009190443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19086347498702943339460295 28629521248054415009190443)
        ·
          refine ⟨42944281872081622513785665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28629521248054415009190443 42944281872081622513785665)
          ·
            refine ⟨32208211404061216885339249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42944281872081622513785665 32208211404061216885339249)
            ·
              refine ⟨24156158553045912664004437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32208211404061216885339249 24156158553045912664004437)
              ·
                refine ⟨141539991521753394515651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 24156158553045912664004437 141539991521753394515651)
                ·
                  rfl

theorem cell22_3721250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 2, 9].length) (baseStart_3721250 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3721250 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3721250 prefixEnd_3721250 := by exact prefixLift 3721250
  have htrace : WordTrace (prefixWord ++ tailWord_3721250) baseStart_3721250 baseEnd_3721250 := by
    simpa [prefixWord, tailWord_3721250, baseEnd_3721250] using wordTrace_append hprefix tailTrace_3721250
  have hstable : (prefixWord ++ tailWord_3721250).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3721250).length < 2 ^ (prefixWord ++ tailWord_3721250).sum := by decide
  have hdescent : baseEnd_3721250 < baseStart_3721250 := by decide
  rcases family_descends (prefixWord ++ tailWord_3721250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3721312 : List Nat := [2, 1, 1, 3, 2, 4, 1, 3, 5]
def baseStart_3721312 : Nat := 118140960795 + 3721312 * 2 ^ 59
def prefixEnd_3721312 : Nat := 4983230072969 + 3 ^ 40 * 3721312 * 2
def baseEnd_3721312 : Nat := 424627049187611018530223

theorem tailTrace_3721312 : CollatzResearch.WordTrace tailWord_3721312 prefixEnd_3721312 424627049187611018530223 := by
  unfold tailWord_3721312
  simp only [CollatzResearch.WordTrace]
  refine ⟨67863699547164824168015095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90484932729553098890686793 67863699547164824168015095)
  ·
    refine ⟨101795549320747236252022643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67863699547164824168015095 101795549320747236252022643)
    ·
      refine ⟨152693323981120854378033965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101795549320747236252022643 152693323981120854378033965)
      ·
        refine ⟨57259996492920320391762737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 152693323981120854378033965 57259996492920320391762737)
        ·
          refine ⟨42944997369690240293822053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57259996492920320391762737 42944997369690240293822053)
          ·
            refine ⟨8052187006816920055091635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42944997369690240293822053 8052187006816920055091635)
            ·
              refine ⟨12078280510225380082637453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8052187006816920055091635 12078280510225380082637453)
              ·
                refine ⟨4529355191334517530989045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12078280510225380082637453 4529355191334517530989045)
                ·
                  refine ⟨424627049187611018530223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4529355191334517530989045 424627049187611018530223)
                  ·
                    rfl

theorem cell22_3721312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 1, 3, 5].length) (baseStart_3721312 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3721312 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3721312 prefixEnd_3721312 := by exact prefixLift 3721312
  have htrace : WordTrace (prefixWord ++ tailWord_3721312) baseStart_3721312 baseEnd_3721312 := by
    simpa [prefixWord, tailWord_3721312, baseEnd_3721312] using wordTrace_append hprefix tailTrace_3721312
  have hstable : (prefixWord ++ tailWord_3721312).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3721312).length < 2 ^ (prefixWord ++ tailWord_3721312).sum := by decide
  have hdescent : baseEnd_3721312 < baseStart_3721312 := by decide
  rcases family_descends (prefixWord ++ tailWord_3721312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3721389 : List Nat := [1, 5, 2, 1, 2, 1, 2, 2, 1, 5]
def baseStart_3721389 : Nat := 118140960795 + 3721389 * 2 ^ 59
def prefixEnd_3721389 : Nat := 4983230072969 + 3 ^ 40 * 3721389 * 2
def baseEnd_3721389 : Nat := 1273907506236430521415433

theorem tailTrace_3721389 : CollatzResearch.WordTrace tailWord_3721389 prefixEnd_3721389 1273907506236430521415433 := by
  unfold tailWord_3721389
  simp only [CollatzResearch.WordTrace]
  refine ⟨135730207515050690486583221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90486805010033793657722147 135730207515050690486583221)
  ·
    refine ⟨12724706954536002233117177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 135730207515050690486583221 12724706954536002233117177)
    ·
      refine ⟨9543530215902001674837883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12724706954536002233117177 9543530215902001674837883)
      ·
        refine ⟨14315295323853002512256825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9543530215902001674837883 14315295323853002512256825)
        ·
          refine ⟨10736471492889751884192619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14315295323853002512256825 10736471492889751884192619)
          ·
            refine ⟨16104707239334627826288929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10736471492889751884192619 16104707239334627826288929)
            ·
              refine ⟨12078530429500970869716697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16104707239334627826288929 12078530429500970869716697)
              ·
                refine ⟨9058897822125728152287523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12078530429500970869716697 9058897822125728152287523)
                ·
                  refine ⟨13588346733188592228431285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9058897822125728152287523 13588346733188592228431285)
                  ·
                    refine ⟨1273907506236430521415433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13588346733188592228431285 1273907506236430521415433)
                    ·
                      rfl

theorem cell22_3721389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 2, 2, 1, 5].length) (baseStart_3721389 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3721389 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3721389 prefixEnd_3721389 := by exact prefixLift 3721389
  have htrace : WordTrace (prefixWord ++ tailWord_3721389) baseStart_3721389 baseEnd_3721389 := by
    simpa [prefixWord, tailWord_3721389, baseEnd_3721389] using wordTrace_append hprefix tailTrace_3721389
  have hstable : (prefixWord ++ tailWord_3721389).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3721389).length < 2 ^ (prefixWord ++ tailWord_3721389).sum := by decide
  have hdescent : baseEnd_3721389 < baseStart_3721389 := by decide
  rcases family_descends (prefixWord ++ tailWord_3721389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3721393 : List Nat := [1, 2, 2, 5, 2, 2, 2, 1, 1, 4]
def baseStart_3721393 : Nat := 118140960795 + 3721393 * 2 ^ 59
def prefixEnd_3721393 : Nat := 4983230072969 + 3 ^ 40 * 3721393 * 2
def baseEnd_3721393 : Nat := 1273908875518175844315421

theorem tailTrace_3721393 : CollatzResearch.WordTrace tailWord_3721393 prefixEnd_3721393 1273908875518175844315421 := by
  unfold tailWord_3721393
  simp only [CollatzResearch.WordTrace]
  refine ⟨135730353407036199169728833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90486902271357466113152555 135730353407036199169728833)
  ·
    refine ⟨101797765055277149377296625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135730353407036199169728833 101797765055277149377296625)
    ·
      refine ⟨76348323791457862032972469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101797765055277149377296625 76348323791457862032972469)
      ·
        refine ⟨7157655355449174565591169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 76348323791457862032972469 7157655355449174565591169)
        ·
          refine ⟨5368241516586880924193377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7157655355449174565591169 5368241516586880924193377)
          ·
            refine ⟨4026181137440160693145033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5368241516586880924193377 4026181137440160693145033)
            ·
              refine ⟨3019635853080120519858775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4026181137440160693145033 3019635853080120519858775)
              ·
                refine ⟨4529453779620180779788163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3019635853080120519858775 4529453779620180779788163)
                ·
                  refine ⟨6794180669430271169682245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4529453779620180779788163 6794180669430271169682245)
                  ·
                    refine ⟨1273908875518175844315421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6794180669430271169682245 1273908875518175844315421)
                    ·
                      rfl

theorem cell22_3721393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 2, 2, 1, 1, 4].length) (baseStart_3721393 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3721393 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3721393 prefixEnd_3721393 := by exact prefixLift 3721393
  have htrace : WordTrace (prefixWord ++ tailWord_3721393) baseStart_3721393 baseEnd_3721393 := by
    simpa [prefixWord, tailWord_3721393, baseEnd_3721393] using wordTrace_append hprefix tailTrace_3721393
  have hstable : (prefixWord ++ tailWord_3721393).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3721393).length < 2 ^ (prefixWord ++ tailWord_3721393).sum := by decide
  have hdescent : baseEnd_3721393 < baseStart_3721393 := by decide
  rcases family_descends (prefixWord ++ tailWord_3721393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3721406 : List Nat := [4, 2, 1, 1, 4, 1, 1, 1, 4, 3]
def baseStart_3721406 : Nat := 118140960795 + 3721406 * 2 ^ 59
def prefixEnd_3721406 : Nat := 4983230072969 + 3 ^ 40 * 3721406 * 2
def baseEnd_3721406 : Nat := 1273913325683848143740381

theorem tailTrace_3721406 : CollatzResearch.WordTrace tailWord_3721406 prefixEnd_3721406 1273913325683848143740381 := by
  unfold tailWord_3721406
  simp only [CollatzResearch.WordTrace]
  refine ⟨16966353444498637798744009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 90487218370659401593301381 16966353444498637798744009)
  ·
    refine ⟨12724765083373978349058007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16966353444498637798744009 12724765083373978349058007)
    ·
      refine ⟨19087147625060967523587011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12724765083373978349058007 19087147625060967523587011)
      ·
        refine ⟨28630721437591451285380517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19087147625060967523587011 28630721437591451285380517)
        ·
          refine ⟨5368260269548397116008847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28630721437591451285380517 5368260269548397116008847)
          ·
            refine ⟨8052390404322595674013271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5368260269548397116008847 8052390404322595674013271)
            ·
              refine ⟨12078585606483893511019907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8052390404322595674013271 12078585606483893511019907)
              ·
                refine ⟨18117878409725840266529861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12078585606483893511019907 18117878409725840266529861)
                ·
                  refine ⟨3397102201823595049974349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18117878409725840266529861 3397102201823595049974349)
                  ·
                    refine ⟨1273913325683848143740381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3397102201823595049974349 1273913325683848143740381)
                    ·
                      rfl

theorem cell22_3721406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 1, 1, 4, 3].length) (baseStart_3721406 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3721406 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3721406 prefixEnd_3721406 := by exact prefixLift 3721406
  have htrace : WordTrace (prefixWord ++ tailWord_3721406) baseStart_3721406 baseEnd_3721406 := by
    simpa [prefixWord, tailWord_3721406, baseEnd_3721406] using wordTrace_append hprefix tailTrace_3721406
  have hstable : (prefixWord ++ tailWord_3721406).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3721406).length < 2 ^ (prefixWord ++ tailWord_3721406).sum := by decide
  have hdescent : baseEnd_3721406 < baseStart_3721406 := by decide
  rcases family_descends (prefixWord ++ tailWord_3721406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3721434 : List Nat := [3, 1, 1, 2, 2, 1, 4, 2, 3, 3]
def baseStart_3721434 : Nat := 118140960795 + 3721434 * 2 ^ 59
def prefixEnd_3721434 : Nat := 4983230072969 + 3 ^ 40 * 3721434 * 2
def baseEnd_3721434 : Nat := 1273922910656065404040295

theorem tailTrace_3721434 : CollatzResearch.WordTrace tailWord_3721434 prefixEnd_3721434 1273922910656065404040295 := by
  unfold tailWord_3721434
  simp only [CollatzResearch.WordTrace]
  refine ⟨33932962199971915792992839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90487899199925108781314237 33932962199971915792992839)
  ·
    refine ⟨50899443299957873689489259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33932962199971915792992839 50899443299957873689489259)
    ·
      refine ⟨76349164949936810534233889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50899443299957873689489259 76349164949936810534233889)
      ·
        refine ⟨57261873712452607900675417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76349164949936810534233889 57261873712452607900675417)
        ·
          refine ⟨42946405284339455925506563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57261873712452607900675417 42946405284339455925506563)
          ·
            refine ⟨64419607926509183888259845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42946405284339455925506563 64419607926509183888259845)
            ·
              refine ⟨12078676486220471979048721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 64419607926509183888259845 12078676486220471979048721)
              ·
                refine ⟨9059007364665353984286541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12078676486220471979048721 9059007364665353984286541)
                ·
                  refine ⟨3397127761749507744107453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9059007364665353984286541 3397127761749507744107453)
                  ·
                    refine ⟨1273922910656065404040295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3397127761749507744107453 1273922910656065404040295)
                    ·
                      rfl

theorem cell22_3721434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 4, 2, 3, 3].length) (baseStart_3721434 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3721434 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3721434 prefixEnd_3721434 := by exact prefixLift 3721434
  have htrace : WordTrace (prefixWord ++ tailWord_3721434) baseStart_3721434 baseEnd_3721434 := by
    simpa [prefixWord, tailWord_3721434, baseEnd_3721434] using wordTrace_append hprefix tailTrace_3721434
  have hstable : (prefixWord ++ tailWord_3721434).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3721434).length < 2 ^ (prefixWord ++ tailWord_3721434).sum := by decide
  have hdescent : baseEnd_3721434 < baseStart_3721434 := by decide
  rcases family_descends (prefixWord ++ tailWord_3721434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3721436 : List Nat := [2, 2, 5, 2, 1, 1, 1, 8]
def baseStart_3721436 : Nat := 118140960795 + 3721436 * 2 ^ 59
def prefixEnd_3721436 : Nat := 4983230072969 + 3 ^ 40 * 3721436 * 2
def baseEnd_3721436 : Nat := 141547066144104229498921

theorem tailTrace_3721436 : CollatzResearch.WordTrace tailWord_3721436 prefixEnd_3721436 141547066144104229498921 := by
  unfold tailWord_3721436
  simp only [CollatzResearch.WordTrace]
  refine ⟨67865960872940208756772081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90487947830586945009029441 67865960872940208756772081)
  ·
    refine ⟨50899470654705156567579061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67865960872940208756772081 50899470654705156567579061)
    ·
      refine ⟨4771825373878608428210537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 50899470654705156567579061 4771825373878608428210537)
      ·
        refine ⟨3578869030408956321157903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4771825373878608428210537 3578869030408956321157903)
        ·
          refine ⟨5368303545613434481736855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3578869030408956321157903 5368303545613434481736855)
          ·
            refine ⟨8052455318420151722605283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5368303545613434481736855 8052455318420151722605283)
            ·
              refine ⟨12078682977630227583907925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8052455318420151722605283 12078682977630227583907925)
              ·
                refine ⟨141547066144104229498921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12078682977630227583907925 141547066144104229498921)
                ·
                  rfl

theorem cell22_3721436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 1, 8].length) (baseStart_3721436 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3721436 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3721436 prefixEnd_3721436 := by exact prefixLift 3721436
  have htrace : WordTrace (prefixWord ++ tailWord_3721436) baseStart_3721436 baseEnd_3721436 := by
    simpa [prefixWord, tailWord_3721436, baseEnd_3721436] using wordTrace_append hprefix tailTrace_3721436
  have hstable : (prefixWord ++ tailWord_3721436).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3721436).length < 2 ^ (prefixWord ++ tailWord_3721436).sum := by decide
  have hdescent : baseEnd_3721436 < baseStart_3721436 := by decide
  rcases family_descends (prefixWord ++ tailWord_3721436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3721442 : List Nat := [3, 3, 4, 1, 1, 2, 1, 3, 4]
def baseStart_3721442 : Nat := 118140960795 + 3721442 * 2 ^ 59
def prefixEnd_3721442 : Nat := 4983230072969 + 3 ^ 40 * 3721442 * 2
def baseEnd_3721442 : Nat := 424641883073185349946757

theorem tailTrace_3721442 : CollatzResearch.WordTrace tailWord_3721442 prefixEnd_3721442 424641883073185349946757 := by
  unfold tailWord_3721442
  simp only [CollatzResearch.WordTrace]
  refine ⟨33933035145964670134565645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90488093722572453692175053 33933035145964670134565645)
  ·
    refine ⟨12724888179736751300462117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33933035145964670134565645 12724888179736751300462117)
    ·
      refine ⟨2385916533700640868836647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12724888179736751300462117 2385916533700640868836647)
      ·
        refine ⟨3578874800550961303254971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2385916533700640868836647 3578874800550961303254971)
        ·
          refine ⟨5368312200826441954882457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3578874800550961303254971 5368312200826441954882457)
          ·
            refine ⟨4026234150619831466161843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5368312200826441954882457 4026234150619831466161843)
            ·
              refine ⟨6039351225929747199242765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4026234150619831466161843 6039351225929747199242765)
              ·
                refine ⟨2264756709723655199716037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6039351225929747199242765 2264756709723655199716037)
                ·
                  refine ⟨424641883073185349946757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2264756709723655199716037 424641883073185349946757)
                  ·
                    rfl

theorem cell22_3721442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 2, 1, 3, 4].length) (baseStart_3721442 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3721442 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3721442 prefixEnd_3721442 := by exact prefixLift 3721442
  have htrace : WordTrace (prefixWord ++ tailWord_3721442) baseStart_3721442 baseEnd_3721442 := by
    simpa [prefixWord, tailWord_3721442, baseEnd_3721442] using wordTrace_append hprefix tailTrace_3721442
  have hstable : (prefixWord ++ tailWord_3721442).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3721442).length < 2 ^ (prefixWord ++ tailWord_3721442).sum := by decide
  have hdescent : baseEnd_3721442 < baseStart_3721442 := by decide
  rcases family_descends (prefixWord ++ tailWord_3721442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3721481 : List Nat := [1, 2, 1, 1, 3, 6, 2, 1, 5]
def baseStart_3721481 : Nat := 118140960795 + 3721481 * 2 ^ 59
def prefixEnd_3721481 : Nat := 4983230072969 + 3 ^ 40 * 3721481 * 2
def baseEnd_3721481 : Nat := 424646333238857649371717

theorem tailTrace_3721481 : CollatzResearch.WordTrace tailWord_3721481 prefixEnd_3721481 424646333238857649371717 := by
  unfold tailWord_3721481
  simp only [CollatzResearch.WordTrace]
  refine ⟨135733563030717390198932297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90489042020478260132621531 135733563030717390198932297)
  ·
    refine ⟨101800172273038042649199223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135733563030717390198932297 101800172273038042649199223)
    ·
      refine ⟨152700258409557063973798835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101800172273038042649199223 152700258409557063973798835)
      ·
        refine ⟨229050387614335595960698253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152700258409557063973798835 229050387614335595960698253)
        ·
          refine ⟨85893895355375848485261845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 229050387614335595960698253 85893895355375848485261845)
          ·
            refine ⟨4026276344783242897746649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 85893895355375848485261845 4026276344783242897746649)
            ·
              refine ⟨3019707258587432173309987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4026276344783242897746649 3019707258587432173309987)
              ·
                refine ⟨4529560887881148259964981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3019707258587432173309987 4529560887881148259964981)
                ·
                  refine ⟨424646333238857649371717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4529560887881148259964981 424646333238857649371717)
                  ·
                    rfl

theorem cell22_3721481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 6, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 6, 2, 1, 5].length) (baseStart_3721481 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3721481 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3721481 prefixEnd_3721481 := by exact prefixLift 3721481
  have htrace : WordTrace (prefixWord ++ tailWord_3721481) baseStart_3721481 baseEnd_3721481 := by
    simpa [prefixWord, tailWord_3721481, baseEnd_3721481] using wordTrace_append hprefix tailTrace_3721481
  have hstable : (prefixWord ++ tailWord_3721481).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3721481).length < 2 ^ (prefixWord ++ tailWord_3721481).sum := by decide
  have hdescent : baseEnd_3721481 < baseStart_3721481 := by decide
  rcases family_descends (prefixWord ++ tailWord_3721481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3721556 : List Nat := [2, 4, 1, 1, 2, 2, 3, 1, 2, 4]
def baseStart_3721556 : Nat := 118140960795 + 3721556 * 2 ^ 59
def prefixEnd_3721556 : Nat := 4983230072969 + 3 ^ 40 * 3721556 * 2
def baseEnd_3721556 : Nat := 1273964673749297752489921

theorem tailTrace_3721556 : CollatzResearch.WordTrace tailWord_3721556 prefixEnd_3721556 1273964673749297752489921 := by
  unfold tailWord_3721556
  simp only [CollatzResearch.WordTrace]
  refine ⟨67868149252722839003956261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90490865670297118671941681 67868149252722839003956261)
  ·
    refine ⟨12725277984885532313241799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 67868149252722839003956261 12725277984885532313241799)
    ·
      refine ⟨19087916977328298469862699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12725277984885532313241799 19087916977328298469862699)
      ·
        refine ⟨28631875465992447704794049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19087916977328298469862699 28631875465992447704794049)
        ·
          refine ⟨21473906599494335778595537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28631875465992447704794049 21473906599494335778595537)
          ·
            refine ⟨16105429949620751833946653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21473906599494335778595537 16105429949620751833946653)
            ·
              refine ⟨6039536231107781937729995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16105429949620751833946653 6039536231107781937729995)
              ·
                refine ⟨9059304346661672906594993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6039536231107781937729995 9059304346661672906594993)
                ·
                  refine ⟨6794478259996254679946245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9059304346661672906594993 6794478259996254679946245)
                  ·
                    refine ⟨1273964673749297752489921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6794478259996254679946245 1273964673749297752489921)
                    ·
                      rfl

theorem cell22_3721556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 3, 1, 2, 4].length) (baseStart_3721556 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3721556 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3721556 prefixEnd_3721556 := by exact prefixLift 3721556
  have htrace : WordTrace (prefixWord ++ tailWord_3721556) baseStart_3721556 baseEnd_3721556 := by
    simpa [prefixWord, tailWord_3721556, baseEnd_3721556] using wordTrace_append hprefix tailTrace_3721556
  have hstable : (prefixWord ++ tailWord_3721556).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3721556).length < 2 ^ (prefixWord ++ tailWord_3721556).sum := by decide
  have hdescent : baseEnd_3721556 < baseStart_3721556 := by decide
  rcases family_descends (prefixWord ++ tailWord_3721556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3721586 : List Nat := [3, 2, 1, 2, 1, 3, 1, 3, 3, 3]
def baseStart_3721586 : Nat := 118140960795 + 3721586 * 2 ^ 59
def prefixEnd_3721586 : Nat := 4983230072969 + 3 ^ 40 * 3721586 * 2
def baseEnd_3721586 : Nat := 1273974943362387674239829

theorem tailTrace_3721586 : CollatzResearch.WordTrace tailWord_3721586 prefixEnd_3721586 1273974943362387674239829 := by
  unfold tailWord_3721586
  simp only [CollatzResearch.WordTrace]
  refine ⟨33934348173834248282876153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90491595130224662087669741 33934348173834248282876153)
  ·
    refine ⟨25450761130375686212157115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33934348173834248282876153 25450761130375686212157115)
    ·
      refine ⟨38176141695563529318235673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25450761130375686212157115 38176141695563529318235673)
      ·
        refine ⟨28632106271672646988676755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38176141695563529318235673 28632106271672646988676755)
        ·
          refine ⟨42948159407508970483015133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28632106271672646988676755 42948159407508970483015133)
          ·
            refine ⟨16105559777815863931130675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42948159407508970483015133 16105559777815863931130675)
            ·
              refine ⟨24158339666723795896696013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16105559777815863931130675 24158339666723795896696013)
              ·
                refine ⟨9059377375021423461261005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24158339666723795896696013 9059377375021423461261005)
                ·
                  refine ⟨3397266515633033797972877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9059377375021423461261005 3397266515633033797972877)
                  ·
                    refine ⟨1273974943362387674239829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3397266515633033797972877 1273974943362387674239829)
                    ·
                      rfl

theorem cell22_3721586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 1, 3, 3, 3].length) (baseStart_3721586 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3721586 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3721586 prefixEnd_3721586 := by exact prefixLift 3721586
  have htrace : WordTrace (prefixWord ++ tailWord_3721586) baseStart_3721586 baseEnd_3721586 := by
    simpa [prefixWord, tailWord_3721586, baseEnd_3721586] using wordTrace_append hprefix tailTrace_3721586
  have hstable : (prefixWord ++ tailWord_3721586).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3721586).length < 2 ^ (prefixWord ++ tailWord_3721586).sum := by decide
  have hdescent : baseEnd_3721586 < baseStart_3721586 := by decide
  rcases family_descends (prefixWord ++ tailWord_3721586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3721622 : List Nat := [5, 3, 1, 2, 2, 1, 8]
def baseStart_3721622 : Nat := 118140960795 + 3721622 * 2 ^ 59
def prefixEnd_3721622 : Nat := 4983230072969 + 3 ^ 40 * 3721622 * 2
def baseEnd_3721622 : Nat := 47184713588818354827397

theorem tailTrace_3721622 : CollatzResearch.WordTrace tailWord_3721622 prefixEnd_3721622 47184713588818354827397 := by
  unfold tailWord_3721622
  simp only [CollatzResearch.WordTrace]
  refine ⟨8483669107700410704988445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 90492470482137714186543413 8483669107700410704988445)
  ·
    refine ⟨3181375915387654014370667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8483669107700410704988445 3181375915387654014370667)
    ·
      refine ⟨4772063873081481021556001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3181375915387654014370667 4772063873081481021556001)
      ·
        refine ⟨3579047904811110766167001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4772063873081481021556001 3579047904811110766167001)
        ·
          refine ⟨2684285928608333074625251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3579047904811110766167001 2684285928608333074625251)
          ·
            refine ⟨4026428892912499611937877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2684285928608333074625251 4026428892912499611937877)
            ·
              refine ⟨47184713588818354827397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4026428892912499611937877 47184713588818354827397)
              ·
                rfl

theorem cell22_3721622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 2, 1, 8].length) (baseStart_3721622 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3721622 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3721622 prefixEnd_3721622 := by exact prefixLift 3721622
  have htrace : WordTrace (prefixWord ++ tailWord_3721622) baseStart_3721622 baseEnd_3721622 := by
    simpa [prefixWord, tailWord_3721622, baseEnd_3721622] using wordTrace_append hprefix tailTrace_3721622
  have hstable : (prefixWord ++ tailWord_3721622).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3721622).length < 2 ^ (prefixWord ++ tailWord_3721622).sum := by decide
  have hdescent : baseEnd_3721622 < baseStart_3721622 := by decide
  rcases family_descends (prefixWord ++ tailWord_3721622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3721695 : List Nat := [1, 1, 2, 3, 3, 4, 2, 2, 4]
def baseStart_3721695 : Nat := 118140960795 + 3721695 * 2 ^ 59
def prefixEnd_3721695 : Nat := 4983230072969 + 3 ^ 40 * 3721695 * 2
def baseEnd_3721695 : Nat := 424670752096649241088165

theorem tailTrace_3721695 : CollatzResearch.WordTrace tailWord_3721695 prefixEnd_3721695 424670752096649241088165 := by
  unfold tailWord_3721695
  simp only [CollatzResearch.WordTrace]
  refine ⟨135741368251942104747222539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90494245501294736498148359 135741368251942104747222539)
  ·
    refine ⟨203612052377913157120833809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135741368251942104747222539 203612052377913157120833809)
    ·
      refine ⟨152709039283434867840625357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 203612052377913157120833809 152709039283434867840625357)
      ·
        refine ⟨57265889731288075440234509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 152709039283434867840625357 57265889731288075440234509)
        ·
          refine ⟨21474708649233028290087941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57265889731288075440234509 21474708649233028290087941)
          ·
            refine ⟨4026507871731192804391489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21474708649233028290087941 4026507871731192804391489)
            ·
              refine ⟨3019880903798394603293617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4026507871731192804391489 3019880903798394603293617)
              ·
                refine ⟨2264910677848795952470213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3019880903798394603293617 2264910677848795952470213)
                ·
                  refine ⟨424670752096649241088165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2264910677848795952470213 424670752096649241088165)
                  ·
                    rfl

theorem cell22_3721695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 4, 2, 2, 4].length) (baseStart_3721695 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3721695 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3721695 prefixEnd_3721695 := by exact prefixLift 3721695
  have htrace : WordTrace (prefixWord ++ tailWord_3721695) baseStart_3721695 baseEnd_3721695 := by
    simpa [prefixWord, tailWord_3721695, baseEnd_3721695] using wordTrace_append hprefix tailTrace_3721695
  have hstable : (prefixWord ++ tailWord_3721695).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3721695).length < 2 ^ (prefixWord ++ tailWord_3721695).sum := by decide
  have hdescent : baseEnd_3721695 < baseStart_3721695 := by decide
  rcases family_descends (prefixWord ++ tailWord_3721695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3721706 : List Nat := [3, 1, 3, 1, 3, 1, 3, 7]
def baseStart_3721706 : Nat := 118140960795 + 3721706 * 2 ^ 59
def prefixEnd_3721706 : Nat := 4983230072969 + 3 ^ 40 * 3721706 * 2
def baseEnd_3721706 : Nat := 141557335757194151248829

theorem tailTrace_3721706 : CollatzResearch.WordTrace tailWord_3721706 prefixEnd_3721706 141557335757194151248829 := by
  unfold tailWord_3721706
  simp only [CollatzResearch.WordTrace]
  refine ⟨33935442363725563406468243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90494512969934835750581981 33935442363725563406468243)
  ·
    refine ⟨50903163545588345109702365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33935442363725563406468243 50903163545588345109702365)
    ·
      refine ⟨19088686329595629416138387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50903163545588345109702365 19088686329595629416138387)
      ·
        refine ⟨28633029494393444124207581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19088686329595629416138387 28633029494393444124207581)
        ·
          refine ⟨10737386060397541546577843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28633029494393444124207581 10737386060397541546577843)
          ·
            refine ⟨16106079090596312319866765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10737386060397541546577843 16106079090596312319866765)
            ·
              refine ⟨6039779658973617119950037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16106079090596312319866765 6039779658973617119950037)
              ·
                refine ⟨141557335757194151248829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6039779658973617119950037 141557335757194151248829)
                ·
                  rfl

theorem cell22_3721706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 3, 7].length) (baseStart_3721706 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3721706 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3721706 prefixEnd_3721706 := by exact prefixLift 3721706
  have htrace : WordTrace (prefixWord ++ tailWord_3721706) baseStart_3721706 baseEnd_3721706 := by
    simpa [prefixWord, tailWord_3721706, baseEnd_3721706] using wordTrace_append hprefix tailTrace_3721706
  have hstable : (prefixWord ++ tailWord_3721706).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3721706).length < 2 ^ (prefixWord ++ tailWord_3721706).sum := by decide
  have hdescent : baseEnd_3721706 < baseStart_3721706 := by decide
  rcases family_descends (prefixWord ++ tailWord_3721706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3721721 : List Nat := [1, 2, 1, 3, 1, 2, 3, 1, 5, 3]
def baseStart_3721721 : Nat := 118140960795 + 3721721 * 2 ^ 59
def prefixEnd_3721721 : Nat := 4983230072969 + 3 ^ 40 * 3721721 * 2
def baseEnd_3721721 : Nat := 1274021156621292322114415

theorem tailTrace_3721721 : CollatzResearch.WordTrace tailWord_3721721 prefixEnd_3721721 1274021156621292322114415 := by
  unfold tailWord_3721721
  simp only [CollatzResearch.WordTrace]
  refine ⟨135742316549847911187669017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90494877699898607458446011 135742316549847911187669017)
  ·
    refine ⟨101806737412385933390751763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135742316549847911187669017 101806737412385933390751763)
    ·
      refine ⟨152710106118578900086127645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101806737412385933390751763 152710106118578900086127645)
      ·
        refine ⟨57266289794467087532297867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 152710106118578900086127645 57266289794467087532297867)
        ·
          refine ⟨85899434691700631298446801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57266289794467087532297867 85899434691700631298446801)
          ·
            refine ⟨64424576018775473473835101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85899434691700631298446801 64424576018775473473835101)
            ·
              refine ⟨24159216007040802552688163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64424576018775473473835101 24159216007040802552688163)
              ·
                refine ⟨36238824010561203829032245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24159216007040802552688163 36238824010561203829032245)
                ·
                  refine ⟨3397389750990112858971773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 36238824010561203829032245 3397389750990112858971773)
                  ·
                    refine ⟨1274021156621292322114415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3397389750990112858971773 1274021156621292322114415)
                    ·
                      rfl

theorem cell22_3721721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 3, 1, 5, 3].length) (baseStart_3721721 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3721721 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3721721 prefixEnd_3721721 := by exact prefixLift 3721721
  have htrace : WordTrace (prefixWord ++ tailWord_3721721) baseStart_3721721 baseEnd_3721721 := by
    simpa [prefixWord, tailWord_3721721, baseEnd_3721721] using wordTrace_append hprefix tailTrace_3721721
  have hstable : (prefixWord ++ tailWord_3721721).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3721721).length < 2 ^ (prefixWord ++ tailWord_3721721).sum := by decide
  have hdescent : baseEnd_3721721 < baseStart_3721721 := by decide
  rcases family_descends (prefixWord ++ tailWord_3721721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3721813 : List Nat := [1, 3, 2, 2, 1, 1, 2, 6, 4]
def baseStart_3721813 : Nat := 118140960795 + 3721813 * 2 ^ 59
def prefixEnd_3721813 : Nat := 4983230072969 + 3 ^ 40 * 3721813 * 2
def baseEnd_3721813 : Nat := 424684216700478249604711

theorem tailTrace_3721813 : CollatzResearch.WordTrace tailWord_3721813 prefixEnd_3721813 424684216700478249604711 := by
  unfold tailWord_3721813
  simp only [CollatzResearch.WordTrace]
  refine ⟨135745672065514610900018093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90497114710343073933345395 135745672065514610900018093)
  ·
    refine ⟨50904627024567979087506785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135745672065514610900018093 50904627024567979087506785)
    ·
      refine ⟨38178470268425984315630089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50904627024567979087506785 38178470268425984315630089)
      ·
        refine ⟨28633852701319488236722567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38178470268425984315630089 28633852701319488236722567)
        ·
          refine ⟨42950779051979232355083851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28633852701319488236722567 42950779051979232355083851)
          ·
            refine ⟨64426168577968848532625777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42950779051979232355083851 64426168577968848532625777)
            ·
              refine ⟨48319626433476636399469333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64426168577968848532625777 48319626433476636399469333)
              ·
                refine ⟨2264982489069217331225125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 48319626433476636399469333 2264982489069217331225125)
                ·
                  refine ⟨424684216700478249604711, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2264982489069217331225125 424684216700478249604711)
                  ·
                    rfl

theorem cell22_3721813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 6, 4].length) (baseStart_3721813 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3721813 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3721813 prefixEnd_3721813 := by exact prefixLift 3721813
  have htrace : WordTrace (prefixWord ++ tailWord_3721813) baseStart_3721813 baseEnd_3721813 := by
    simpa [prefixWord, tailWord_3721813, baseEnd_3721813] using wordTrace_append hprefix tailTrace_3721813
  have hstable : (prefixWord ++ tailWord_3721813).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3721813).length < 2 ^ (prefixWord ++ tailWord_3721813).sum := by decide
  have hdescent : baseEnd_3721813 < baseStart_3721813 := by decide
  rcases family_descends (prefixWord ++ tailWord_3721813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3721832 : List Nat := [2, 1, 4, 3, 2, 2, 1, 2, 1, 4]
def baseStart_3721832 : Nat := 118140960795 + 3721832 * 2 ^ 59
def prefixEnd_3721832 : Nat := 4983230072969 + 3 ^ 40 * 3721832 * 2
def baseEnd_3721832 : Nat := 1274059154189725032589075

theorem tailTrace_3721832 : CollatzResearch.WordTrace tailWord_3721832 prefixEnd_3721832 1274059154189725032589075 := by
  unfold tailWord_3721832
  simp only [CollatzResearch.WordTrace]
  refine ⟨67873182526222888572479875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90497576701630518096639833 67873182526222888572479875)
  ·
    refine ⟨101809773789334332858719813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67873182526222888572479875 101809773789334332858719813)
    ·
      refine ⟨19089332585500187411009965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 101809773789334332858719813 19089332585500187411009965)
      ·
        refine ⟨7158499719562570279128737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19089332585500187411009965 7158499719562570279128737)
        ·
          refine ⟨5368874789671927709346553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7158499719562570279128737 5368874789671927709346553)
          ·
            refine ⟨4026656092253945782009915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5368874789671927709346553 4026656092253945782009915)
            ·
              refine ⟨6039984138380918673014873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4026656092253945782009915 6039984138380918673014873)
              ·
                refine ⟨4529988103785689004761155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6039984138380918673014873 4529988103785689004761155)
                ·
                  refine ⟨6794982155678533507141733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4529988103785689004761155 6794982155678533507141733)
                  ·
                    refine ⟨1274059154189725032589075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6794982155678533507141733 1274059154189725032589075)
                    ·
                      rfl

theorem cell22_3721832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 2, 1, 2, 1, 4].length) (baseStart_3721832 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3721832 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3721832 prefixEnd_3721832 := by exact prefixLift 3721832
  have htrace : WordTrace (prefixWord ++ tailWord_3721832) baseStart_3721832 baseEnd_3721832 := by
    simpa [prefixWord, tailWord_3721832, baseEnd_3721832] using wordTrace_append hprefix tailTrace_3721832
  have hstable : (prefixWord ++ tailWord_3721832).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3721832).length < 2 ^ (prefixWord ++ tailWord_3721832).sum := by decide
  have hdescent : baseEnd_3721832 < baseStart_3721832 := by decide
  rcases family_descends (prefixWord ++ tailWord_3721832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3721845 : List Nat := [1, 3, 4, 2, 2, 1, 1, 2, 1, 5]
def baseStart_3721845 : Nat := 118140960795 + 3721845 * 2 ^ 59
def prefixEnd_3721845 : Nat := 4983230072969 + 3 ^ 40 * 3721845 * 2
def baseEnd_3721845 : Nat := 1274063604355397332014035

theorem tailTrace_3721845 : CollatzResearch.WordTrace tailWord_3721845 prefixEnd_3721845 1274063604355397332014035 := by
  unfold tailWord_3721845
  simp only [CollatzResearch.WordTrace]
  refine ⟨135746839201398680365182989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90497892800932453576788659 135746839201398680365182989)
  ·
    refine ⟨50905064700524505136943621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135746839201398680365182989 50905064700524505136943621)
    ·
      refine ⟨9544699631348344713176929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50905064700524505136943621 9544699631348344713176929)
      ·
        refine ⟨7158524723511258534882697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9544699631348344713176929 7158524723511258534882697)
        ·
          refine ⟨5368893542633443901162023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7158524723511258534882697 5368893542633443901162023)
          ·
            refine ⟨8053340313950165851743035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5368893542633443901162023 8053340313950165851743035)
            ·
              refine ⟨12080010470925248777614553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8053340313950165851743035 12080010470925248777614553)
              ·
                refine ⟨9060007853193936583210915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12080010470925248777614553 9060007853193936583210915)
                ·
                  refine ⟨13590011779790904874816373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9060007853193936583210915 13590011779790904874816373)
                  ·
                    refine ⟨1274063604355397332014035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13590011779790904874816373 1274063604355397332014035)
                    ·
                      rfl

theorem cell22_3721845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 1, 2, 1, 5].length) (baseStart_3721845 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3721845 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3721845 prefixEnd_3721845 := by exact prefixLift 3721845
  have htrace : WordTrace (prefixWord ++ tailWord_3721845) baseStart_3721845 baseEnd_3721845 := by
    simpa [prefixWord, tailWord_3721845, baseEnd_3721845] using wordTrace_append hprefix tailTrace_3721845
  have hstable : (prefixWord ++ tailWord_3721845).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3721845).length < 2 ^ (prefixWord ++ tailWord_3721845).sum := by decide
  have hdescent : baseEnd_3721845 < baseStart_3721845 := by decide
  rcases family_descends (prefixWord ++ tailWord_3721845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3721907 : List Nat := [1, 1, 1, 2, 3, 5, 2, 3, 1, 3]
def baseStart_3721907 : Nat := 118140960795 + 3721907 * 2 ^ 59
def prefixEnd_3721907 : Nat := 4983230072969 + 3 ^ 40 * 3721907 * 2
def baseEnd_3721907 : Nat := 1274084828222449836963845

theorem tailTrace_3721907 : CollatzResearch.WordTrace tailWord_3721907 prefixEnd_3721907 1274084828222449836963845 := by
  unfold tailWord_3721907
  simp only [CollatzResearch.WordTrace]
  refine ⟨135749100527174064953939975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90499400351449376635959983 135749100527174064953939975)
  ·
    refine ⟨203623650790761097430909963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135749100527174064953939975 203623650790761097430909963)
    ·
      refine ⟨305435476186141646146364945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203623650790761097430909963 305435476186141646146364945)
      ·
        refine ⟨229076607139606234609773709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 305435476186141646146364945 229076607139606234609773709)
        ·
          refine ⟨85903727677352337978665141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 229076607139606234609773709 85903727677352337978665141)
          ·
            refine ⟨8053474469751781685499857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 85903727677352337978665141 8053474469751781685499857)
            ·
              refine ⟨6040105852313836264124893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8053474469751781685499857 6040105852313836264124893)
              ·
                refine ⟨2265039694617688599046835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6040105852313836264124893 2265039694617688599046835)
                ·
                  refine ⟨3397559541926532898570253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2265039694617688599046835 3397559541926532898570253)
                  ·
                    refine ⟨1274084828222449836963845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3397559541926532898570253 1274084828222449836963845)
                    ·
                      rfl

theorem cell22_3721907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 2, 3, 1, 3].length) (baseStart_3721907 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3721907 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3721907 prefixEnd_3721907 := by exact prefixLift 3721907
  have htrace : WordTrace (prefixWord ++ tailWord_3721907) baseStart_3721907 baseEnd_3721907 := by
    simpa [prefixWord, tailWord_3721907, baseEnd_3721907] using wordTrace_append hprefix tailTrace_3721907
  have hstable : (prefixWord ++ tailWord_3721907).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3721907).length < 2 ^ (prefixWord ++ tailWord_3721907).sum := by decide
  have hdescent : baseEnd_3721907 < baseStart_3721907 := by decide
  rcases family_descends (prefixWord ++ tailWord_3721907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3721918 : List Nat := [4, 2, 1, 1, 2, 1, 1, 1, 4, 5]
def baseStart_3721918 : Nat := 118140960795 + 3721918 * 2 ^ 59
def prefixEnd_3721918 : Nat := 4983230072969 + 3 ^ 40 * 3721918 * 2
def baseEnd_3721918 : Nat := 1274088593747249474938811

theorem tailTrace_3721918 : CollatzResearch.WordTrace tailWord_3721918 prefixEnd_3721918 1274088593747249474938811 := by
  unfold tailWord_3721918
  simp only [CollatzResearch.WordTrace]
  refine ⟨16968687716266776729073801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 90499667820089475888393605 16968687716266776729073801)
  ·
    refine ⟨12726515787200082546805351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16968687716266776729073801 12726515787200082546805351)
    ·
      refine ⟨19089773680800123820208027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12726515787200082546805351 19089773680800123820208027)
      ·
        refine ⟨28634660521200185730312041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19089773680800123820208027 28634660521200185730312041)
        ·
          refine ⟨21475995390900139297734031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28634660521200185730312041 21475995390900139297734031)
          ·
            refine ⟨32213993086350208946601047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21475995390900139297734031 32213993086350208946601047)
            ·
              refine ⟨48320989629525313419901571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32213993086350208946601047 48320989629525313419901571)
              ·
                refine ⟨72481484444287970129852357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48320989629525313419901571 72481484444287970129852357)
                ·
                  refine ⟨13590278333303994399347317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 72481484444287970129852357 13590278333303994399347317)
                  ·
                    refine ⟨1274088593747249474938811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13590278333303994399347317 1274088593747249474938811)
                    ·
                      rfl

theorem cell22_3721918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 1, 4, 5].length) (baseStart_3721918 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3721918 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3721918 prefixEnd_3721918 := by exact prefixLift 3721918
  have htrace : WordTrace (prefixWord ++ tailWord_3721918) baseStart_3721918 baseEnd_3721918 := by
    simpa [prefixWord, tailWord_3721918, baseEnd_3721918] using wordTrace_append hprefix tailTrace_3721918
  have hstable : (prefixWord ++ tailWord_3721918).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3721918).length < 2 ^ (prefixWord ++ tailWord_3721918).sum := by decide
  have hdescent : baseEnd_3721918 < baseStart_3721918 := by decide
  rcases family_descends (prefixWord ++ tailWord_3721918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3721920 : List Nat := [2, 1, 1, 2, 4, 4, 1, 2, 5]
def baseStart_3721920 : Nat := 118140960795 + 3721920 * 2 ^ 59
def prefixEnd_3721920 : Nat := 4983230072969 + 3 ^ 40 * 3721920 * 2
def baseEnd_3721920 : Nat := 424696426129374045462935

theorem tailTrace_3721920 : CollatzResearch.WordTrace tailWord_3721920 prefixEnd_3721920 424696426129374045462935 := by
  unfold tailWord_3721920
  simp only [CollatzResearch.WordTrace]
  refine ⟨67874787338063484087081607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90499716450751312116108809 67874787338063484087081607)
  ·
    refine ⟨101812181007095226130622411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67874787338063484087081607 101812181007095226130622411)
    ·
      refine ⟨152718271510642839195933617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101812181007095226130622411 152718271510642839195933617)
      ·
        refine ⟨114538703632982129396950213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152718271510642839195933617 114538703632982129396950213)
        ·
          refine ⟨21476006931184149261928165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 114538703632982129396950213 21476006931184149261928165)
          ·
            refine ⟨4026751299597027986611531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21476006931184149261928165 4026751299597027986611531)
            ·
              refine ⟨6040126949395541979917297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4026751299597027986611531 6040126949395541979917297)
              ·
                refine ⟨4530095212046656484937973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6040126949395541979917297 4530095212046656484937973)
                ·
                  refine ⟨424696426129374045462935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4530095212046656484937973 424696426129374045462935)
                  ·
                    rfl

theorem cell22_3721920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 4, 1, 2, 5].length) (baseStart_3721920 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3721920 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3721920 prefixEnd_3721920 := by exact prefixLift 3721920
  have htrace : WordTrace (prefixWord ++ tailWord_3721920) baseStart_3721920 baseEnd_3721920 := by
    simpa [prefixWord, tailWord_3721920, baseEnd_3721920] using wordTrace_append hprefix tailTrace_3721920
  have hstable : (prefixWord ++ tailWord_3721920).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3721920).length < 2 ^ (prefixWord ++ tailWord_3721920).sum := by decide
  have hdescent : baseEnd_3721920 < baseStart_3721920 := by decide
  rcases family_descends (prefixWord ++ tailWord_3721920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3721978 : List Nat := [3, 1, 1, 1, 1, 3, 3, 1, 4, 4]
def baseStart_3721978 : Nat := 118140960795 + 3721978 * 2 ^ 59
def prefixEnd_3721978 : Nat := 4983230072969 + 3 ^ 40 * 3721978 * 2
def baseEnd_3721978 : Nat := 1274109132973429318438627

theorem tailTrace_3721978 : CollatzResearch.WordTrace tailWord_3721978 prefixEnd_3721978 1274109132973429318438627 := by
  unfold tailWord_3721978
  simp only [CollatzResearch.WordTrace]
  refine ⟨33937922527479211019943647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90501126739944562719849725 33937922527479211019943647)
  ·
    refine ⟨50906883791218816529915471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33937922527479211019943647 50906883791218816529915471)
    ·
      refine ⟨76360325686828224794873207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50906883791218816529915471 76360325686828224794873207)
      ·
        refine ⟨114540488530242337192309811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76360325686828224794873207 114540488530242337192309811)
        ·
          refine ⟨171810732795363505788464717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114540488530242337192309811 171810732795363505788464717)
          ·
            refine ⟨64429024798261314670674269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 171810732795363505788464717 64429024798261314670674269)
            ·
              refine ⟨24160884299347993001502851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64429024798261314670674269 24160884299347993001502851)
              ·
                refine ⟨36241326449021989502254277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24160884299347993001502851 36241326449021989502254277)
                ·
                  refine ⟨6795248709191623031672677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36241326449021989502254277 6795248709191623031672677)
                  ·
                    refine ⟨1274109132973429318438627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6795248709191623031672677 1274109132973429318438627)
                    ·
                      rfl

theorem cell22_3721978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 3, 1, 4, 4].length) (baseStart_3721978 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3721978 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3721978 prefixEnd_3721978 := by exact prefixLift 3721978
  have htrace : WordTrace (prefixWord ++ tailWord_3721978) baseStart_3721978 baseEnd_3721978 := by
    simpa [prefixWord, tailWord_3721978, baseEnd_3721978] using wordTrace_append hprefix tailTrace_3721978
  have hstable : (prefixWord ++ tailWord_3721978).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3721978).length < 2 ^ (prefixWord ++ tailWord_3721978).sum := by decide
  have hdescent : baseEnd_3721978 < baseStart_3721978 := by decide
  rcases family_descends (prefixWord ++ tailWord_3721978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3721980 : List Nat := [2, 2, 2, 1, 3, 2, 2, 1, 4, 3]
def baseStart_3721980 : Nat := 118140960795 + 3721980 * 2 ^ 59
def prefixEnd_3721980 : Nat := 4983230072969 + 3 ^ 40 * 3721980 * 2
def baseEnd_3721980 : Nat := 1274109817614301979888621

theorem tailTrace_3721980 : CollatzResearch.WordTrace tailWord_3721980 prefixEnd_3721980 1274109817614301979888621 := by
  unfold tailWord_3721980
  simp only [CollatzResearch.WordTrace]
  refine ⟨67875881527954799210673697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90501175370606398947564929 67875881527954799210673697)
  ·
    refine ⟨50906911145966099408005273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67875881527954799210673697 50906911145966099408005273)
    ·
      refine ⟨38180183359474574556003955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50906911145966099408005273 38180183359474574556003955)
      ·
        refine ⟨57270275039211861834005933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38180183359474574556003955 57270275039211861834005933)
        ·
          refine ⟨21476353139704448187752225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57270275039211861834005933 21476353139704448187752225)
          ·
            refine ⟨16107264854778336140814169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21476353139704448187752225 16107264854778336140814169)
            ·
              refine ⟨12080448641083752105610627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16107264854778336140814169 12080448641083752105610627)
              ·
                refine ⟨18120672961625628158415941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12080448641083752105610627 18120672961625628158415941)
                ·
                  refine ⟨3397626180304805279702989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18120672961625628158415941 3397626180304805279702989)
                  ·
                    refine ⟨1274109817614301979888621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3397626180304805279702989 1274109817614301979888621)
                    ·
                      rfl

theorem cell22_3721980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 2, 1, 4, 3].length) (baseStart_3721980 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3721980 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3721980 prefixEnd_3721980 := by exact prefixLift 3721980
  have htrace : WordTrace (prefixWord ++ tailWord_3721980) baseStart_3721980 baseEnd_3721980 := by
    simpa [prefixWord, tailWord_3721980, baseEnd_3721980] using wordTrace_append hprefix tailTrace_3721980
  have hstable : (prefixWord ++ tailWord_3721980).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3721980).length < 2 ^ (prefixWord ++ tailWord_3721980).sum := by decide
  have hdescent : baseEnd_3721980 < baseStart_3721980 := by decide
  rcases family_descends (prefixWord ++ tailWord_3721980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3721982 : List Nat := [4, 2, 2, 1, 2, 3, 1, 1, 6]
def baseStart_3721982 : Nat := 118140960795 + 3721982 * 2 ^ 59
def prefixEnd_3721982 : Nat := 4983230072969 + 3 ^ 40 * 3721982 * 2
def baseEnd_3721982 : Nat := 424703500751724880446205

theorem tailTrace_3721982 : CollatzResearch.WordTrace tailWord_3721982 prefixEnd_3721982 424703500751724880446205 := by
  unfold tailWord_3721982
  simp only [CollatzResearch.WordTrace]
  refine ⟨16968979500237794095365025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 90501224001268235175280133 16968979500237794095365025)
  ·
    refine ⟨12726734625178345571523769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16968979500237794095365025 12726734625178345571523769)
    ·
      refine ⟨9545050968883759178642827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12726734625178345571523769 9545050968883759178642827)
      ·
        refine ⟨14317576453325638767964241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9545050968883759178642827 14317576453325638767964241)
        ·
          refine ⟨10738182339994229075973181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14317576453325638767964241 10738182339994229075973181)
          ·
            refine ⟨4026818377497835903489943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10738182339994229075973181 4026818377497835903489943)
            ·
              refine ⟨6040227566246753855234915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4026818377497835903489943 6040227566246753855234915)
              ·
                refine ⟨9060341349370130782852373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6040227566246753855234915 9060341349370130782852373)
                ·
                  refine ⟨424703500751724880446205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9060341349370130782852373 424703500751724880446205)
                  ·
                    rfl

theorem cell22_3721982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 3, 1, 1, 6].length) (baseStart_3721982 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3721982 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3721982 prefixEnd_3721982 := by exact prefixLift 3721982
  have htrace : WordTrace (prefixWord ++ tailWord_3721982) baseStart_3721982 baseEnd_3721982 := by
    simpa [prefixWord, tailWord_3721982, baseEnd_3721982] using wordTrace_append hprefix tailTrace_3721982
  have hstable : (prefixWord ++ tailWord_3721982).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3721982).length < 2 ^ (prefixWord ++ tailWord_3721982).sum := by decide
  have hdescent : baseEnd_3721982 < baseStart_3721982 := by decide
  rcases family_descends (prefixWord ++ tailWord_3721982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3722076 : List Nat := [2, 2, 4, 2, 1, 2, 2, 3, 1, 3]
def baseStart_3722076 : Nat := 118140960795 + 3722076 * 2 ^ 59
def prefixEnd_3722076 : Nat := 4983230072969 + 3 ^ 40 * 3722076 * 2
def baseEnd_3722076 : Nat := 1274142680376189729488327

theorem tailTrace_3722076 : CollatzResearch.WordTrace tailWord_3722076 prefixEnd_3722076 1274142680376189729488327 := by
  unfold tailWord_3722076
  simp only [CollatzResearch.WordTrace]
  refine ⟨67877632231780903408421041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90503509642374537877894721 67877632231780903408421041)
  ·
    refine ⟨50908224173835677556315781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67877632231780903408421041 50908224173835677556315781)
    ·
      refine ⟨9545292032594189541809209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50908224173835677556315781 9545292032594189541809209)
      ·
        refine ⟨7158969024445642156356907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9545292032594189541809209 7158969024445642156356907)
        ·
          refine ⟨10738453536668463234535361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7158969024445642156356907 10738453536668463234535361)
          ·
            refine ⟨8053840152501347425901521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10738453536668463234535361 8053840152501347425901521)
            ·
              refine ⟨6040380114376010569426141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8053840152501347425901521 6040380114376010569426141)
              ·
                refine ⟨2265142542891003963534803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6040380114376010569426141 2265142542891003963534803)
                ·
                  refine ⟨3397713814336505945302205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2265142542891003963534803 3397713814336505945302205)
                  ·
                    refine ⟨1274142680376189729488327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3397713814336505945302205 1274142680376189729488327)
                    ·
                      rfl

theorem cell22_3722076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 2, 3, 1, 3].length) (baseStart_3722076 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3722076 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3722076 prefixEnd_3722076 := by exact prefixLift 3722076
  have htrace : WordTrace (prefixWord ++ tailWord_3722076) baseStart_3722076 baseEnd_3722076 := by
    simpa [prefixWord, tailWord_3722076, baseEnd_3722076] using wordTrace_append hprefix tailTrace_3722076
  have hstable : (prefixWord ++ tailWord_3722076).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3722076).length < 2 ^ (prefixWord ++ tailWord_3722076).sum := by decide
  have hdescent : baseEnd_3722076 < baseStart_3722076 := by decide
  rcases family_descends (prefixWord ++ tailWord_3722076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3722132 : List Nat := [2, 4, 2, 1, 1, 1, 1, 1, 6, 3]
def baseStart_3722132 : Nat := 118140960795 + 3722132 * 2 ^ 59
def prefixEnd_3722132 : Nat := 4983230072969 + 3 ^ 40 * 3722132 * 2
def baseEnd_3722132 : Nat := 1274161850320624250088155

theorem tailTrace_3722132 : CollatzResearch.WordTrace tailWord_3722132 prefixEnd_3722132 1274161850320624250088155 := by
  unfold tailWord_3722132
  simp only [CollatzResearch.WordTrace]
  refine ⟨67878653475679464190440325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90504871300905952253920433 67878653475679464190440325)
  ·
    refine ⟨12727247526689899535707561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 67878653475679464190440325 12727247526689899535707561)
    ·
      refine ⟨9545435645017424651780671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12727247526689899535707561 9545435645017424651780671)
      ·
        refine ⟨14318153467526136977671007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9545435645017424651780671 14318153467526136977671007)
        ·
          refine ⟨21477230201289205466506511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14318153467526136977671007 21477230201289205466506511)
          ·
            refine ⟨32215845301933808199759767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21477230201289205466506511 32215845301933808199759767)
            ·
              refine ⟨48323767952900712299639651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32215845301933808199759767 48323767952900712299639651)
              ·
                refine ⟨72485651929351068449459477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48323767952900712299639651 72485651929351068449459477)
                ·
                  refine ⟨3397764934188331333568413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 72485651929351068449459477 3397764934188331333568413)
                  ·
                    refine ⟨1274161850320624250088155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3397764934188331333568413 1274161850320624250088155)
                    ·
                      rfl

theorem cell22_3722132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 1, 6, 3].length) (baseStart_3722132 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3722132 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3722132 prefixEnd_3722132 := by exact prefixLift 3722132
  have htrace : WordTrace (prefixWord ++ tailWord_3722132) baseStart_3722132 baseEnd_3722132 := by
    simpa [prefixWord, tailWord_3722132, baseEnd_3722132] using wordTrace_append hprefix tailTrace_3722132
  have hstable : (prefixWord ++ tailWord_3722132).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3722132).length < 2 ^ (prefixWord ++ tailWord_3722132).sum := by decide
  have hdescent : baseEnd_3722132 < baseStart_3722132 := by decide
  rcases family_descends (prefixWord ++ tailWord_3722132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3722145 : List Nat := [1, 2, 3, 4, 1, 1, 10]
def baseStart_3722145 : Nat := 118140960795 + 3722145 * 2 ^ 59
def prefixEnd_3722145 : Nat := 4983230072969 + 3 ^ 40 * 3722145 * 2
def baseEnd_3722145 : Nat := 47191344462455427759745

theorem tailTrace_3722145 : CollatzResearch.WordTrace tailWord_3722145 prefixEnd_3722145 47191344462455427759745 := by
  unfold tailWord_3722145
  simp only [CollatzResearch.WordTrace]
  refine ⟨135757781100311831601103889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90505187400207887734069259 135757781100311831601103889)
  ·
    refine ⟨101818335825233873700827917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135757781100311831601103889 101818335825233873700827917)
    ·
      refine ⟨38181875934462702637810469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101818335825233873700827917 38181875934462702637810469)
      ·
        refine ⟨7159101737711756744589463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38181875934462702637810469 7159101737711756744589463)
        ·
          refine ⟨10738652606567635116884195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7159101737711756744589463 10738652606567635116884195)
          ·
            refine ⟨16107978909851452675326293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10738652606567635116884195 16107978909851452675326293)
            ·
              refine ⟨47191344462455427759745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 16107978909851452675326293 47191344462455427759745)
              ·
                rfl

theorem cell22_3722145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 10].length) (baseStart_3722145 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3722145 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3722145 prefixEnd_3722145 := by exact prefixLift 3722145
  have htrace : WordTrace (prefixWord ++ tailWord_3722145) baseStart_3722145 baseEnd_3722145 := by
    simpa [prefixWord, tailWord_3722145, baseEnd_3722145] using wordTrace_append hprefix tailTrace_3722145
  have hstable : (prefixWord ++ tailWord_3722145).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3722145).length < 2 ^ (prefixWord ++ tailWord_3722145).sum := by decide
  have hdescent : baseEnd_3722145 < baseStart_3722145 := by decide
  rcases family_descends (prefixWord ++ tailWord_3722145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3722151 : List Nat := [1, 1, 6, 1, 3, 1, 3, 2, 4]
def baseStart_3722151 : Nat := 118140960795 + 3722151 * 2 ^ 59
def prefixEnd_3722151 : Nat := 4983230072969 + 3 ^ 40 * 3722151 * 2
def baseEnd_3722151 : Nat := 424722784802971511287699

theorem tailTrace_3722151 : CollatzResearch.WordTrace tailWord_3722151 prefixEnd_3722151 424722784802971511287699 := by
  unfold tailWord_3722151
  simp only [CollatzResearch.WordTrace]
  refine ⟨135757999938290094625822307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90505333292193396417214871 135757999938290094625822307)
  ·
    refine ⟨203636999907435141938733461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135757999938290094625822307 203636999907435141938733461)
    ·
      refine ⟨9545484370661022278378131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 203636999907435141938733461 9545484370661022278378131)
      ·
        refine ⟨14318226555991533417567197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9545484370661022278378131 14318226555991533417567197)
        ·
          refine ⟨5369334958496825031587699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14318226555991533417567197 5369334958496825031587699)
          ·
            refine ⟨8054002437745237547381549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5369334958496825031587699 8054002437745237547381549)
            ·
              refine ⟨3020250914154464080268081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8054002437745237547381549 3020250914154464080268081)
              ·
                refine ⟨2265188185615848060201061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3020250914154464080268081 2265188185615848060201061)
                ·
                  refine ⟨424722784802971511287699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2265188185615848060201061 424722784802971511287699)
                  ·
                    rfl

theorem cell22_3722151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 3, 2, 4].length) (baseStart_3722151 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3722151 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3722151 prefixEnd_3722151 := by exact prefixLift 3722151
  have htrace : WordTrace (prefixWord ++ tailWord_3722151) baseStart_3722151 baseEnd_3722151 := by
    simpa [prefixWord, tailWord_3722151, baseEnd_3722151] using wordTrace_append hprefix tailTrace_3722151
  have hstable : (prefixWord ++ tailWord_3722151).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3722151).length < 2 ^ (prefixWord ++ tailWord_3722151).sum := by decide
  have hdescent : baseEnd_3722151 < baseStart_3722151 := by decide
  rcases family_descends (prefixWord ++ tailWord_3722151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3722237 : List Nat := [1, 4, 1, 1, 1, 2, 1, 6, 1, 4]
def baseStart_3722237 : Nat := 118140960795 + 3722237 * 2 ^ 59
def prefixEnd_3722237 : Nat := 4983230072969 + 3 ^ 40 * 3722237 * 2
def baseEnd_3722237 : Nat := 1274197793966438976212833

theorem tailTrace_3722237 : CollatzResearch.WordTrace tailWord_3722237 prefixEnd_3722237 1274197793966438976212833 := by
  unfold tailWord_3722237
  simp only [CollatzResearch.WordTrace]
  refine ⟨135761136615978531313452965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90507424410652354208968643 135761136615978531313452965)
  ·
    refine ⟨25455213115495974621272431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 135761136615978531313452965 25455213115495974621272431)
    ·
      refine ⟨38182819673243961931908647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25455213115495974621272431 38182819673243961931908647)
      ·
        refine ⟨57274229509865942897862971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38182819673243961931908647 57274229509865942897862971)
        ·
          refine ⟨85911344264798914346794457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57274229509865942897862971 85911344264798914346794457)
          ·
            refine ⟨64433508198599185760095843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85911344264798914346794457 64433508198599185760095843)
            ·
              refine ⟨96650262297898778640143765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64433508198599185760095843 96650262297898778640143765)
              ·
                refine ⟨4530481045214005248756739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 96650262297898778640143765 4530481045214005248756739)
                ·
                  refine ⟨6795721567821007873135109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4530481045214005248756739 6795721567821007873135109)
                  ·
                    refine ⟨1274197793966438976212833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6795721567821007873135109 1274197793966438976212833)
                    ·
                      rfl

theorem cell22_3722237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 6, 1, 4].length) (baseStart_3722237 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3722237 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3722237 prefixEnd_3722237 := by exact prefixLift 3722237
  have htrace : WordTrace (prefixWord ++ tailWord_3722237) baseStart_3722237 baseEnd_3722237 := by
    simpa [prefixWord, tailWord_3722237, baseEnd_3722237] using wordTrace_append hprefix tailTrace_3722237
  have hstable : (prefixWord ++ tailWord_3722237).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3722237).length < 2 ^ (prefixWord ++ tailWord_3722237).sum := by decide
  have hdescent : baseEnd_3722237 < baseStart_3722237 := by decide
  rcases family_descends (prefixWord ++ tailWord_3722237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3722254 : List Nat := [4, 1, 1, 2, 2, 3, 1, 3, 1, 4]
def baseStart_3722254 : Nat := 118140960795 + 3722254 * 2 ^ 59
def prefixEnd_3722254 : Nat := 4983230072969 + 3 ^ 40 * 3722254 * 2
def baseEnd_3722254 : Nat := 1274203613413856598537781

theorem tailTrace_3722254 : CollatzResearch.WordTrace tailWord_3722254 prefixEnd_3722254 1274203613413856598537781 := by
  unfold tailWord_3722254
  simp only [CollatzResearch.WordTrace]
  refine ⟨16970219582114617902102727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 90507837771277962144547877 16970219582114617902102727)
  ·
    refine ⟨25455329373171926853154091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16970219582114617902102727 25455329373171926853154091)
    ·
      refine ⟨38182994059757890279731137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25455329373171926853154091 38182994059757890279731137)
      ·
        refine ⟨28637245544818417709798353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38182994059757890279731137 28637245544818417709798353)
        ·
          refine ⟨21477934158613813282348765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28637245544818417709798353 21477934158613813282348765)
          ·
            refine ⟨8054225309480179980880787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21477934158613813282348765 8054225309480179980880787)
            ·
              refine ⟨12081337964220269971321181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8054225309480179980880787 12081337964220269971321181)
              ·
                refine ⟨4530501736582601239245443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12081337964220269971321181 4530501736582601239245443)
                ·
                  refine ⟨6795752604873901858868165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4530501736582601239245443 6795752604873901858868165)
                  ·
                    refine ⟨1274203613413856598537781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6795752604873901858868165 1274203613413856598537781)
                    ·
                      rfl

theorem cell22_3722254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 1, 3, 1, 4].length) (baseStart_3722254 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3722254 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3722254 prefixEnd_3722254 := by exact prefixLift 3722254
  have htrace : WordTrace (prefixWord ++ tailWord_3722254) baseStart_3722254 baseEnd_3722254 := by
    simpa [prefixWord, tailWord_3722254, baseEnd_3722254] using wordTrace_append hprefix tailTrace_3722254
  have hstable : (prefixWord ++ tailWord_3722254).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3722254).length < 2 ^ (prefixWord ++ tailWord_3722254).sum := by decide
  have hdescent : baseEnd_3722254 < baseStart_3722254 := by decide
  rcases family_descends (prefixWord ++ tailWord_3722254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3722269 : List Nat := [1, 4, 2, 2, 3, 1, 2, 1, 6]
def baseStart_3722269 : Nat := 118140960795 + 3722269 * 2 ^ 59
def prefixEnd_3722269 : Nat := 4983230072969 + 3 ^ 40 * 3722269 * 2
def baseEnd_3722269 : Nat := 424736249406800519804245

theorem tailTrace_3722269 : CollatzResearch.WordTrace tailWord_3722269 prefixEnd_3722269 424736249406800519804245 := by
  unfold tailWord_3722269
  simp only [CollatzResearch.WordTrace]
  refine ⟨135762303751862600778617861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90508202501241733852411907 135762303751862600778617861)
  ·
    refine ⟨25455431953474237645990849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 135762303751862600778617861 25455431953474237645990849)
    ·
      refine ⟨19091573965105678234493137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25455431953474237645990849 19091573965105678234493137)
      ·
        refine ⟨14318680473829258675869853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19091573965105678234493137 14318680473829258675869853)
        ·
          refine ⟨5369505177685972003451195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14318680473829258675869853 5369505177685972003451195)
          ·
            refine ⟨8054257766528958005176793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5369505177685972003451195 8054257766528958005176793)
            ·
              refine ⟨6040693324896718503882595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8054257766528958005176793 6040693324896718503882595)
              ·
                refine ⟨9061039987345077755823893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6040693324896718503882595 9061039987345077755823893)
                ·
                  refine ⟨424736249406800519804245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9061039987345077755823893 424736249406800519804245)
                  ·
                    rfl

theorem cell22_3722269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 2, 1, 6].length) (baseStart_3722269 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3722269 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3722269 prefixEnd_3722269 := by exact prefixLift 3722269
  have htrace : WordTrace (prefixWord ++ tailWord_3722269) baseStart_3722269 baseEnd_3722269 := by
    simpa [prefixWord, tailWord_3722269, baseEnd_3722269] using wordTrace_append hprefix tailTrace_3722269
  have hstable : (prefixWord ++ tailWord_3722269).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3722269).length < 2 ^ (prefixWord ++ tailWord_3722269).sum := by decide
  have hdescent : baseEnd_3722269 < baseStart_3722269 := by decide
  rcases family_descends (prefixWord ++ tailWord_3722269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3722295 : List Nat := [1, 1, 3, 1, 2, 2, 1, 1, 1, 9]
def baseStart_3722295 : Nat := 118140960795 + 3722295 * 2 ^ 59
def prefixEnd_3722295 : Nat := 4983230072969 + 3 ^ 40 * 3722295 * 2
def baseEnd_3722295 : Nat := 1274217648551746158262655

theorem tailTrace_3722295 : CollatzResearch.WordTrace tailWord_3722295 prefixEnd_3722295 1274217648551746158262655 := by
  unfold tailWord_3722295
  simp only [CollatzResearch.WordTrace]
  refine ⟨135763252049768407219064339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90508834699845604812709559 135763252049768407219064339)
  ·
    refine ⟨203644878074652610828596509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135763252049768407219064339 203644878074652610828596509)
    ·
      refine ⟨76366829277994729060723691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 203644878074652610828596509 76366829277994729060723691)
      ·
        refine ⟨114550243916992093591085537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76366829277994729060723691 114550243916992093591085537)
        ·
          refine ⟨85912682937744070193314153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114550243916992093591085537 85912682937744070193314153)
          ·
            refine ⟨64434512203308052644985615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85912682937744070193314153 64434512203308052644985615)
            ·
              refine ⟨96651768304962078967478423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64434512203308052644985615 96651768304962078967478423)
              ·
                refine ⟨144977652457443118451217635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96651768304962078967478423 144977652457443118451217635)
                ·
                  refine ⟨217466478686164677676826453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 144977652457443118451217635 217466478686164677676826453)
                  ·
                    refine ⟨1274217648551746158262655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 217466478686164677676826453 1274217648551746158262655)
                    ·
                      rfl

theorem cell22_3722295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 1, 1, 9].length) (baseStart_3722295 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3722295 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3722295 prefixEnd_3722295 := by exact prefixLift 3722295
  have htrace : WordTrace (prefixWord ++ tailWord_3722295) baseStart_3722295 baseEnd_3722295 := by
    simpa [prefixWord, tailWord_3722295, baseEnd_3722295] using wordTrace_append hprefix tailTrace_3722295
  have hstable : (prefixWord ++ tailWord_3722295).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3722295).length < 2 ^ (prefixWord ++ tailWord_3722295).sum := by decide
  have hdescent : baseEnd_3722295 < baseStart_3722295 := by decide
  rcases family_descends (prefixWord ++ tailWord_3722295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3722297 : List Nat := [1, 2, 1, 5, 2, 2, 1, 8]
def baseStart_3722297 : Nat := 118140960795 + 3722297 * 2 ^ 59
def prefixEnd_3722297 : Nat := 4983230072969 + 3 ^ 40 * 3722297 * 2
def baseEnd_3722297 : Nat := 141579814799179868856961

theorem tailTrace_3722297 : CollatzResearch.WordTrace tailWord_3722297 prefixEnd_3722297 141579814799179868856961 := by
  unfold tailWord_3722297
  simp only [CollatzResearch.WordTrace]
  refine ⟨135763324995761161560637145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90508883330507441040424763 135763324995761161560637145)
  ·
    refine ⟨101822493746820871170477859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135763324995761161560637145 101822493746820871170477859)
    ·
      refine ⟨152733740620231306755716789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101822493746820871170477859 152733740620231306755716789)
      ·
        refine ⟨14318788183146685008348449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 152733740620231306755716789 14318788183146685008348449)
        ·
          refine ⟨10739091137360013756261337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14318788183146685008348449 10739091137360013756261337)
          ·
            refine ⟨8054318353020010317196003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10739091137360013756261337 8054318353020010317196003)
            ·
              refine ⟨12081477529530015475794005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8054318353020010317196003 12081477529530015475794005)
              ·
                refine ⟨141579814799179868856961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12081477529530015475794005 141579814799179868856961)
                ·
                  rfl

theorem cell22_3722297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 1, 8].length) (baseStart_3722297 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3722297 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3722297 prefixEnd_3722297 := by exact prefixLift 3722297
  have htrace : WordTrace (prefixWord ++ tailWord_3722297) baseStart_3722297 baseEnd_3722297 := by
    simpa [prefixWord, tailWord_3722297, baseEnd_3722297] using wordTrace_append hprefix tailTrace_3722297
  have hstable : (prefixWord ++ tailWord_3722297).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3722297).length < 2 ^ (prefixWord ++ tailWord_3722297).sum := by decide
  have hdescent : baseEnd_3722297 < baseStart_3722297 := by decide
  rcases family_descends (prefixWord ++ tailWord_3722297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3722376 : List Nat := [2, 1, 3, 4, 2, 1, 2, 2, 5]
def baseStart_3722376 : Nat := 118140960795 + 3722376 * 2 ^ 59
def prefixEnd_3722376 : Nat := 4983230072969 + 3 ^ 40 * 3722376 * 2
def baseEnd_3722376 : Nat := 424748458835696315662469

theorem tailTrace_3722376 : CollatzResearch.WordTrace tailWord_3722376 prefixEnd_3722376 424748458835696315662469 := by
  unfold tailWord_3722376
  simp only [CollatzResearch.WordTrace]
  refine ⟨67883103181237479026381491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90510804241649972035175321 67883103181237479026381491)
  ·
    refine ⟨101824654771856218539572237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67883103181237479026381491 101824654771856218539572237)
    ·
      refine ⟨38184245539446081952339589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101824654771856218539572237 38184245539446081952339589)
      ·
        refine ⟨7159546038646140366063673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38184245539446081952339589 7159546038646140366063673)
        ·
          refine ⟨5369659528984605274547755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7159546038646140366063673 5369659528984605274547755)
          ·
            refine ⟨8054489293476907911821633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5369659528984605274547755 8054489293476907911821633)
            ·
              refine ⟨6040866970107680933866225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8054489293476907911821633 6040866970107680933866225)
              ·
                refine ⟨4530650227580760700399669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6040866970107680933866225 4530650227580760700399669)
                ·
                  refine ⟨424748458835696315662469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4530650227580760700399669 424748458835696315662469)
                  ·
                    rfl

theorem cell22_3722376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 2, 2, 5].length) (baseStart_3722376 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3722376 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3722376 prefixEnd_3722376 := by exact prefixLift 3722376
  have htrace : WordTrace (prefixWord ++ tailWord_3722376) baseStart_3722376 baseEnd_3722376 := by
    simpa [prefixWord, tailWord_3722376, baseEnd_3722376] using wordTrace_append hprefix tailTrace_3722376
  have hstable : (prefixWord ++ tailWord_3722376).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3722376).length < 2 ^ (prefixWord ++ tailWord_3722376).sum := by decide
  have hdescent : baseEnd_3722376 < baseStart_3722376 := by decide
  rcases family_descends (prefixWord ++ tailWord_3722376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3722404 : List Nat := [2, 3, 1, 2, 3, 2, 1, 2, 6]
def baseStart_3722404 : Nat := 118140960795 + 3722404 * 2 ^ 59
def prefixEnd_3722404 : Nat := 4983230072969 + 3 ^ 40 * 3722404 * 2
def baseEnd_3722404 : Nat := 424751653826435402429107

theorem tailTrace_3722404 : CollatzResearch.WordTrace tailWord_3722404 prefixEnd_3722404 424751653826435402429107 := by
  unfold tailWord_3722404
  simp only [CollatzResearch.WordTrace]
  refine ⟨67883613803186759417391133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90511485070915679223188177 67883613803186759417391133)
  ·
    refine ⟨25456355176195034781521675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67883613803186759417391133 25456355176195034781521675)
    ·
      refine ⟨38184532764292552172282513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25456355176195034781521675 38184532764292552172282513)
      ·
        refine ⟨28638399573219414129211885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38184532764292552172282513 28638399573219414129211885)
        ·
          refine ⟨10739399839957280298454457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28638399573219414129211885 10739399839957280298454457)
          ·
            refine ⟨8054549879967960223840843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10739399839957280298454457 8054549879967960223840843)
            ·
              refine ⟨12081824819951940335761265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8054549879967960223840843 12081824819951940335761265)
              ·
                refine ⟨9061368614963955251820949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12081824819951940335761265 9061368614963955251820949)
                ·
                  refine ⟨424751653826435402429107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9061368614963955251820949 424751653826435402429107)
                  ·
                    rfl

theorem cell22_3722404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 1, 2, 6].length) (baseStart_3722404 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3722404 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3722404 prefixEnd_3722404 := by exact prefixLift 3722404
  have htrace : WordTrace (prefixWord ++ tailWord_3722404) baseStart_3722404 baseEnd_3722404 := by
    simpa [prefixWord, tailWord_3722404, baseEnd_3722404] using wordTrace_append hprefix tailTrace_3722404
  have hstable : (prefixWord ++ tailWord_3722404).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3722404).length < 2 ^ (prefixWord ++ tailWord_3722404).sum := by decide
  have hdescent : baseEnd_3722404 < baseStart_3722404 := by decide
  rcases family_descends (prefixWord ++ tailWord_3722404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3722554 : List Nat := [3, 1, 1, 1, 4, 1, 1, 2, 3, 5]
def baseStart_3722554 : Nat := 118140960795 + 3722554 * 2 ^ 59
def prefixEnd_3722554 : Nat := 4983230072969 + 3 ^ 40 * 3722554 * 2
def baseEnd_3722554 : Nat := 1274306309544755816036861

theorem tailTrace_3722554 : CollatzResearch.WordTrace tailWord_3722554 prefixEnd_3722554 1274306309544755816036861 := by
  unfold tailWord_3722554
  simp only [CollatzResearch.WordTrace]
  refine ⟨33943174638957523613185679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90515132370553396301828477 33943174638957523613185679)
  ·
    refine ⟨50914761958436285419778519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33943174638957523613185679 50914761958436285419778519)
    ·
      refine ⟨76372142937654428129667779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50914761958436285419778519 76372142937654428129667779)
      ·
        refine ⟨114558214406481642194501669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76372142937654428129667779 114558214406481642194501669)
        ·
          refine ⟨21479665201215307911469063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 114558214406481642194501669 21479665201215307911469063)
          ·
            refine ⟨32219497801822961867203595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21479665201215307911469063 32219497801822961867203595)
            ·
              refine ⟨48329246702734442800805393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32219497801822961867203595 48329246702734442800805393)
              ·
                refine ⟨36246935027050832100604045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48329246702734442800805393 36246935027050832100604045)
                ·
                  refine ⟨13592600635144062037726517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36246935027050832100604045 13592600635144062037726517)
                  ·
                    refine ⟨1274306309544755816036861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13592600635144062037726517 1274306309544755816036861)
                    ·
                      rfl

theorem cell22_3722554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 2, 3, 5].length) (baseStart_3722554 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3722554 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3722554 prefixEnd_3722554 := by exact prefixLift 3722554
  have htrace : WordTrace (prefixWord ++ tailWord_3722554) baseStart_3722554 baseEnd_3722554 := by
    simpa [prefixWord, tailWord_3722554, baseEnd_3722554] using wordTrace_append hprefix tailTrace_3722554
  have hstable : (prefixWord ++ tailWord_3722554).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3722554).length < 2 ^ (prefixWord ++ tailWord_3722554).sum := by decide
  have hdescent : baseEnd_3722554 < baseStart_3722554 := by decide
  rcases family_descends (prefixWord ++ tailWord_3722554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3722569 : List Nat := [1, 2, 1, 1, 2, 3, 2, 2, 4, 4]
def baseStart_3722569 : Nat := 118140960795 + 3722569 * 2 ^ 59
def prefixEnd_3722569 : Nat := 4983230072969 + 3 ^ 40 * 3722569 * 2
def baseEnd_3722569 : Nat := 1274311444351300776911815

theorem tailTrace_3722569 : CollatzResearch.WordTrace tailWord_3722569 prefixEnd_3722569 1274311444351300776911815 := by
  unfold tailWord_3722569
  simp only [CollatzResearch.WordTrace]
  refine ⟨135773245650775752014538761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90515497100517168009692507 135773245650775752014538761)
  ·
    refine ⟨101829934238081814010904071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135773245650775752014538761 101829934238081814010904071)
    ·
      refine ⟨152744901357122721016356107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101829934238081814010904071 152744901357122721016356107)
      ·
        refine ⟨229117352035684081524534161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152744901357122721016356107 229117352035684081524534161)
        ·
          refine ⟨171838014026763061143400621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 229117352035684081524534161 171838014026763061143400621)
          ·
            refine ⟨64439255260036147928775233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 171838014026763061143400621 64439255260036147928775233)
            ·
              refine ⟨48329441445027110946581425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64439255260036147928775233 48329441445027110946581425)
              ·
                refine ⟨36247081083770333209936069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48329441445027110946581425 36247081083770333209936069)
                ·
                  refine ⟨6796327703206937476863013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36247081083770333209936069 6796327703206937476863013)
                  ·
                    refine ⟨1274311444351300776911815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6796327703206937476863013 1274311444351300776911815)
                    ·
                      rfl

theorem cell22_3722569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 2, 4, 4].length) (baseStart_3722569 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3722569 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3722569 prefixEnd_3722569 := by exact prefixLift 3722569
  have htrace : WordTrace (prefixWord ++ tailWord_3722569) baseStart_3722569 baseEnd_3722569 := by
    simpa [prefixWord, tailWord_3722569, baseEnd_3722569] using wordTrace_append hprefix tailTrace_3722569
  have hstable : (prefixWord ++ tailWord_3722569).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3722569).length < 2 ^ (prefixWord ++ tailWord_3722569).sum := by decide
  have hdescent : baseEnd_3722569 < baseStart_3722569 := by decide
  rcases family_descends (prefixWord ++ tailWord_3722569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3722586 : List Nat := [3, 1, 1, 2, 1, 2, 5, 1, 2, 4]
def baseStart_3722586 : Nat := 118140960795 + 3722586 * 2 ^ 59
def prefixEnd_3722586 : Nat := 4983230072969 + 3 ^ 40 * 3722586 * 2
def baseEnd_3722586 : Nat := 1274317263798718399236763

theorem tailTrace_3722586 : CollatzResearch.WordTrace tailWord_3722586 prefixEnd_3722586 1274317263798718399236763 := by
  unfold tailWord_3722586
  simp only [CollatzResearch.WordTrace]
  refine ⟨33943466422928540979476903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90515910461142775945271741 33943466422928540979476903)
  ·
    refine ⟨50915199634392811469215355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33943466422928540979476903 50915199634392811469215355)
    ·
      refine ⟨76372799451589217203823033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50915199634392811469215355 76372799451589217203823033)
      ·
        refine ⟨57279599588691912902867275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76372799451589217203823033 57279599588691912902867275)
        ·
          refine ⟨85919399383037869354300913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57279599588691912902867275 85919399383037869354300913)
          ·
            refine ⟨64439549537278402015725685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85919399383037869354300913 64439549537278402015725685)
            ·
              refine ⟨6041207769119850188974283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 64439549537278402015725685 6041207769119850188974283)
              ·
                refine ⟨9061811653679775283461425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6041207769119850188974283 9061811653679775283461425)
                ·
                  refine ⟨6796358740259831462596069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9061811653679775283461425 6796358740259831462596069)
                  ·
                    refine ⟨1274317263798718399236763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6796358740259831462596069 1274317263798718399236763)
                    ·
                      rfl

theorem cell22_3722586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 5, 1, 2, 4].length) (baseStart_3722586 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3722586 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3722586 prefixEnd_3722586 := by exact prefixLift 3722586
  have htrace : WordTrace (prefixWord ++ tailWord_3722586) baseStart_3722586 baseEnd_3722586 := by
    simpa [prefixWord, tailWord_3722586, baseEnd_3722586] using wordTrace_append hprefix tailTrace_3722586
  have hstable : (prefixWord ++ tailWord_3722586).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3722586).length < 2 ^ (prefixWord ++ tailWord_3722586).sum := by decide
  have hdescent : baseEnd_3722586 < baseStart_3722586 := by decide
  rcases family_descends (prefixWord ++ tailWord_3722586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3722605 : List Nat := [1, 5, 1, 1, 1, 5, 1, 2, 2, 3]
def baseStart_3722605 : Nat := 118140960795 + 3722605 * 2 ^ 59
def prefixEnd_3722605 : Nat := 4983230072969 + 3 ^ 40 * 3722605 * 2
def baseEnd_3722605 : Nat := 1274323767887008683011705

theorem tailTrace_3722605 : CollatzResearch.WordTrace tailWord_3722605 prefixEnd_3722605 1274323767887008683011705 := by
  unfold tailWord_3722605
  simp only [CollatzResearch.WordTrace]
  refine ⟨135774558678645330162849269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90516372452430220108566179 135774558678645330162849269)
  ·
    refine ⟨12728864876122999702767119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 135774558678645330162849269 12728864876122999702767119)
    ·
      refine ⟨19093297314184499554150679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12728864876122999702767119 19093297314184499554150679)
      ·
        refine ⟨28639945971276749331226019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19093297314184499554150679 28639945971276749331226019)
        ·
          refine ⟨42959918956915123996839029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28639945971276749331226019 42959918956915123996839029)
          ·
            refine ⟨4027492402210792874703659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 42959918956915123996839029 4027492402210792874703659)
            ·
              refine ⟨6041238603316189312055489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4027492402210792874703659 6041238603316189312055489)
              ·
                refine ⟨4530928952487141984041617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6041238603316189312055489 4530928952487141984041617)
                ·
                  refine ⟨3398196714365356488031213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4530928952487141984041617 3398196714365356488031213)
                  ·
                    refine ⟨1274323767887008683011705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3398196714365356488031213 1274323767887008683011705)
                    ·
                      rfl

theorem cell22_3722605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 5, 1, 2, 2, 3].length) (baseStart_3722605 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3722605 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3722605 prefixEnd_3722605 := by exact prefixLift 3722605
  have htrace : WordTrace (prefixWord ++ tailWord_3722605) baseStart_3722605 baseEnd_3722605 := by
    simpa [prefixWord, tailWord_3722605, baseEnd_3722605] using wordTrace_append hprefix tailTrace_3722605
  have hstable : (prefixWord ++ tailWord_3722605).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3722605).length < 2 ^ (prefixWord ++ tailWord_3722605).sum := by decide
  have hdescent : baseEnd_3722605 < baseStart_3722605 := by decide
  rcases family_descends (prefixWord ++ tailWord_3722605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3722622 : List Nat := [4, 2, 3, 2, 1, 2, 1, 1, 1, 5]
def baseStart_3722622 : Nat := 118140960795 + 3722622 * 2 ^ 59
def prefixEnd_3722622 : Nat := 4983230072969 + 3 ^ 40 * 3722622 * 2
def baseEnd_3722622 : Nat := 1274329587334426305336653

theorem tailTrace_3722622 : CollatzResearch.WordTrace tailWord_3722622 prefixEnd_3722622 1274329587334426305336653 := by
  unfold tailWord_3722622
  simp only [CollatzResearch.WordTrace]
  refine ⟨16971897339947967758277265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 90516785813055828044145413 16971897339947967758277265)
  ·
    refine ⟨12728923004960975818707949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16971897339947967758277265 12728923004960975818707949)
    ·
      refine ⟨4773346126860365932015481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12728923004960975818707949 4773346126860365932015481)
      ·
        refine ⟨3580009595145274449011611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4773346126860365932015481 3580009595145274449011611)
        ·
          refine ⟨5370014392717911673517417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3580009595145274449011611 5370014392717911673517417)
          ·
            refine ⟨4027510794538433755138063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5370014392717911673517417 4027510794538433755138063)
            ·
              refine ⟨6041266191807650632707095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4027510794538433755138063 6041266191807650632707095)
              ·
                refine ⟨9061899287711475949060643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6041266191807650632707095 9061899287711475949060643)
                ·
                  refine ⟨13592848931567213923590965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9061899287711475949060643 13592848931567213923590965)
                  ·
                    refine ⟨1274329587334426305336653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13592848931567213923590965 1274329587334426305336653)
                    ·
                      rfl

theorem cell22_3722622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 2, 1, 1, 1, 5].length) (baseStart_3722622 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3722622 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3722622 prefixEnd_3722622 := by exact prefixLift 3722622
  have htrace : WordTrace (prefixWord ++ tailWord_3722622) baseStart_3722622 baseEnd_3722622 := by
    simpa [prefixWord, tailWord_3722622, baseEnd_3722622] using wordTrace_append hprefix tailTrace_3722622
  have hstable : (prefixWord ++ tailWord_3722622).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3722622).length < 2 ^ (prefixWord ++ tailWord_3722622).sum := by decide
  have hdescent : baseEnd_3722622 < baseStart_3722622 := by decide
  rcases family_descends (prefixWord ++ tailWord_3722622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3722725 : List Nat := [1, 3, 1, 5, 1, 2, 1, 4, 4]
def baseStart_3722725 : Nat := 118140960795 + 3722725 * 2 ^ 59
def prefixEnd_3722725 : Nat := 4983230072969 + 3 ^ 40 * 3722725 * 2
def baseEnd_3722725 : Nat := 424788282113122790003779

theorem tailTrace_3722725 : CollatzResearch.WordTrace tailWord_3722725 prefixEnd_3722725 424788282113122790003779 := by
  unfold tailWord_3722725
  simp only [CollatzResearch.WordTrace]
  refine ⟨135778935438210590657217629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90519290292140393771478419 135778935438210590657217629)
  ·
    refine ⟨50917100789328971496456611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135778935438210590657217629 50917100789328971496456611)
    ·
      refine ⟨76375651183993457244684917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50917100789328971496456611 76375651183993457244684917)
      ·
        refine ⟨7160217298499386616689211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 76375651183993457244684917 7160217298499386616689211)
        ·
          refine ⟨10740325947749079925033817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7160217298499386616689211 10740325947749079925033817)
          ·
            refine ⟨8055244460811809943775363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10740325947749079925033817 8055244460811809943775363)
            ·
              refine ⟨12082866691217714915663045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8055244460811809943775363 12082866691217714915663045)
              ·
                refine ⟨2265537504603321546686821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12082866691217714915663045 2265537504603321546686821)
                ·
                  refine ⟨424788282113122790003779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2265537504603321546686821 424788282113122790003779)
                  ·
                    rfl

theorem cell22_3722725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 1, 4, 4].length) (baseStart_3722725 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3722725 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3722725 prefixEnd_3722725 := by exact prefixLift 3722725
  have htrace : WordTrace (prefixWord ++ tailWord_3722725) baseStart_3722725 baseEnd_3722725 := by
    simpa [prefixWord, tailWord_3722725, baseEnd_3722725] using wordTrace_append hprefix tailTrace_3722725
  have hstable : (prefixWord ++ tailWord_3722725).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3722725).length < 2 ^ (prefixWord ++ tailWord_3722725).sum := by decide
  have hdescent : baseEnd_3722725 < baseStart_3722725 := by decide
  rcases family_descends (prefixWord ++ tailWord_3722725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3722736 : List Nat := [2, 1, 1, 1, 3, 4, 3, 7]
def baseStart_3722736 : Nat := 118140960795 + 3722736 * 2 ^ 59
def prefixEnd_3722736 : Nat := 4983230072969 + 3 ^ 40 * 3722736 * 2
def baseEnd_3722736 : Nat := 141596512429352000887367

theorem tailTrace_3722736 : CollatzResearch.WordTrace tailWord_3722736 prefixEnd_3722736 141596512429352000887367 := by
  unfold tailWord_3722736
  simp only [CollatzResearch.WordTrace]
  refine ⟨67889668320585369767934031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90519557760780493023912041 67889668320585369767934031)
  ·
    refine ⟨101834502480878054651901047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67889668320585369767934031 101834502480878054651901047)
    ·
      refine ⟨152751753721317081977851571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101834502480878054651901047 152751753721317081977851571)
      ·
        refine ⟨229127630581975622966777357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152751753721317081977851571 229127630581975622966777357)
        ·
          refine ⟨85922861468240858612541509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 229127630581975622966777357 85922861468240858612541509)
          ·
            refine ⟨16110536525295160989851533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 85922861468240858612541509 16110536525295160989851533)
            ·
              refine ⟨6041451196985685371194325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16110536525295160989851533 6041451196985685371194325)
              ·
                refine ⟨141596512429352000887367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6041451196985685371194325 141596512429352000887367)
                ·
                  rfl

theorem cell22_3722736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 3, 7].length) (baseStart_3722736 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3722736 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3722736 prefixEnd_3722736 := by exact prefixLift 3722736
  have htrace : WordTrace (prefixWord ++ tailWord_3722736) baseStart_3722736 baseEnd_3722736 := by
    simpa [prefixWord, tailWord_3722736, baseEnd_3722736] using wordTrace_append hprefix tailTrace_3722736
  have hstable : (prefixWord ++ tailWord_3722736).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3722736).length < 2 ^ (prefixWord ++ tailWord_3722736).sum := by decide
  have hdescent : baseEnd_3722736 < baseStart_3722736 := by decide
  rcases family_descends (prefixWord ++ tailWord_3722736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3722785 : List Nat := [1, 2, 3, 2, 2, 3, 2, 1, 3, 3]
def baseStart_3722785 : Nat := 118140960795 + 3722785 * 2 ^ 59
def prefixEnd_3722785 : Nat := 4983230072969 + 3 ^ 40 * 3722785 * 2
def baseEnd_3722785 : Nat := 1274385385565548213511153

theorem tailTrace_3722785 : CollatzResearch.WordTrace tailWord_3722785 prefixEnd_3722785 1274385385565548213511153 := by
  unfold tailWord_3722785
  simp only [CollatzResearch.WordTrace]
  refine ⟨135781123817993220904401809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90520749211995480602934539 135781123817993220904401809)
  ·
    refine ⟨101835842863494915678301357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135781123817993220904401809 101835842863494915678301357)
    ·
      refine ⟨38188441073810593379363009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101835842863494915678301357 38188441073810593379363009)
      ·
        refine ⟨28641330805357945034522257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38188441073810593379363009 28641330805357945034522257)
        ·
          refine ⟨21480998104018458775891693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28641330805357945034522257 21480998104018458775891693)
          ·
            refine ⟨8055374289006922040959385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21480998104018458775891693 8055374289006922040959385)
            ·
              refine ⟨6041530716755191530719539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8055374289006922040959385 6041530716755191530719539)
              ·
                refine ⟨9062296075132787296079309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6041530716755191530719539 9062296075132787296079309)
                ·
                  refine ⟨3398361028174795236029741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9062296075132787296079309 3398361028174795236029741)
                  ·
                    refine ⟨1274385385565548213511153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3398361028174795236029741 1274385385565548213511153)
                    ·
                      rfl

theorem cell22_3722785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 2, 1, 3, 3].length) (baseStart_3722785 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3722785 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3722785 prefixEnd_3722785 := by exact prefixLift 3722785
  have htrace : WordTrace (prefixWord ++ tailWord_3722785) baseStart_3722785 baseEnd_3722785 := by
    simpa [prefixWord, tailWord_3722785, baseEnd_3722785] using wordTrace_append hprefix tailTrace_3722785
  have hstable : (prefixWord ++ tailWord_3722785).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3722785).length < 2 ^ (prefixWord ++ tailWord_3722785).sum := by decide
  have hdescent : baseEnd_3722785 < baseStart_3722785 := by decide
  rcases family_descends (prefixWord ++ tailWord_3722785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3722888 : List Nat := [2, 1, 3, 5, 11]
def baseStart_3722888 : Nat := 118140960795 + 3722888 * 2 ^ 59
def prefixEnd_3722888 : Nat := 4983230072969 + 3 ^ 40 * 3722888 * 2
def baseEnd_3722888 : Nat := 5244529401524651350559

theorem tailTrace_3722888 : CollatzResearch.WordTrace tailWord_3722888 prefixEnd_3722888 5244529401524651350559 := by
  unfold tailWord_3722888
  simp only [CollatzResearch.WordTrace]
  refine ⟨67892440268310034747700659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90523253691080046330267545 67892440268310034747700659)
  ·
    refine ⟨101838660402465052121550989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67892440268310034747700659 101838660402465052121550989)
    ·
      refine ⟨38189497650924394545581621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101838660402465052121550989 38189497650924394545581621)
      ·
        refine ⟨3580265404774161988648277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 38189497650924394545581621 3580265404774161988648277)
        ·
          refine ⟨5244529401524651350559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 3580265404774161988648277 5244529401524651350559)
          ·
            rfl

theorem cell22_3722888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 11].length) (baseStart_3722888 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3722888 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3722888 prefixEnd_3722888 := by exact prefixLift 3722888
  have htrace : WordTrace (prefixWord ++ tailWord_3722888) baseStart_3722888 baseEnd_3722888 := by
    simpa [prefixWord, tailWord_3722888, baseEnd_3722888] using wordTrace_append hprefix tailTrace_3722888
  have hstable : (prefixWord ++ tailWord_3722888).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3722888).length < 2 ^ (prefixWord ++ tailWord_3722888).sum := by decide
  have hdescent : baseEnd_3722888 < baseStart_3722888 := by decide
  rcases family_descends (prefixWord ++ tailWord_3722888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3722890 : List Nat := [3, 1, 2, 3, 2, 1, 2, 2, 2, 4]
def baseStart_3722890 : Nat := 118140960795 + 3722890 * 2 ^ 59
def prefixEnd_3722890 : Nat := 4983230072969 + 3 ^ 40 * 3722890 * 2
def baseEnd_3722890 : Nat := 1274421329211362939635831

theorem tailTrace_3722890 : CollatzResearch.WordTrace tailWord_3722890 prefixEnd_3722890 1274421329211362939635831 := by
  unfold tailWord_3722890
  simp only [CollatzResearch.WordTrace]
  refine ⟨33946238370653205959243531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90523302321741882557982749 33946238370653205959243531)
  ·
    refine ⟨50919357555979808938865297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33946238370653205959243531 50919357555979808938865297)
    ·
      refine ⟨38189518166984856704148973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50919357555979808938865297 38189518166984856704148973)
      ·
        refine ⟨14321069312619321264055865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38189518166984856704148973 14321069312619321264055865)
        ·
          refine ⟨10740801984464490948041899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14321069312619321264055865 10740801984464490948041899)
          ·
            refine ⟨16111202976696736422062849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10740801984464490948041899 16111202976696736422062849)
            ·
              refine ⟨12083402232522552316547137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16111202976696736422062849 12083402232522552316547137)
              ·
                refine ⟨9062551674391914237410353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12083402232522552316547137 9062551674391914237410353)
                ·
                  refine ⟨6796913755793935678057765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9062551674391914237410353 6796913755793935678057765)
                  ·
                    refine ⟨1274421329211362939635831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6796913755793935678057765 1274421329211362939635831)
                    ·
                      rfl

theorem cell22_3722890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 2, 2, 2, 4].length) (baseStart_3722890 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3722890 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3722890 prefixEnd_3722890 := by exact prefixLift 3722890
  have htrace : WordTrace (prefixWord ++ tailWord_3722890) baseStart_3722890 baseEnd_3722890 := by
    simpa [prefixWord, tailWord_3722890, baseEnd_3722890] using wordTrace_append hprefix tailTrace_3722890
  have hstable : (prefixWord ++ tailWord_3722890).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3722890).length < 2 ^ (prefixWord ++ tailWord_3722890).sum := by decide
  have hdescent : baseEnd_3722890 < baseStart_3722890 := by decide
  rcases family_descends (prefixWord ++ tailWord_3722890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3722894 : List Nat := [4, 1, 1, 3, 1, 4, 2, 2, 4]
def baseStart_3722894 : Nat := 118140960795 + 3722894 * 2 ^ 59
def prefixEnd_3722894 : Nat := 4983230072969 + 3 ^ 40 * 3722894 * 2
def baseEnd_3722894 : Nat := 424807566164369420845273

theorem tailTrace_3722894 : CollatzResearch.WordTrace tailWord_3722894 prefixEnd_3722894 424807566164369420845273 := by
  unfold tailWord_3722894
  simp only [CollatzResearch.WordTrace]
  refine ⟨16973137421824791565014967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 90523399583065555013413157 16973137421824791565014967)
  ·
    refine ⟨25459706132737187347522451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16973137421824791565014967 25459706132737187347522451)
    ·
      refine ⟨38189559199105781021283677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25459706132737187347522451 38189559199105781021283677)
      ·
        refine ⟨14321084699664667882981379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38189559199105781021283677 14321084699664667882981379)
        ·
          refine ⟨21481627049497001824472069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14321084699664667882981379 21481627049497001824472069)
          ·
            refine ⟨4027805071780687842088513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21481627049497001824472069 4027805071780687842088513)
            ·
              refine ⟨3020853803835515881566385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4027805071780687842088513 3020853803835515881566385)
              ·
                refine ⟨2265640352876636911174789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3020853803835515881566385 2265640352876636911174789)
                ·
                  refine ⟨424807566164369420845273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2265640352876636911174789 424807566164369420845273)
                  ·
                    rfl

theorem cell22_3722894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 4, 2, 2, 4].length) (baseStart_3722894 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3722894 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3722894 prefixEnd_3722894 := by exact prefixLift 3722894
  have htrace : WordTrace (prefixWord ++ tailWord_3722894) baseStart_3722894 baseEnd_3722894 := by
    simpa [prefixWord, tailWord_3722894, baseEnd_3722894] using wordTrace_append hprefix tailTrace_3722894
  have hstable : (prefixWord ++ tailWord_3722894).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3722894).length < 2 ^ (prefixWord ++ tailWord_3722894).sum := by decide
  have hdescent : baseEnd_3722894 < baseStart_3722894 := by decide
  rcases family_descends (prefixWord ++ tailWord_3722894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3722937 : List Nat := [1, 2, 1, 4, 1, 1, 3, 5, 1, 3]
def baseStart_3722937 : Nat := 118140960795 + 3722937 * 2 ^ 59
def prefixEnd_3722937 : Nat := 4983230072969 + 3 ^ 40 * 3722937 * 2
def baseEnd_3722937 : Nat := 1274437418271870483710687

theorem tailTrace_3722937 : CollatzResearch.WordTrace tailWord_3722937 prefixEnd_3722937 1274437418271870483710687 := by
  unfold tailWord_3722937
  simp only [CollatzResearch.WordTrace]
  refine ⟨135786667713442550863935065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90524445142295033909290043 135786667713442550863935065)
  ·
    refine ⟨101840000785081913147951299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135786667713442550863935065 101840000785081913147951299)
    ·
      refine ⟨152760001177622869721926949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101840000785081913147951299 152760001177622869721926949)
      ·
        refine ⟨28642500220804288072861303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 152760001177622869721926949 28642500220804288072861303)
        ·
          refine ⟨42963750331206432109291955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28642500220804288072861303 42963750331206432109291955)
          ·
            refine ⟨64445625496809648163937933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42963750331206432109291955 64445625496809648163937933)
            ·
              refine ⟨24167109561303618061476725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64445625496809648163937933 24167109561303618061476725)
              ·
                refine ⟨2265666521372214193263443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24167109561303618061476725 2265666521372214193263443)
                ·
                  refine ⟨3398499782058321289895165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2265666521372214193263443 3398499782058321289895165)
                  ·
                    refine ⟨1274437418271870483710687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3398499782058321289895165 1274437418271870483710687)
                    ·
                      rfl

theorem cell22_3722937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 3, 5, 1, 3].length) (baseStart_3722937 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3722937 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3722937 prefixEnd_3722937 := by exact prefixLift 3722937
  have htrace : WordTrace (prefixWord ++ tailWord_3722937) baseStart_3722937 baseEnd_3722937 := by
    simpa [prefixWord, tailWord_3722937, baseEnd_3722937] using wordTrace_append hprefix tailTrace_3722937
  have hstable : (prefixWord ++ tailWord_3722937).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3722937).length < 2 ^ (prefixWord ++ tailWord_3722937).sum := by decide
  have hdescent : baseEnd_3722937 < baseStart_3722937 := by decide
  rcases family_descends (prefixWord ++ tailWord_3722937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3723012 : List Nat := [2, 3, 2, 2, 1, 4, 1, 1, 6]
def baseStart_3723012 : Nat := 118140960795 + 3723012 * 2 ^ 59
def prefixEnd_3723012 : Nat := 4983230072969 + 3 ^ 40 * 3723012 * 2
def baseEnd_3723012 : Nat := 424821030768198429361819

theorem tailTrace_3723012 : CollatzResearch.WordTrace tailWord_3723012 prefixEnd_3723012 424821030768198429361819 := by
  unfold tailWord_3723012
  simp only [CollatzResearch.WordTrace]
  refine ⟨67894701594085419336457645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90526268792113892448610193 67894701594085419336457645)
  ·
    refine ⟨25460513097782032251171617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67894701594085419336457645 25460513097782032251171617)
    ·
      refine ⟨19095384823336524188378713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25460513097782032251171617 19095384823336524188378713)
      ·
        refine ⟨14321538617502393141284035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19095384823336524188378713 14321538617502393141284035)
        ·
          refine ⟨21482307926253589711926053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14321538617502393141284035 21482307926253589711926053)
          ·
            refine ⟨4027932736172548070986135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21482307926253589711926053 4027932736172548070986135)
            ·
              refine ⟨6041899104258822106479203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4027932736172548070986135 6041899104258822106479203)
              ·
                refine ⟨9062848656388233159718805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6041899104258822106479203 9062848656388233159718805)
                ·
                  refine ⟨424821030768198429361819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9062848656388233159718805 424821030768198429361819)
                  ·
                    rfl

theorem cell22_3723012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 4, 1, 1, 6].length) (baseStart_3723012 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3723012 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3723012 prefixEnd_3723012 := by exact prefixLift 3723012
  have htrace : WordTrace (prefixWord ++ tailWord_3723012) baseStart_3723012 baseEnd_3723012 := by
    simpa [prefixWord, tailWord_3723012, baseEnd_3723012] using wordTrace_append hprefix tailTrace_3723012
  have hstable : (prefixWord ++ tailWord_3723012).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3723012).length < 2 ^ (prefixWord ++ tailWord_3723012).sum := by decide
  have hdescent : baseEnd_3723012 < baseStart_3723012 := by decide
  rcases family_descends (prefixWord ++ tailWord_3723012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3723042 : List Nat := [3, 3, 1, 1, 2, 1, 4, 1, 2, 4]
def baseStart_3723042 : Nat := 118140960795 + 3723042 * 2 ^ 59
def prefixEnd_3723042 : Nat := 4983230072969 + 3 ^ 40 * 3723042 * 2
def baseEnd_3723042 : Nat := 1274473361917685209835365

theorem tailTrace_3723042 : CollatzResearch.WordTrace tailWord_3723042 prefixEnd_3723042 1274473361917685209835365 := by
  unfold tailWord_3723042
  simp only [CollatzResearch.WordTrace]
  refine ⟨33947624344515538449126845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90526998252041435864338253 33947624344515538449126845)
  ·
    refine ⟨12730359129193326918422567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33947624344515538449126845 12730359129193326918422567)
    ·
      refine ⟨19095538693789990377633851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12730359129193326918422567 19095538693789990377633851)
      ·
        refine ⟨28643308040684985566450777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19095538693789990377633851 28643308040684985566450777)
        ·
          refine ⟨21482481030513739174838083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28643308040684985566450777 21482481030513739174838083)
          ·
            refine ⟨32223721545770608762257125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21482481030513739174838083 32223721545770608762257125)
            ·
              refine ⟨6041947789831989142923211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32223721545770608762257125 6041947789831989142923211)
              ·
                refine ⟨9062921684747983714384817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6041947789831989142923211 9062921684747983714384817)
                ·
                  refine ⟨6797191263560987785788613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9062921684747983714384817 6797191263560987785788613)
                  ·
                    refine ⟨1274473361917685209835365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6797191263560987785788613 1274473361917685209835365)
                    ·
                      rfl

theorem cell22_3723042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 4, 1, 2, 4].length) (baseStart_3723042 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3723042 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3723042 prefixEnd_3723042 := by exact prefixLift 3723042
  have htrace : WordTrace (prefixWord ++ tailWord_3723042) baseStart_3723042 baseEnd_3723042 := by
    simpa [prefixWord, tailWord_3723042, baseEnd_3723042] using wordTrace_append hprefix tailTrace_3723042
  have hstable : (prefixWord ++ tailWord_3723042).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3723042).length < 2 ^ (prefixWord ++ tailWord_3723042).sum := by decide
  have hdescent : baseEnd_3723042 < baseStart_3723042 := by decide
  rcases family_descends (prefixWord ++ tailWord_3723042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3723055 : List Nat := [1, 1, 2, 1, 2, 1, 2, 4, 5, 3]
def baseStart_3723055 : Nat := 118140960795 + 3723055 * 2 ^ 59
def prefixEnd_3723055 : Nat := 4983230072969 + 3 ^ 40 * 3723055 * 2
def baseEnd_3723055 : Nat := 1274477812083357509260325

theorem tailTrace_3723055 : CollatzResearch.WordTrace tailWord_3723055 prefixEnd_3723055 1274477812083357509260325 := by
  unfold tailWord_3723055
  simp only [CollatzResearch.WordTrace]
  refine ⟨135790971527015057016730619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90527314351343371344487079 135790971527015057016730619)
  ·
    refine ⟨203686457290522585525095929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135790971527015057016730619 203686457290522585525095929)
    ·
      refine ⟨152764842967891939143821947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 203686457290522585525095929 152764842967891939143821947)
      ·
        refine ⟨229147264451837908715732921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152764842967891939143821947 229147264451837908715732921)
        ·
          refine ⟨171860448338878431536799691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 229147264451837908715732921 171860448338878431536799691)
          ·
            refine ⟨257790672508317647305199537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 171860448338878431536799691 257790672508317647305199537)
            ·
              refine ⟨193343004381238235478899653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 257790672508317647305199537 193343004381238235478899653)
              ·
                refine ⟨36251813321482169152293685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 193343004381238235478899653 36251813321482169152293685)
                ·
                  refine ⟨3398607498888953358027533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 36251813321482169152293685 3398607498888953358027533)
                  ·
                    refine ⟨1274477812083357509260325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3398607498888953358027533 1274477812083357509260325)
                    ·
                      rfl

theorem cell22_3723055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 4, 5, 3].length) (baseStart_3723055 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3723055 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3723055 prefixEnd_3723055 := by exact prefixLift 3723055
  have htrace : WordTrace (prefixWord ++ tailWord_3723055) baseStart_3723055 baseEnd_3723055 := by
    simpa [prefixWord, tailWord_3723055, baseEnd_3723055] using wordTrace_append hprefix tailTrace_3723055
  have hstable : (prefixWord ++ tailWord_3723055).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3723055).length < 2 ^ (prefixWord ++ tailWord_3723055).sum := by decide
  have hdescent : baseEnd_3723055 < baseStart_3723055 := by decide
  rcases family_descends (prefixWord ++ tailWord_3723055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3723106 : List Nat := [3, 3, 2, 1, 2, 1, 1, 5, 1, 3]
def baseStart_3723106 : Nat := 118140960795 + 3723106 * 2 ^ 59
def prefixEnd_3723106 : Nat := 4983230072969 + 3 ^ 40 * 3723106 * 2
def baseEnd_3723106 : Nat := 1274495270425610376235169

theorem tailTrace_3723106 : CollatzResearch.WordTrace tailWord_3723106 prefixEnd_3723106 1274495270425610376235169 := by
  unfold tailWord_3723106
  simp only [CollatzResearch.WordTrace]
  refine ⟨33948207912457573181709293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90528554433220195151224781 33948207912457573181709293)
  ·
    refine ⟨12730577967171589943140985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33948207912457573181709293 12730577967171589943140985)
    ·
      refine ⟨9547933475378692457355739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12730577967171589943140985 9547933475378692457355739)
      ·
        refine ⟨14321900213068038686033609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9547933475378692457355739 14321900213068038686033609)
        ·
          refine ⟨10741425159801029014525207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14321900213068038686033609 10741425159801029014525207)
          ·
            refine ⟨16112137739701543521787811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10741425159801029014525207 16112137739701543521787811)
            ·
              refine ⟨24168206609552315282681717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16112137739701543521787811 24168206609552315282681717)
              ·
                refine ⟨2265769369645529557751411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24168206609552315282681717 2265769369645529557751411)
                ·
                  refine ⟨3398654054468294336627117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2265769369645529557751411 3398654054468294336627117)
                  ·
                    refine ⟨1274495270425610376235169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3398654054468294336627117 1274495270425610376235169)
                    ·
                      rfl

theorem cell22_3723106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 1, 5, 1, 3].length) (baseStart_3723106 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3723106 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3723106 prefixEnd_3723106 := by exact prefixLift 3723106
  have htrace : WordTrace (prefixWord ++ tailWord_3723106) baseStart_3723106 baseEnd_3723106 := by
    simpa [prefixWord, tailWord_3723106, baseEnd_3723106] using wordTrace_append hprefix tailTrace_3723106
  have hstable : (prefixWord ++ tailWord_3723106).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3723106).length < 2 ^ (prefixWord ++ tailWord_3723106).sum := by decide
  have hdescent : baseEnd_3723106 < baseStart_3723106 := by decide
  rcases family_descends (prefixWord ++ tailWord_3723106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3723130 : List Nat := [3, 1, 1, 1, 1, 1, 5, 3, 6]
def baseStart_3723130 : Nat := 118140960795 + 3723130 * 2 ^ 59
def prefixEnd_3723130 : Nat := 4983230072969 + 3 ^ 40 * 3723130 * 2
def baseEnd_3723130 : Nat := 424834495372027437878365

theorem tailTrace_3723130 : CollatzResearch.WordTrace tailWord_3723130 prefixEnd_3723130 424834495372027437878365 := by
  unfold tailWord_3723130
  simp only [CollatzResearch.WordTrace]
  refine ⟨33948426750435836206427711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90529138001162229883807229 33948426750435836206427711)
  ·
    refine ⟨50922640125653754309641567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33948426750435836206427711 50922640125653754309641567)
    ·
      refine ⟨76383960188480631464462351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50922640125653754309641567 76383960188480631464462351)
      ·
        refine ⟨114575940282720947196693527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76383960188480631464462351 114575940282720947196693527)
        ·
          refine ⟨171863910424081420795040291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114575940282720947196693527 171863910424081420795040291)
          ·
            refine ⟨257795865636122131192560437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 171863910424081420795040291 257795865636122131192560437)
            ·
              refine ⟨24168362403386449799302541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 257795865636122131192560437 24168362403386449799302541)
              ·
                refine ⟨9063135901269918674738453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24168362403386449799302541 9063135901269918674738453)
                ·
                  refine ⟨424834495372027437878365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9063135901269918674738453 424834495372027437878365)
                  ·
                    rfl

theorem cell22_3723130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 5, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 5, 3, 6].length) (baseStart_3723130 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3723130 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3723130 prefixEnd_3723130 := by exact prefixLift 3723130
  have htrace : WordTrace (prefixWord ++ tailWord_3723130) baseStart_3723130 baseEnd_3723130 := by
    simpa [prefixWord, tailWord_3723130, baseEnd_3723130] using wordTrace_append hprefix tailTrace_3723130
  have hstable : (prefixWord ++ tailWord_3723130).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3723130).length < 2 ^ (prefixWord ++ tailWord_3723130).sum := by decide
  have hdescent : baseEnd_3723130 < baseStart_3723130 := by decide
  rcases family_descends (prefixWord ++ tailWord_3723130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3723134 : List Nat := [4, 2, 3, 1, 1, 1, 2, 1, 2, 5]
def baseStart_3723134 : Nat := 118140960795 + 3723134 * 2 ^ 59
def prefixEnd_3723134 : Nat := 4983230072969 + 3 ^ 40 * 3723134 * 2
def baseEnd_3723134 : Nat := 1274504855397827636535083

theorem tailTrace_3723134 : CollatzResearch.WordTrace tailWord_3723134 prefixEnd_3723134 1274504855397827636535083 := by
  unfold tailWord_3723134
  simp only [CollatzResearch.WordTrace]
  refine ⟨16974231611716106688607057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 90529235262485902339237637 16974231611716106688607057)
  ·
    refine ⟨12730673708787080016455293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16974231611716106688607057 12730673708787080016455293)
    ·
      refine ⟨4774002640795155006170735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12730673708787080016455293 4774002640795155006170735)
      ·
        refine ⟨7161003961192732509256103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4774002640795155006170735 7161003961192732509256103)
        ·
          refine ⟨10741505941789098763884155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7161003961192732509256103 10741505941789098763884155)
          ·
            refine ⟨16112258912683648145826233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10741505941789098763884155 16112258912683648145826233)
            ·
              refine ⟨12084194184512736109369675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16112258912683648145826233 12084194184512736109369675)
              ·
                refine ⟨18126291276769104164054513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12084194184512736109369675 18126291276769104164054513)
                ·
                  refine ⟨13594718457576828123040885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18126291276769104164054513 13594718457576828123040885)
                  ·
                    refine ⟨1274504855397827636535083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13594718457576828123040885 1274504855397827636535083)
                    ·
                      rfl

theorem cell22_3723134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 2, 1, 2, 5].length) (baseStart_3723134 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3723134 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3723134 prefixEnd_3723134 := by exact prefixLift 3723134
  have htrace : WordTrace (prefixWord ++ tailWord_3723134) baseStart_3723134 baseEnd_3723134 := by
    simpa [prefixWord, tailWord_3723134, baseEnd_3723134] using wordTrace_append hprefix tailTrace_3723134
  have hstable : (prefixWord ++ tailWord_3723134).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3723134).length < 2 ^ (prefixWord ++ tailWord_3723134).sum := by decide
  have hdescent : baseEnd_3723134 < baseStart_3723134 := by decide
  rcases family_descends (prefixWord ++ tailWord_3723134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3723205 : List Nat := [1, 3, 1, 1, 1, 1, 1, 3, 4, 6]
def baseStart_3723205 : Nat := 118140960795 + 3723205 * 2 ^ 59
def prefixEnd_3723205 : Nat := 4983230072969 + 3 ^ 40 * 3723205 * 2
def baseEnd_3723205 : Nat := 1274529160148807118009865

theorem tailTrace_3723205 : CollatzResearch.WordTrace tailWord_3723205 prefixEnd_3723205 1274529160148807118009865 := by
  unfold tailWord_3723205
  simp only [CollatzResearch.WordTrace]
  refine ⟨135796442476471632634691069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90530961650981088423127379 135796442476471632634691069)
  ·
    refine ⟨50923665928676862238009151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135796442476471632634691069 50923665928676862238009151)
    ·
      refine ⟨76385498893015293357013727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50923665928676862238009151 76385498893015293357013727)
      ·
        refine ⟨114578248339522940035520591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76385498893015293357013727 114578248339522940035520591)
        ·
          refine ⟨171867372509284410053280887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114578248339522940035520591 171867372509284410053280887)
          ·
            refine ⟨257801058763926615079921331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 171867372509284410053280887 257801058763926615079921331)
            ·
              refine ⟨386701588145889922619881997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 257801058763926615079921331 386701588145889922619881997)
              ·
                refine ⟨145013095554708720982455749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 386701588145889922619881997 145013095554708720982455749)
                ·
                  refine ⟨27189955416507885184210453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 145013095554708720982455749 27189955416507885184210453)
                  ·
                    refine ⟨1274529160148807118009865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27189955416507885184210453 1274529160148807118009865)
                    ·
                      rfl

theorem cell22_3723205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 3, 4, 6].length) (baseStart_3723205 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3723205 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3723205 prefixEnd_3723205 := by exact prefixLift 3723205
  have htrace : WordTrace (prefixWord ++ tailWord_3723205) baseStart_3723205 baseEnd_3723205 := by
    simpa [prefixWord, tailWord_3723205, baseEnd_3723205] using wordTrace_append hprefix tailTrace_3723205
  have hstable : (prefixWord ++ tailWord_3723205).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3723205).length < 2 ^ (prefixWord ++ tailWord_3723205).sum := by decide
  have hdescent : baseEnd_3723205 < baseStart_3723205 := by decide
  rcases family_descends (prefixWord ++ tailWord_3723205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3723207 : List Nat := [1, 1, 4, 1, 1, 2, 1, 3, 5, 3]
def baseStart_3723207 : Nat := 118140960795 + 3723207 * 2 ^ 59
def prefixEnd_3723207 : Nat := 4983230072969 + 3 ^ 40 * 3723207 * 2
def baseEnd_3723207 : Nat := 1274529844789679779459859

theorem tailTrace_3723207 : CollatzResearch.WordTrace tailWord_3723207 prefixEnd_3723207 1274529844789679779459859 := by
  unfold tailWord_3723207
  simp only [CollatzResearch.WordTrace]
  refine ⟨135796515422464386976263875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90531010281642924650842583 135796515422464386976263875)
  ·
    refine ⟨203694773133696580464395813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135796515422464386976263875 203694773133696580464395813)
    ·
      refine ⟨38192769962568108837074215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 203694773133696580464395813 38192769962568108837074215)
      ·
        refine ⟨57289154943852163255611323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38192769962568108837074215 57289154943852163255611323)
        ·
          refine ⟨85933732415778244883416985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57289154943852163255611323 85933732415778244883416985)
          ·
            refine ⟨64450299311833683662562739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85933732415778244883416985 64450299311833683662562739)
            ·
              refine ⟨96675448967750525493844109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64450299311833683662562739 96675448967750525493844109)
              ·
                refine ⟨36253293362906447060191541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 96675448967750525493844109 36253293362906447060191541)
                ·
                  refine ⟨3398746252772479411892957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 36253293362906447060191541 3398746252772479411892957)
                  ·
                    refine ⟨1274529844789679779459859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3398746252772479411892957 1274529844789679779459859)
                    ·
                      rfl

theorem cell22_3723207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 3, 5, 3].length) (baseStart_3723207 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3723207 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3723207 prefixEnd_3723207 := by exact prefixLift 3723207
  have htrace : WordTrace (prefixWord ++ tailWord_3723207) baseStart_3723207 baseEnd_3723207 := by
    simpa [prefixWord, tailWord_3723207, baseEnd_3723207] using wordTrace_append hprefix tailTrace_3723207
  have hstable : (prefixWord ++ tailWord_3723207).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3723207).length < 2 ^ (prefixWord ++ tailWord_3723207).sum := by decide
  have hdescent : baseEnd_3723207 < baseStart_3723207 := by decide
  rcases family_descends (prefixWord ++ tailWord_3723207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3723299 : List Nat := [1, 1, 1, 4, 3, 1, 1, 6, 4]
def baseStart_3723299 : Nat := 118140960795 + 3723299 * 2 ^ 59
def prefixEnd_3723299 : Nat := 4983230072969 + 3 ^ 40 * 3723299 * 2
def baseEnd_3723299 : Nat := 424853779423274068719859

theorem tailTrace_3723299 : CollatzResearch.WordTrace tailWord_3723299 prefixEnd_3723299 424853779423274068719859 := by
  unfold tailWord_3723299
  simp only [CollatzResearch.WordTrace]
  refine ⟨135799870938131086688612951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90533247292087391125741967 135799870938131086688612951)
  ·
    refine ⟨203699806407196630032919427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135799870938131086688612951 203699806407196630032919427)
    ·
      refine ⟨305549709610794945049379141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203699806407196630032919427 305549709610794945049379141)
      ·
        refine ⟨57290570552024052196758589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 305549709610794945049379141 57290570552024052196758589)
        ·
          refine ⟨21483963957009019573784471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57290570552024052196758589 21483963957009019573784471)
          ·
            refine ⟨32225945935513529360676707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21483963957009019573784471 32225945935513529360676707)
            ·
              refine ⟨48338918903270294041015061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32225945935513529360676707 48338918903270294041015061)
              ·
                refine ⟨2265886823590795033172581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 48338918903270294041015061 2265886823590795033172581)
                ·
                  refine ⟨424853779423274068719859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2265886823590795033172581 424853779423274068719859)
                  ·
                    rfl

theorem cell22_3723299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 6, 4].length) (baseStart_3723299 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3723299 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3723299 prefixEnd_3723299 := by exact prefixLift 3723299
  have htrace : WordTrace (prefixWord ++ tailWord_3723299) baseStart_3723299 baseEnd_3723299 := by
    simpa [prefixWord, tailWord_3723299, baseEnd_3723299] using wordTrace_append hprefix tailTrace_3723299
  have hstable : (prefixWord ++ tailWord_3723299).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3723299).length < 2 ^ (prefixWord ++ tailWord_3723299).sum := by decide
  have hdescent : baseEnd_3723299 < baseStart_3723299 := by decide
  rcases family_descends (prefixWord ++ tailWord_3723299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3723312 : List Nat := [2, 1, 1, 1, 2, 5, 1, 2, 1, 6]
def baseStart_3723312 : Nat := 118140960795 + 3723312 * 2 ^ 59
def prefixEnd_3723312 : Nat := 4983230072969 + 3 ^ 40 * 3723312 * 2
def baseEnd_3723312 : Nat := 1274565788435494505584537

theorem tailTrace_3723312 : CollatzResearch.WordTrace tailWord_3723312 prefixEnd_3723312 1274565788435494505584537 := by
  unfold tailWord_3723312
  simp only [CollatzResearch.WordTrace]
  refine ⟨67900172543541994954418095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90533563391389326605890793 67900172543541994954418095)
  ·
    refine ⟨101850258815312992431627143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67900172543541994954418095 101850258815312992431627143)
    ·
      refine ⟨152775388222969488647440715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101850258815312992431627143 152775388222969488647440715)
      ·
        refine ⟨229163082334454232971161073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152775388222969488647440715 229163082334454232971161073)
        ·
          refine ⟨171872311750840674728370805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 229163082334454232971161073 171872311750840674728370805)
          ·
            refine ⟨16113029226641313255784763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 171872311750840674728370805 16113029226641313255784763)
            ·
              refine ⟨24169543839961969883677145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16113029226641313255784763 24169543839961969883677145)
              ·
                refine ⟨18127157879971477412757859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24169543839961969883677145 18127157879971477412757859)
                ·
                  refine ⟨27190736819957216119136789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18127157879971477412757859 27190736819957216119136789)
                  ·
                    refine ⟨1274565788435494505584537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27190736819957216119136789 1274565788435494505584537)
                    ·
                      rfl

theorem cell22_3723312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 1, 2, 1, 6].length) (baseStart_3723312 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3723312 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3723312 prefixEnd_3723312 := by exact prefixLift 3723312
  have htrace : WordTrace (prefixWord ++ tailWord_3723312) baseStart_3723312 baseEnd_3723312 := by
    simpa [prefixWord, tailWord_3723312, baseEnd_3723312] using wordTrace_append hprefix tailTrace_3723312
  have hstable : (prefixWord ++ tailWord_3723312).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3723312).length < 2 ^ (prefixWord ++ tailWord_3723312).sum := by decide
  have hdescent : baseEnd_3723312 < baseStart_3723312 := by decide
  rcases family_descends (prefixWord ++ tailWord_3723312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3723314 : List Nat := [3, 2, 1, 1, 2, 3, 3, 1, 1, 5]
def baseStart_3723314 : Nat := 118140960795 + 3723314 * 2 ^ 59
def prefixEnd_3723314 : Nat := 4983230072969 + 3 ^ 40 * 3723314 * 2
def baseEnd_3723314 : Nat := 1274566473076367167034531

theorem tailTrace_3723314 : CollatzResearch.WordTrace tailWord_3723314 prefixEnd_3723314 1274566473076367167034531 := by
  unfold tailWord_3723314
  simp only [CollatzResearch.WordTrace]
  refine ⟨33950104508269186062602249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90533612022051162833605997 33950104508269186062602249)
  ·
    refine ⟨25462578381201889546951687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33950104508269186062602249 25462578381201889546951687)
    ·
      refine ⟨38193867571802834320427531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25462578381201889546951687 38193867571802834320427531)
      ·
        refine ⟨57290801357704251480641297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38193867571802834320427531 57290801357704251480641297)
        ·
          refine ⟨42968101018278188610480973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57290801357704251480641297 42968101018278188610480973)
          ·
            refine ⟨16113037881854320728930365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42968101018278188610480973 16113037881854320728930365)
            ·
              refine ⟨6042389205695370273348887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16113037881854320728930365 6042389205695370273348887)
              ·
                refine ⟨9063583808543055410023331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6042389205695370273348887 9063583808543055410023331)
                ·
                  refine ⟨13595375712814583115034997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9063583808543055410023331 13595375712814583115034997)
                  ·
                    refine ⟨1274566473076367167034531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13595375712814583115034997 1274566473076367167034531)
                    ·
                      rfl

theorem cell22_3723314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 3, 1, 1, 5].length) (baseStart_3723314 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3723314 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3723314 prefixEnd_3723314 := by exact prefixLift 3723314
  have htrace : WordTrace (prefixWord ++ tailWord_3723314) baseStart_3723314 baseEnd_3723314 := by
    simpa [prefixWord, tailWord_3723314, baseEnd_3723314] using wordTrace_append hprefix tailTrace_3723314
  have hstable : (prefixWord ++ tailWord_3723314).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3723314).length < 2 ^ (prefixWord ++ tailWord_3723314).sum := by decide
  have hdescent : baseEnd_3723314 < baseStart_3723314 := by decide
  rcases family_descends (prefixWord ++ tailWord_3723314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3723329 : List Nat := [1, 2, 5, 1, 2, 1, 2, 1, 1, 6]
def baseStart_3723329 : Nat := 118140960795 + 3723329 * 2 ^ 59
def prefixEnd_3723329 : Nat := 4983230072969 + 3 ^ 40 * 3723329 * 2
def baseEnd_3723329 : Nat := 1274571607882912127909485

theorem tailTrace_3723329 : CollatzResearch.WordTrace tailWord_3723329 prefixEnd_3723329 1274571607882912127909485 := by
  unfold tailWord_3723329
  simp only [CollatzResearch.WordTrace]
  refine ⟨135800965128022401812205041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90533976752014934541470027 135800965128022401812205041)
  ·
    refine ⟨101850723846016801359153781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135800965128022401812205041 101850723846016801359153781)
    ·
      refine ⟨9548505360564075127420667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 101850723846016801359153781 9548505360564075127420667)
      ·
        refine ⟨14322758040846112691131001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9548505360564075127420667 14322758040846112691131001)
        ·
          refine ⟨10742068530634584518348251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14322758040846112691131001 10742068530634584518348251)
          ·
            refine ⟨16113102795951876777522377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10742068530634584518348251 16113102795951876777522377)
            ·
              refine ⟨12084827096963907583141783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16113102795951876777522377 12084827096963907583141783)
              ·
                refine ⟨18127240645445861374712675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12084827096963907583141783 18127240645445861374712675)
                ·
                  refine ⟨27190860968168792062069013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18127240645445861374712675 27190860968168792062069013)
                  ·
                    refine ⟨1274571607882912127909485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27190860968168792062069013 1274571607882912127909485)
                    ·
                      rfl

theorem cell22_3723329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 2, 1, 1, 6].length) (baseStart_3723329 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3723329 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3723329 prefixEnd_3723329 := by exact prefixLift 3723329
  have htrace : WordTrace (prefixWord ++ tailWord_3723329) baseStart_3723329 baseEnd_3723329 := by
    simpa [prefixWord, tailWord_3723329, baseEnd_3723329] using wordTrace_append hprefix tailTrace_3723329
  have hstable : (prefixWord ++ tailWord_3723329).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3723329).length < 2 ^ (prefixWord ++ tailWord_3723329).sum := by decide
  have hdescent : baseEnd_3723329 < baseStart_3723329 := by decide
  rcases family_descends (prefixWord ++ tailWord_3723329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3723346 : List Nat := [3, 2, 2, 1, 4, 1, 1, 2, 2, 4]
def baseStart_3723346 : Nat := 118140960795 + 3723346 * 2 ^ 59
def prefixEnd_3723346 : Nat := 4983230072969 + 3 ^ 40 * 3723346 * 2
def baseEnd_3723346 : Nat := 1274577427330329750234433

theorem tailTrace_3723346 : CollatzResearch.WordTrace tailWord_3723346 prefixEnd_3723346 1274577427330329750234433 := by
  unfold tailWord_3723346
  simp only [CollatzResearch.WordTrace]
  refine ⟨33950396292240203428893473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90534390112640542477049261 33950396292240203428893473)
  ·
    refine ⟨25462797219180152571670105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33950396292240203428893473 25462797219180152571670105)
    ·
      refine ⟨19097097914385114428752579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25462797219180152571670105 19097097914385114428752579)
      ·
        refine ⟨28645646871577671643128869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19097097914385114428752579 28645646871577671643128869)
        ·
          refine ⟨5371058788420813433086663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28645646871577671643128869 5371058788420813433086663)
          ·
            refine ⟨8056588182631220149629995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5371058788420813433086663 8056588182631220149629995)
            ·
              refine ⟨12084882273946830224444993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8056588182631220149629995 12084882273946830224444993)
              ·
                refine ⟨9063661705460122668333745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12084882273946830224444993 9063661705460122668333745)
                ·
                  refine ⟨6797746279095092001250309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9063661705460122668333745 6797746279095092001250309)
                  ·
                    refine ⟨1274577427330329750234433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6797746279095092001250309 1274577427330329750234433)
                    ·
                      rfl

theorem cell22_3723346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 1, 2, 2, 4].length) (baseStart_3723346 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3723346 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3723346 prefixEnd_3723346 := by exact prefixLift 3723346
  have htrace : WordTrace (prefixWord ++ tailWord_3723346) baseStart_3723346 baseEnd_3723346 := by
    simpa [prefixWord, tailWord_3723346, baseEnd_3723346] using wordTrace_append hprefix tailTrace_3723346
  have hstable : (prefixWord ++ tailWord_3723346).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3723346).length < 2 ^ (prefixWord ++ tailWord_3723346).sum := by decide
  have hdescent : baseEnd_3723346 < baseStart_3723346 := by decide
  rcases family_descends (prefixWord ++ tailWord_3723346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3723359 : List Nat := [1, 1, 2, 3, 1, 1, 2, 5, 3, 3]
def baseStart_3723359 : Nat := 118140960795 + 3723359 * 2 ^ 59
def prefixEnd_3723359 : Nat := 4983230072969 + 3 ^ 40 * 3723359 * 2
def baseEnd_3723359 : Nat := 1274581877496002049659393

theorem tailTrace_3723359 : CollatzResearch.WordTrace tailWord_3723359 prefixEnd_3723359 1274581877496002049659393 := by
  unfold tailWord_3723359
  simp only [CollatzResearch.WordTrace]
  refine ⟨135802059317913716935797131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90534706211942477957198087 135802059317913716935797131)
  ·
    refine ⟨203703088976870575403695697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135802059317913716935797131 203703088976870575403695697)
    ·
      refine ⟨152777316732652931552771773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 203703088976870575403695697 152777316732652931552771773)
      ·
        refine ⟨57291493774744849332289415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 152777316732652931552771773 57291493774744849332289415)
        ·
          refine ⟨85937240662117273998434123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57291493774744849332289415 85937240662117273998434123)
          ·
            refine ⟨128905860993175910997651185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85937240662117273998434123 128905860993175910997651185)
            ·
              refine ⟨96679395744881933248238389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 128905860993175910997651185 96679395744881933248238389)
              ·
                refine ⟨9063693351082681242022349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 96679395744881933248238389 9063693351082681242022349)
                ·
                  refine ⟨3398885006656005465758381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9063693351082681242022349 3398885006656005465758381)
                  ·
                    refine ⟨1274581877496002049659393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3398885006656005465758381 1274581877496002049659393)
                    ·
                      rfl

theorem cell22_3723359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 5, 3, 3].length) (baseStart_3723359 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3723359 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3723359 prefixEnd_3723359 := by exact prefixLift 3723359
  have htrace : WordTrace (prefixWord ++ tailWord_3723359) baseStart_3723359 baseEnd_3723359 := by
    simpa [prefixWord, tailWord_3723359, baseEnd_3723359] using wordTrace_append hprefix tailTrace_3723359
  have hstable : (prefixWord ++ tailWord_3723359).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3723359).length < 2 ^ (prefixWord ++ tailWord_3723359).sum := by decide
  have hdescent : baseEnd_3723359 < baseStart_3723359 := by decide
  rcases family_descends (prefixWord ++ tailWord_3723359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3723387 : List Nat := [1, 1, 1, 1, 1, 4, 1, 1, 6, 5]
def baseStart_3723387 : Nat := 118140960795 + 3723387 * 2 ^ 59
def prefixEnd_3723387 : Nat := 4983230072969 + 3 ^ 40 * 3723387 * 2
def baseEnd_3723387 : Nat := 1274591462468219309959307

theorem tailTrace_3723387 : CollatzResearch.WordTrace tailWord_3723387 prefixEnd_3723387 1274591462468219309959307 := by
  unfold tailWord_3723387
  simp only [CollatzResearch.WordTrace]
  refine ⟨135803080561812277717816415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90535387041208185145210943 135803080561812277717816415)
  ·
    refine ⟨203704620842718416576724623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135803080561812277717816415 203704620842718416576724623)
    ·
      refine ⟨305556931264077624865086935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203704620842718416576724623 305556931264077624865086935)
      ·
        refine ⟨458335396896116437297630403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 305556931264077624865086935 458335396896116437297630403)
        ·
          refine ⟨687503095344174655946445605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 458335396896116437297630403 687503095344174655946445605)
          ·
            refine ⟨128906830377032747989958551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 687503095344174655946445605 128906830377032747989958551)
            ·
              refine ⟨193360245565549121984937827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 128906830377032747989958551 193360245565549121984937827)
              ·
                refine ⟨290040368348323682977406741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 193360245565549121984937827 290040368348323682977406741)
                ·
                  refine ⟨13595642266327672639565941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 290040368348323682977406741 13595642266327672639565941)
                  ·
                    refine ⟨1274591462468219309959307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13595642266327672639565941 1274591462468219309959307)
                    ·
                      rfl

theorem cell22_3723387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 1, 6, 5].length) (baseStart_3723387 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3723387 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3723387 prefixEnd_3723387 := by exact prefixLift 3723387
  have htrace : WordTrace (prefixWord ++ tailWord_3723387) baseStart_3723387 baseEnd_3723387 := by
    simpa [prefixWord, tailWord_3723387, baseEnd_3723387] using wordTrace_append hprefix tailTrace_3723387
  have hstable : (prefixWord ++ tailWord_3723387).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3723387).length < 2 ^ (prefixWord ++ tailWord_3723387).sum := by decide
  have hdescent : baseEnd_3723387 < baseStart_3723387 := by decide
  rcases family_descends (prefixWord ++ tailWord_3723387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3723417 : List Nat := [1, 2, 1, 2, 1, 2, 1, 2, 10]
def baseStart_3723417 : Nat := 118140960795 + 3723417 * 2 ^ 59
def prefixEnd_3723417 : Nat := 4983230072969 + 3 ^ 40 * 3723417 * 2
def baseEnd_3723417 : Nat := 424867244027103077236405

theorem tailTrace_3723417 : CollatzResearch.WordTrace tailWord_3723417 prefixEnd_3723417 424867244027103077236405 := by
  unfold tailWord_3723417
  simp only [CollatzResearch.WordTrace]
  refine ⟨135804174751703592841408505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90536116501135728560939003 135804174751703592841408505)
  ·
    refine ⟨101853131063777694631056379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135804174751703592841408505 101853131063777694631056379)
    ·
      refine ⟨152779696595666541946584569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101853131063777694631056379 152779696595666541946584569)
      ·
        refine ⟨114584772446749906459938427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152779696595666541946584569 114584772446749906459938427)
        ·
          refine ⟨171877158670124859689907641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114584772446749906459938427 171877158670124859689907641)
          ·
            refine ⟨128907869002593644767430731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 171877158670124859689907641 128907869002593644767430731)
            ·
              refine ⟨193361803503890467151146097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 128907869002593644767430731 193361803503890467151146097)
              ·
                refine ⟨145021352627917850363359573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 193361803503890467151146097 145021352627917850363359573)
                ·
                  refine ⟨424867244027103077236405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 145021352627917850363359573 424867244027103077236405)
                  ·
                    rfl

theorem cell22_3723417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 2, 10].length) (baseStart_3723417 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3723417 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3723417 prefixEnd_3723417 := by exact prefixLift 3723417
  have htrace : WordTrace (prefixWord ++ tailWord_3723417) baseStart_3723417 baseEnd_3723417 := by
    simpa [prefixWord, tailWord_3723417, baseEnd_3723417] using wordTrace_append hprefix tailTrace_3723417
  have hstable : (prefixWord ++ tailWord_3723417).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3723417).length < 2 ^ (prefixWord ++ tailWord_3723417).sum := by decide
  have hdescent : baseEnd_3723417 < baseStart_3723417 := by decide
  rcases family_descends (prefixWord ++ tailWord_3723417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3723449 : List Nat := [1, 2, 1, 4, 1, 2, 1, 4, 1, 5]
def baseStart_3723449 : Nat := 118140960795 + 3723449 * 2 ^ 59
def prefixEnd_3723449 : Nat := 4983230072969 + 3 ^ 40 * 3723449 * 2
def baseEnd_3723449 : Nat := 1274612686335271814909117

theorem tailTrace_3723449 : CollatzResearch.WordTrace tailWord_3723449 prefixEnd_3723449 1274612686335271814909117 := by
  unfold tailWord_3723449
  simp only [CollatzResearch.WordTrace]
  refine ⟨135805341887587662306573401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90536894591725108204382267 135805341887587662306573401)
  ·
    refine ⟨101854006415690746729930051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135805341887587662306573401 101854006415690746729930051)
    ·
      refine ⟨152781009623536120094895077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101854006415690746729930051 152781009623536120094895077)
      ·
        refine ⟨28646439304413022517792827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 152781009623536120094895077 28646439304413022517792827)
        ·
          refine ⟨42969658956619533776689241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28646439304413022517792827 42969658956619533776689241)
          ·
            refine ⟨32227244217464650332516931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42969658956619533776689241 32227244217464650332516931)
            ·
              refine ⟨48340866326196975498775397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32227244217464650332516931 48340866326196975498775397)
              ·
                refine ⟨9063912436161932906020387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48340866326196975498775397 9063912436161932906020387)
                ·
                  refine ⟨13595868654242899359030581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9063912436161932906020387 13595868654242899359030581)
                  ·
                    refine ⟨1274612686335271814909117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13595868654242899359030581 1274612686335271814909117)
                    ·
                      rfl

theorem cell22_3723449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 4, 1, 5].length) (baseStart_3723449 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3723449 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3723449 prefixEnd_3723449 := by exact prefixLift 3723449
  have htrace : WordTrace (prefixWord ++ tailWord_3723449) baseStart_3723449 baseEnd_3723449 := by
    simpa [prefixWord, tailWord_3723449, baseEnd_3723449] using wordTrace_append hprefix tailTrace_3723449
  have hstable : (prefixWord ++ tailWord_3723449).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3723449).length < 2 ^ (prefixWord ++ tailWord_3723449).sum := by decide
  have hdescent : baseEnd_3723449 < baseStart_3723449 := by decide
  rcases family_descends (prefixWord ++ tailWord_3723449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3723451 : List Nat := [1, 1, 1, 1, 1, 2, 8, 3, 4]
def baseStart_3723451 : Nat := 118140960795 + 3723451 * 2 ^ 59
def prefixEnd_3723451 : Nat := 4983230072969 + 3 ^ 40 * 3723451 * 2
def baseEnd_3723451 : Nat := 424871123658714825453037

theorem tailTrace_3723451 : CollatzResearch.WordTrace tailWord_3723451 prefixEnd_3723451 424871123658714825453037 := by
  unfold tailWord_3723451
  simp only [CollatzResearch.WordTrace]
  refine ⟨135805414833580416648146207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90536943222386944432097471 135805414833580416648146207)
  ·
    refine ⟨203708122250370624972219311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135805414833580416648146207 203708122250370624972219311)
    ·
      refine ⟨305562183375555937458328967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203708122250370624972219311 305562183375555937458328967)
      ·
        refine ⟨458343275063333906187493451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 305562183375555937458328967 458343275063333906187493451)
        ·
          refine ⟨687514912595000859281240177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 458343275063333906187493451 687514912595000859281240177)
          ·
            refine ⟨515636184446250644460930133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 687514912595000859281240177 515636184446250644460930133)
            ·
              refine ⟨6042611536479499739776525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 515636184446250644460930133 6042611536479499739776525)
              ·
                refine ⟨2265979326179812402416197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6042611536479499739776525 2265979326179812402416197)
                ·
                  refine ⟨424871123658714825453037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2265979326179812402416197 424871123658714825453037)
                  ·
                    rfl

theorem cell22_3723451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 8, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 8, 3, 4].length) (baseStart_3723451 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3723451 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3723451 prefixEnd_3723451 := by exact prefixLift 3723451
  have htrace : WordTrace (prefixWord ++ tailWord_3723451) baseStart_3723451 baseEnd_3723451 := by
    simpa [prefixWord, tailWord_3723451, baseEnd_3723451] using wordTrace_append hprefix tailTrace_3723451
  have hstable : (prefixWord ++ tailWord_3723451).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3723451).length < 2 ^ (prefixWord ++ tailWord_3723451).sum := by decide
  have hdescent : baseEnd_3723451 < baseStart_3723451 := by decide
  rcases family_descends (prefixWord ++ tailWord_3723451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3723464 : List Nat := [2, 1, 3, 1, 2, 1, 1, 3, 4, 4]
def baseStart_3723464 : Nat := 118140960795 + 3723464 * 2 ^ 59
def prefixEnd_3723464 : Nat := 4983230072969 + 3 ^ 40 * 3723464 * 2
def baseEnd_3723464 : Nat := 1274617821141816775784071

theorem tailTrace_3723464 : CollatzResearch.WordTrace tailWord_3723464 prefixEnd_3723464 1274617821141816775784071 := by
  unfold tailWord_3723464
  simp only [CollatzResearch.WordTrace]
  refine ⟨67902944491266659934184723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90537259321688879912246297 67902944491266659934184723)
  ·
    refine ⟨101854416736899989901277085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67902944491266659934184723 101854416736899989901277085)
    ·
      refine ⟨38195406276337496212978907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101854416736899989901277085 38195406276337496212978907)
      ·
        refine ⟨57293109414506244319468361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38195406276337496212978907 57293109414506244319468361)
        ·
          refine ⟨42969832060879683239601271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57293109414506244319468361 42969832060879683239601271)
          ·
            refine ⟨64454748091319524859401907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42969832060879683239601271 64454748091319524859401907)
            ·
              refine ⟨96682122136979287289102861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64454748091319524859401907 96682122136979287289102861)
              ·
                refine ⟨36255795801367232733413573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 96682122136979287289102861 36255795801367232733413573)
                ·
                  refine ⟨6797961712756356137515045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36255795801367232733413573 6797961712756356137515045)
                  ·
                    refine ⟨1274617821141816775784071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6797961712756356137515045 1274617821141816775784071)
                    ·
                      rfl

theorem cell22_3723464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 3, 4, 4].length) (baseStart_3723464 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3723464 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3723464 prefixEnd_3723464 := by exact prefixLift 3723464
  have htrace : WordTrace (prefixWord ++ tailWord_3723464) baseStart_3723464 baseEnd_3723464 := by
    simpa [prefixWord, tailWord_3723464, baseEnd_3723464] using wordTrace_append hprefix tailTrace_3723464
  have hstable : (prefixWord ++ tailWord_3723464).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3723464).length < 2 ^ (prefixWord ++ tailWord_3723464).sum := by decide
  have hdescent : baseEnd_3723464 < baseStart_3723464 := by decide
  rcases family_descends (prefixWord ++ tailWord_3723464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3723466 : List Nat := [3, 1, 2, 1, 3, 1, 3, 1, 4, 3]
def baseStart_3723466 : Nat := 118140960795 + 3723466 * 2 ^ 59
def prefixEnd_3723466 : Nat := 4983230072969 + 3 ^ 40 * 3723466 * 2
def baseEnd_3723466 : Nat := 1274618505782689437234065

theorem tailTrace_3723466 : CollatzResearch.WordTrace tailWord_3723466 prefixEnd_3723466 1274618505782689437234065 := by
  unfold tailWord_3723466
  simp only [CollatzResearch.WordTrace]
  refine ⟨33951490482131518552485563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90537307952350716139961501 33951490482131518552485563)
  ·
    refine ⟨50927235723197277828728345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33951490482131518552485563 50927235723197277828728345)
    ·
      refine ⟨38195426792397958371546259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50927235723197277828728345 38195426792397958371546259)
      ·
        refine ⟨57293140188596937557319389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38195426792397958371546259 57293140188596937557319389)
        ·
          refine ⟨21484927570723851583994771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57293140188596937557319389 21484927570723851583994771)
          ·
            refine ⟨32227391356085777375992157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21484927570723851583994771 32227391356085777375992157)
            ·
              refine ⟨12085271758532166515997059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32227391356085777375992157 12085271758532166515997059)
              ·
                refine ⟨18127907637798249773995589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12085271758532166515997059 18127907637798249773995589)
                ·
                  refine ⟨3398982682087171832624173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18127907637798249773995589 3398982682087171832624173)
                  ·
                    refine ⟨1274618505782689437234065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3398982682087171832624173 1274618505782689437234065)
                    ·
                      rfl

theorem cell22_3723466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 3, 1, 4, 3].length) (baseStart_3723466 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3723466 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3723466 prefixEnd_3723466 := by exact prefixLift 3723466
  have htrace : WordTrace (prefixWord ++ tailWord_3723466) baseStart_3723466 baseEnd_3723466 := by
    simpa [prefixWord, tailWord_3723466, baseEnd_3723466] using wordTrace_append hprefix tailTrace_3723466
  have hstable : (prefixWord ++ tailWord_3723466).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3723466).length < 2 ^ (prefixWord ++ tailWord_3723466).sum := by decide
  have hdescent : baseEnd_3723466 < baseStart_3723466 := by decide
  rcases family_descends (prefixWord ++ tailWord_3723466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3723468 : List Nat := [2, 2, 1, 6, 1, 1, 2, 1, 6]
def baseStart_3723468 : Nat := 118140960795 + 3723468 * 2 ^ 59
def prefixEnd_3723468 : Nat := 4983230072969 + 3 ^ 40 * 3723468 * 2
def baseEnd_3723468 : Nat := 424873063474520699561353

theorem tailTrace_3723468 : CollatzResearch.WordTrace tailWord_3723468 prefixEnd_3723468 424873063474520699561353 := by
  unfold tailWord_3723468
  simp only [CollatzResearch.WordTrace]
  refine ⟨67903017437259414275757529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90537356583012552367676705 67903017437259414275757529)
  ·
    refine ⟨50927263077944560706818147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67903017437259414275757529 50927263077944560706818147)
    ·
      refine ⟨76390894616916841060227221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50927263077944560706818147 76390894616916841060227221)
      ·
        refine ⟨3580823185167976924698151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 76390894616916841060227221 3580823185167976924698151)
        ·
          refine ⟨5371234777751965387047227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3580823185167976924698151 5371234777751965387047227)
          ·
            refine ⟨8056852166627948080570841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5371234777751965387047227 8056852166627948080570841)
            ·
              refine ⟨6042639124970961060428131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8056852166627948080570841 6042639124970961060428131)
              ·
                refine ⟨9063958687456441590642197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6042639124970961060428131 9063958687456441590642197)
                ·
                  refine ⟨424873063474520699561353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9063958687456441590642197 424873063474520699561353)
                  ·
                    rfl

theorem cell22_3723468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 2, 1, 6].length) (baseStart_3723468 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3723468 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3723468 prefixEnd_3723468 := by exact prefixLift 3723468
  have htrace : WordTrace (prefixWord ++ tailWord_3723468) baseStart_3723468 baseEnd_3723468 := by
    simpa [prefixWord, tailWord_3723468, baseEnd_3723468] using wordTrace_append hprefix tailTrace_3723468
  have hstable : (prefixWord ++ tailWord_3723468).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3723468).length < 2 ^ (prefixWord ++ tailWord_3723468).sum := by decide
  have hdescent : baseEnd_3723468 < baseStart_3723468 := by decide
  rcases family_descends (prefixWord ++ tailWord_3723468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3723496 : List Nat := [2, 1, 4, 1, 2, 2, 4, 6]
def baseStart_3723496 : Nat := 118140960795 + 3723496 * 2 ^ 59
def prefixEnd_3723496 : Nat := 4983230072969 + 3 ^ 40 * 3723496 * 2
def baseEnd_3723496 : Nat := 141625419488419928775997

theorem tailTrace_3723496 : CollatzResearch.WordTrace tailWord_3723496 prefixEnd_3723496 141625419488419928775997 := by
  unfold tailWord_3723496
  simp only [CollatzResearch.WordTrace]
  refine ⟨67903528059208694666767171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90538037412278259555689561 67903528059208694666767171)
  ·
    refine ⟨101855292088813042000150757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67903528059208694666767171 101855292088813042000150757)
    ·
      refine ⟨19097867266652445375028267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 101855292088813042000150757 19097867266652445375028267)
      ·
        refine ⟨28646800899978668062542401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19097867266652445375028267 28646800899978668062542401)
        ·
          refine ⟨21485100674984001046906801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28646800899978668062542401 21485100674984001046906801)
          ·
            refine ⟨16113825506238000785180101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21485100674984001046906801 16113825506238000785180101)
            ·
              refine ⟨3021342282419625147221269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16113825506238000785180101 3021342282419625147221269)
              ·
                refine ⟨141625419488419928775997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3021342282419625147221269 141625419488419928775997)
                ·
                  rfl

theorem cell22_3723496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 4, 6].length) (baseStart_3723496 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3723496 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3723496 prefixEnd_3723496 := by exact prefixLift 3723496
  have htrace : WordTrace (prefixWord ++ tailWord_3723496) baseStart_3723496 baseEnd_3723496 := by
    simpa [prefixWord, tailWord_3723496, baseEnd_3723496] using wordTrace_append hprefix tailTrace_3723496
  have hstable : (prefixWord ++ tailWord_3723496).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3723496).length < 2 ^ (prefixWord ++ tailWord_3723496).sum := by decide
  have hdescent : baseEnd_3723496 < baseStart_3723496 := by decide
  rcases family_descends (prefixWord ++ tailWord_3723496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3723528 : List Nat := [2, 1, 3, 2, 3, 1, 3, 1, 3, 3]
def baseStart_3723528 : Nat := 118140960795 + 3723528 * 2 ^ 59
def prefixEnd_3723528 : Nat := 4983230072969 + 3 ^ 40 * 3723528 * 2
def baseEnd_3723528 : Nat := 1274639729649741942183875

theorem tailTrace_3723528 : CollatzResearch.WordTrace tailWord_3723528 prefixEnd_3723528 1274639729649741942183875 := by
  unfold tailWord_3723528
  simp only [CollatzResearch.WordTrace]
  refine ⟨67904111627150729399349619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90538815502867639199132825 67904111627150729399349619)
  ·
    refine ⟨101856167440726094099024429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67904111627150729399349619 101856167440726094099024429)
    ·
      refine ⟨38196062790272285287134161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101856167440726094099024429 38196062790272285287134161)
      ·
        refine ⟨28647047092704213965350621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38196062790272285287134161 28647047092704213965350621)
        ·
          refine ⟨10742642659764080237006483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28647047092704213965350621 10742642659764080237006483)
          ·
            refine ⟨16113963989646120355509725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10742642659764080237006483 16113963989646120355509725)
            ·
              refine ⟨6042736496117295133316147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16113963989646120355509725 6042736496117295133316147)
              ·
                refine ⟨9064104744175942699974221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6042736496117295133316147 9064104744175942699974221)
                ·
                  refine ⟨3399039279065978512490333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9064104744175942699974221 3399039279065978512490333)
                  ·
                    refine ⟨1274639729649741942183875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3399039279065978512490333 1274639729649741942183875)
                    ·
                      rfl

theorem cell22_3723528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 3, 1, 3, 3].length) (baseStart_3723528 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3723528 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3723528 prefixEnd_3723528 := by exact prefixLift 3723528
  have htrace : WordTrace (prefixWord ++ tailWord_3723528) baseStart_3723528 baseEnd_3723528 := by
    simpa [prefixWord, tailWord_3723528, baseEnd_3723528] using wordTrace_append hprefix tailTrace_3723528
  have hstable : (prefixWord ++ tailWord_3723528).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3723528).length < 2 ^ (prefixWord ++ tailWord_3723528).sum := by decide
  have hdescent : baseEnd_3723528 < baseStart_3723528 := by decide
  rcases family_descends (prefixWord ++ tailWord_3723528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3723539 : List Nat := [1, 1, 1, 2, 1, 3, 1, 5, 2, 5]
def baseStart_3723539 : Nat := 118140960795 + 3723539 * 2 ^ 59
def prefixEnd_3723539 : Nat := 4983230072969 + 3 ^ 40 * 3723539 * 2
def baseEnd_3723539 : Nat := 1274643495174541580158841

theorem tailTrace_3723539 : CollatzResearch.WordTrace tailWord_3723539 prefixEnd_3723539 1274643495174541580158841 := by
  unfold tailWord_3723539
  simp only [CollatzResearch.WordTrace]
  refine ⟨135808624457261607677349671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90539082971507738451566447 135808624457261607677349671)
  ·
    refine ⟨203712936685892411516024507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135808624457261607677349671 203712936685892411516024507)
    ·
      refine ⟨305569405028838617274036761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203712936685892411516024507 305569405028838617274036761)
      ·
        refine ⟨229177053771628962955527571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 305569405028838617274036761 229177053771628962955527571)
        ·
          refine ⟨343765580657443444433291357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 229177053771628962955527571 343765580657443444433291357)
          ·
            refine ⟨128912092746541291662484259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 343765580657443444433291357 128912092746541291662484259)
            ·
              refine ⟨193368139119811937493726389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 128912092746541291662484259 193368139119811937493726389)
              ·
                refine ⟨18128263042482369140036849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 193368139119811937493726389 18128263042482369140036849)
                ·
                  refine ⟨13596197281861776855027637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18128263042482369140036849 13596197281861776855027637)
                  ·
                    refine ⟨1274643495174541580158841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13596197281861776855027637 1274643495174541580158841)
                    ·
                      rfl

theorem cell22_3723539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 5, 2, 5].length) (baseStart_3723539 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3723539 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3723539 prefixEnd_3723539 := by exact prefixLift 3723539
  have htrace : WordTrace (prefixWord ++ tailWord_3723539) baseStart_3723539 baseEnd_3723539 := by
    simpa [prefixWord, tailWord_3723539, baseEnd_3723539] using wordTrace_append hprefix tailTrace_3723539
  have hstable : (prefixWord ++ tailWord_3723539).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3723539).length < 2 ^ (prefixWord ++ tailWord_3723539).sum := by decide
  have hdescent : baseEnd_3723539 < baseStart_3723539 := by decide
  rcases family_descends (prefixWord ++ tailWord_3723539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3723601 : List Nat := [1, 2, 2, 1, 4, 2, 1, 3, 1, 5]
def baseStart_3723601 : Nat := 118140960795 + 3723601 * 2 ^ 59
def prefixEnd_3723601 : Nat := 4983230072969 + 3 ^ 40 * 3723601 * 2
def baseEnd_3723601 : Nat := 1274664719041594085108651

theorem tailTrace_3723601 : CollatzResearch.WordTrace tailWord_3723601 prefixEnd_3723601 1274664719041594085108651 := by
  unfold tailWord_3723601
  simp only [CollatzResearch.WordTrace]
  refine ⟨135810885783036992266106657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90540590522024661510737771 135810885783036992266106657)
  ·
    refine ⟨101858164337277744199579993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135810885783036992266106657 101858164337277744199579993)
    ·
      refine ⟨76393623252958308149684995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101858164337277744199579993 76393623252958308149684995)
      ·
        refine ⟨114590434879437462224527493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76393623252958308149684995 114590434879437462224527493)
        ·
          refine ⟨21485706539894524167098905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 114590434879437462224527493 21485706539894524167098905)
          ·
            refine ⟨16114279904920893125324179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21485706539894524167098905 16114279904920893125324179)
            ·
              refine ⟨24171419857381339687986269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16114279904920893125324179 24171419857381339687986269)
              ·
                refine ⟨9064282446518002382994851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24171419857381339687986269 9064282446518002382994851)
                ·
                  refine ⟨13596423669777003574492277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9064282446518002382994851 13596423669777003574492277)
                  ·
                    refine ⟨1274664719041594085108651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13596423669777003574492277 1274664719041594085108651)
                    ·
                      rfl

theorem cell22_3723601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 1, 3, 1, 5].length) (baseStart_3723601 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3723601 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3723601 prefixEnd_3723601 := by exact prefixLift 3723601
  have htrace : WordTrace (prefixWord ++ tailWord_3723601) baseStart_3723601 baseEnd_3723601 := by
    simpa [prefixWord, tailWord_3723601, baseEnd_3723601] using wordTrace_append hprefix tailTrace_3723601
  have hstable : (prefixWord ++ tailWord_3723601).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3723601).length < 2 ^ (prefixWord ++ tailWord_3723601).sum := by decide
  have hdescent : baseEnd_3723601 < baseStart_3723601 := by decide
  rcases family_descends (prefixWord ++ tailWord_3723601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3723618 : List Nat := [3, 3, 2, 1, 1, 2, 2, 2, 1, 5]
def baseStart_3723618 : Nat := 118140960795 + 3723618 * 2 ^ 59
def prefixEnd_3723618 : Nat := 4983230072969 + 3 ^ 40 * 3723618 * 2
def baseEnd_3723618 : Nat := 1274670538489011707433599

theorem tailTrace_3723618 : CollatzResearch.WordTrace tailWord_3723618 prefixEnd_3723618 1274670538489011707433599 := by
  unfold tailWord_3723618
  simp only [CollatzResearch.WordTrace]
  refine ⟨33952876455993851042368877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90541003882650269446317005 33952876455993851042368877)
  ·
    refine ⟨12732328670997694140888329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33952876455993851042368877 12732328670997694140888329)
    ·
      refine ⟨9549246503248270605666247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12732328670997694140888329 9549246503248270605666247)
      ·
        refine ⟨14323869754872405908499371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9549246503248270605666247 14323869754872405908499371)
        ·
          refine ⟨21485804632308608862749057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14323869754872405908499371 21485804632308608862749057)
          ·
            refine ⟨16114353474231456647061793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21485804632308608862749057 16114353474231456647061793)
            ·
              refine ⟨12085765105673592485296345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16114353474231456647061793 12085765105673592485296345)
              ·
                refine ⟨9064323829255194363972259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12085765105673592485296345 9064323829255194363972259)
                ·
                  refine ⟨13596485743882791545958389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9064323829255194363972259 13596485743882791545958389)
                  ·
                    refine ⟨1274670538489011707433599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13596485743882791545958389 1274670538489011707433599)
                    ·
                      rfl

theorem cell22_3723618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 2, 2, 1, 5].length) (baseStart_3723618 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3723618 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3723618 prefixEnd_3723618 := by exact prefixLift 3723618
  have htrace : WordTrace (prefixWord ++ tailWord_3723618) baseStart_3723618 baseEnd_3723618 := by
    simpa [prefixWord, tailWord_3723618, baseEnd_3723618] using wordTrace_append hprefix tailTrace_3723618
  have hstable : (prefixWord ++ tailWord_3723618).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3723618).length < 2 ^ (prefixWord ++ tailWord_3723618).sum := by decide
  have hdescent : baseEnd_3723618 < baseStart_3723618 := by decide
  rcases family_descends (prefixWord ++ tailWord_3723618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3723710 : List Nat := [4, 2, 1, 1, 1, 1, 6, 1, 5]
def baseStart_3723710 : Nat := 118140960795 + 3723710 * 2 ^ 59
def prefixEnd_3723710 : Nat := 4983230072969 + 3 ^ 40 * 3723710 * 2
def baseEnd_3723710 : Nat := 424900677323051378044439

theorem tailTrace_3723710 : CollatzResearch.WordTrace tailWord_3723710 prefixEnd_3723710 424900677323051378044439 := by
  unfold tailWord_3723710
  simp only [CollatzResearch.WordTrace]
  refine ⟨16976857667455262985228073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 90543240893094735921216389 16976857667455262985228073)
  ·
    refine ⟨12732643250591447238921055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16976857667455262985228073 12732643250591447238921055)
    ·
      refine ⟨19098964875887170858381583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12732643250591447238921055 19098964875887170858381583)
      ·
        refine ⟨28648447313830756287572375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19098964875887170858381583 28648447313830756287572375)
        ·
          refine ⟨42972670970746134431358563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28648447313830756287572375 42972670970746134431358563)
          ·
            refine ⟨64459006456119201647037845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42972670970746134431358563 64459006456119201647037845)
            ·
              refine ⟨3021515927630587577204899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 64459006456119201647037845 3021515927630587577204899)
              ·
                refine ⟨4532273891445881365807349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3021515927630587577204899 4532273891445881365807349)
                ·
                  refine ⟨424900677323051378044439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4532273891445881365807349 424900677323051378044439)
                  ·
                    rfl

theorem cell22_3723710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 6, 1, 5].length) (baseStart_3723710 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3723710 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3723710 prefixEnd_3723710 := by exact prefixLift 3723710
  have htrace : WordTrace (prefixWord ++ tailWord_3723710) baseStart_3723710 baseEnd_3723710 := by
    simpa [prefixWord, tailWord_3723710, baseEnd_3723710] using wordTrace_append hprefix tailTrace_3723710
  have hstable : (prefixWord ++ tailWord_3723710).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3723710).length < 2 ^ (prefixWord ++ tailWord_3723710).sum := by decide
  have hdescent : baseEnd_3723710 < baseStart_3723710 := by decide
  rcases family_descends (prefixWord ++ tailWord_3723710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3723721 : List Nat := [1, 2, 1, 1, 2, 1, 4, 4, 6]
def baseStart_3723721 : Nat := 118140960795 + 3723721 * 2 ^ 59
def prefixEnd_3723721 : Nat := 4983230072969 + 3 ^ 40 * 3723721 * 2
def baseEnd_3723721 : Nat := 424901932497984590702761

theorem tailTrace_3723721 : CollatzResearch.WordTrace tailWord_3723721 prefixEnd_3723721 424901932497984590702761 := by
  unfold tailWord_3723721
  simp only [CollatzResearch.WordTrace]
  refine ⟨135815262542602252760475017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90543508361734835173650011 135815262542602252760475017)
  ·
    refine ⟨101861446906951689570356263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135815262542602252760475017 101861446906951689570356263)
    ·
      refine ⟨152792170360427534355534395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101861446906951689570356263 152792170360427534355534395)
      ·
        refine ⟨229188255540641301533301593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152792170360427534355534395 229188255540641301533301593)
        ·
          refine ⟨171891191655480976149976195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 229188255540641301533301593 171891191655480976149976195)
          ·
            refine ⟨257836787483221464224964293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 171891191655480976149976195 257836787483221464224964293)
            ·
              refine ⟨48344397653104024542180805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 257836787483221464224964293 48344397653104024542180805)
              ·
                refine ⟨9064574559957004601658901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48344397653104024542180805 9064574559957004601658901)
                ·
                  refine ⟨424901932497984590702761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9064574559957004601658901 424901932497984590702761)
                  ·
                    rfl

theorem cell22_3723721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 4, 6].length) (baseStart_3723721 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3723721 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3723721 prefixEnd_3723721 := by exact prefixLift 3723721
  have htrace : WordTrace (prefixWord ++ tailWord_3723721) baseStart_3723721 baseEnd_3723721 := by
    simpa [prefixWord, tailWord_3723721, baseEnd_3723721] using wordTrace_append hprefix tailTrace_3723721
  have hstable : (prefixWord ++ tailWord_3723721).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3723721).length < 2 ^ (prefixWord ++ tailWord_3723721).sum := by decide
  have hdescent : baseEnd_3723721 < baseStart_3723721 := by decide
  rcases family_descends (prefixWord ++ tailWord_3723721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3723789 : List Nat := [1, 7, 1, 1, 1, 1, 1, 5, 4]
def baseStart_3723789 : Nat := 118140960795 + 3723789 * 2 ^ 59
def prefixEnd_3723789 : Nat := 4983230072969 + 3 ^ 40 * 3723789 * 2
def baseEnd_3723789 : Nat := 424909691761208087136025

theorem tailTrace_3723789 : CollatzResearch.WordTrace tailWord_3723789 prefixEnd_3723789 424909691761208087136025 := by
  unfold tailWord_3723789
  simp only [CollatzResearch.WordTrace]
  refine ⟨135817742706355900373950421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90545161804237266915966947 135817742706355900373950421)
  ·
    refine ⟨3183228344680216415014463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 135817742706355900373950421 3183228344680216415014463)
    ·
      refine ⟨4774842517020324622521695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3183228344680216415014463 4774842517020324622521695)
      ·
        refine ⟨7162263775530486933782543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4774842517020324622521695 7162263775530486933782543)
        ·
          refine ⟨10743395663295730400673815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7162263775530486933782543 10743395663295730400673815)
          ·
            refine ⟨16115093494943595601010723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10743395663295730400673815 16115093494943595601010723)
            ·
              refine ⟨24172640242415393401516085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16115093494943595601010723 24172640242415393401516085)
              ·
                refine ⟨2266185022726443131392133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24172640242415393401516085 2266185022726443131392133)
                ·
                  refine ⟨424909691761208087136025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2266185022726443131392133 424909691761208087136025)
                  ·
                    rfl

theorem cell22_3723789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 1, 5, 4].length) (baseStart_3723789 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3723789 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3723789 prefixEnd_3723789 := by exact prefixLift 3723789
  have htrace : WordTrace (prefixWord ++ tailWord_3723789) baseStart_3723789 baseEnd_3723789 := by
    simpa [prefixWord, tailWord_3723789, baseEnd_3723789] using wordTrace_append hprefix tailTrace_3723789
  have hstable : (prefixWord ++ tailWord_3723789).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3723789).length < 2 ^ (prefixWord ++ tailWord_3723789).sum := by decide
  have hdescent : baseEnd_3723789 < baseStart_3723789 := by decide
  rcases family_descends (prefixWord ++ tailWord_3723789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3723821 : List Nat := [1, 5, 4, 1, 1, 2, 1, 1, 1, 5]
def baseStart_3723821 : Nat := 118140960795 + 3723821 * 2 ^ 59
def prefixEnd_3723821 : Nat := 4983230072969 + 3 ^ 40 * 3723821 * 2
def baseEnd_3723821 : Nat := 1274740029537586844607977

theorem tailTrace_3723821 : CollatzResearch.WordTrace tailWord_3723821 prefixEnd_3723821 1274740029537586844607977 := by
  unfold tailWord_3723821
  simp only [CollatzResearch.WordTrace]
  refine ⟨135818909842239969839115317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90545939894826646559410211 135818909842239969839115317)
  ·
    refine ⟨12733022797709997172417061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 135818909842239969839115317 12733022797709997172417061)
    ·
      refine ⟨2387441774570624469828199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12733022797709997172417061 2387441774570624469828199)
      ·
        refine ⟨3581162661855936704742299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2387441774570624469828199 3581162661855936704742299)
        ·
          refine ⟨5371743992783905057113449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3581162661855936704742299 5371743992783905057113449)
          ·
            refine ⟨4028807994587928792835087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5371743992783905057113449 4028807994587928792835087)
            ·
              refine ⟨6043211991881893189252631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4028807994587928792835087 6043211991881893189252631)
              ·
                refine ⟨9064817987822839783878947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6043211991881893189252631 9064817987822839783878947)
                ·
                  refine ⟨13597226981734259675818421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9064817987822839783878947 13597226981734259675818421)
                  ·
                    refine ⟨1274740029537586844607977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13597226981734259675818421 1274740029537586844607977)
                    ·
                      rfl

theorem cell22_3723821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 2, 1, 1, 1, 5].length) (baseStart_3723821 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3723821 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3723821 prefixEnd_3723821 := by exact prefixLift 3723821
  have htrace : WordTrace (prefixWord ++ tailWord_3723821) baseStart_3723821 baseEnd_3723821 := by
    simpa [prefixWord, tailWord_3723821, baseEnd_3723821] using wordTrace_append hprefix tailTrace_3723821
  have hstable : (prefixWord ++ tailWord_3723821).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3723821).length < 2 ^ (prefixWord ++ tailWord_3723821).sum := by decide
  have hdescent : baseEnd_3723821 < baseStart_3723821 := by decide
  rcases family_descends (prefixWord ++ tailWord_3723821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3723905 : List Nat := [1, 2, 4, 2, 1, 1, 3, 2, 1, 5]
def baseStart_3723905 : Nat := 118140960795 + 3723905 * 2 ^ 59
def prefixEnd_3723905 : Nat := 4983230072969 + 3 ^ 40 * 3723905 * 2
def baseEnd_3723905 : Nat := 1274768784454238625507719

theorem tailTrace_3723905 : CollatzResearch.WordTrace tailWord_3723905 prefixEnd_3723905 1274768784454238625507719 := by
  unfold tailWord_3723905
  simp only [CollatzResearch.WordTrace]
  refine ⟨135821973573935652185173169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90547982382623768123448779 135821973573935652185173169)
  ·
    refine ⟨101866480180451739138879877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135821973573935652185173169 101866480180451739138879877)
    ·
      refine ⟨19099965033834701088539977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 101866480180451739138879877 19099965033834701088539977)
      ·
        refine ⟨14324973775376025816404983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19099965033834701088539977 14324973775376025816404983)
        ·
          refine ⟨21487460663064038724607475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14324973775376025816404983 21487460663064038724607475)
          ·
            refine ⟨32231190994596058086911213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21487460663064038724607475 32231190994596058086911213)
            ·
              refine ⟨12086696622973521782591705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32231190994596058086911213 12086696622973521782591705)
              ·
                refine ⟨9065022467230141336943779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12086696622973521782591705 9065022467230141336943779)
                ·
                  refine ⟨13597533700845212005415669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9065022467230141336943779 13597533700845212005415669)
                  ·
                    refine ⟨1274768784454238625507719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13597533700845212005415669 1274768784454238625507719)
                    ·
                      rfl

theorem cell22_3723905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 3, 2, 1, 5].length) (baseStart_3723905 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3723905 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3723905 prefixEnd_3723905 := by exact prefixLift 3723905
  have htrace : WordTrace (prefixWord ++ tailWord_3723905) baseStart_3723905 baseEnd_3723905 := by
    simpa [prefixWord, tailWord_3723905, baseEnd_3723905] using wordTrace_append hprefix tailTrace_3723905
  have hstable : (prefixWord ++ tailWord_3723905).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3723905).length < 2 ^ (prefixWord ++ tailWord_3723905).sum := by decide
  have hdescent : baseEnd_3723905 < baseStart_3723905 := by decide
  rcases family_descends (prefixWord ++ tailWord_3723905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3723924 : List Nat := [2, 4, 2, 2, 1, 2, 1, 4, 4]
def baseStart_3723924 : Nat := 118140960795 + 3723924 * 2 ^ 59
def prefixEnd_3723924 : Nat := 4983230072969 + 3 ^ 40 * 3723924 * 2
def baseEnd_3723924 : Nat := 424925096180842969760887

theorem tailTrace_3723924 : CollatzResearch.WordTrace tailWord_3723924 prefixEnd_3723924 424925096180842969760887 := by
  unfold tailWord_3723924
  simp only [CollatzResearch.WordTrace]
  refine ⟨67911333280433409215057413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90548444373911212286743217 67911333280433409215057413)
  ·
    refine ⟨12733374990081264227823265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 67911333280433409215057413 12733374990081264227823265)
    ·
      refine ⟨9550031242560948170867449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12733374990081264227823265 9550031242560948170867449)
      ·
        refine ⟨7162523431920711128150587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9550031242560948170867449 7162523431920711128150587)
        ·
          refine ⟨10743785147881066692225881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7162523431920711128150587 10743785147881066692225881)
          ·
            refine ⟨8057838860910800019169411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10743785147881066692225881 8057838860910800019169411)
            ·
              refine ⟨12086758291366200028754117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8057838860910800019169411 12086758291366200028754117)
              ·
                refine ⟨2266267179631162505391397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12086758291366200028754117 2266267179631162505391397)
                ·
                  refine ⟨424925096180842969760887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2266267179631162505391397 424925096180842969760887)
                  ·
                    rfl

theorem cell22_3723924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 1, 4, 4].length) (baseStart_3723924 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3723924 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3723924 prefixEnd_3723924 := by exact prefixLift 3723924
  have htrace : WordTrace (prefixWord ++ tailWord_3723924) baseStart_3723924 baseEnd_3723924 := by
    simpa [prefixWord, tailWord_3723924, baseEnd_3723924] using wordTrace_append hprefix tailTrace_3723924
  have hstable : (prefixWord ++ tailWord_3723924).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3723924).length < 2 ^ (prefixWord ++ tailWord_3723924).sum := by decide
  have hdescent : baseEnd_3723924 < baseStart_3723924 := by decide
  rcases family_descends (prefixWord ++ tailWord_3723924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3724093 : List Nat := [1, 4, 1, 4, 2, 2, 2, 2, 4]
def baseStart_3724093 : Nat := 118140960795 + 3724093 * 2 ^ 59
def prefixEnd_3724093 : Nat := 4983230072969 + 3 ^ 40 * 3724093 * 2
def baseEnd_3724093 : Nat := 424944380232089600602381

theorem tailTrace_3724093 : CollatzResearch.WordTrace tailWord_3724093 prefixEnd_3724093 424944380232089600602381 := by
  unfold tailWord_3724093
  simp only [CollatzResearch.WordTrace]
  refine ⟨135828830497254560293016933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90552553664836373528677955 135828830497254560293016933)
  ·
    refine ⟨25467905718235230054940675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 135828830497254560293016933 25467905718235230054940675)
    ·
      refine ⟨38201858577352845082411013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25467905718235230054940675 38201858577352845082411013)
      ·
        refine ⟨7162848483253658452952065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38201858577352845082411013 7162848483253658452952065)
        ·
          refine ⟨5372136362440243839714049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7162848483253658452952065 5372136362440243839714049)
          ·
            refine ⟨4029102271830182879785537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5372136362440243839714049 4029102271830182879785537)
            ·
              refine ⟨3021826703872637159839153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4029102271830182879785537 3021826703872637159839153)
              ·
                refine ⟨2266370027904477869879365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3021826703872637159839153 2266370027904477869879365)
                ·
                  refine ⟨424944380232089600602381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2266370027904477869879365 424944380232089600602381)
                  ·
                    rfl

theorem cell22_3724093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 2, 2, 2, 4].length) (baseStart_3724093 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3724093 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3724093 prefixEnd_3724093 := by exact prefixLift 3724093
  have htrace : WordTrace (prefixWord ++ tailWord_3724093) baseStart_3724093 baseEnd_3724093 := by
    simpa [prefixWord, tailWord_3724093, baseEnd_3724093] using wordTrace_append hprefix tailTrace_3724093
  have hstable : (prefixWord ++ tailWord_3724093).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3724093).length < 2 ^ (prefixWord ++ tailWord_3724093).sum := by decide
  have hdescent : baseEnd_3724093 < baseStart_3724093 := by decide
  rcases family_descends (prefixWord ++ tailWord_3724093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3724119 : List Nat := [1, 1, 3, 2, 4, 2, 1, 2, 3, 3]
def baseStart_3724119 : Nat := 118140960795 + 3724119 * 2 ^ 59
def prefixEnd_3724119 : Nat := 4983230072969 + 3 ^ 40 * 3724119 * 2
def baseEnd_3724119 : Nat := 1274842041027613400657063

theorem tailTrace_3724119 : CollatzResearch.WordTrace tailWord_3724119 prefixEnd_3724119 1274842041027613400657063 := by
  unfold tailWord_3724119
  simp only [CollatzResearch.WordTrace]
  refine ⟨135829778795160366733463411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90553185863440244488975607 135829778795160366733463411)
  ·
    refine ⟨203744668192740550100195117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135829778795160366733463411 203744668192740550100195117)
    ·
      refine ⟨76404250572277706287573169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 203744668192740550100195117 76404250572277706287573169)
      ·
        refine ⟨57303187929208279715679877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76404250572277706287573169 57303187929208279715679877)
        ·
          refine ⟨10744347736726552446689977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 57303187929208279715679877 10744347736726552446689977)
          ·
            refine ⟨8058260802544914335017483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10744347736726552446689977 8058260802544914335017483)
            ·
              refine ⟨12087391203817371502526225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8058260802544914335017483 12087391203817371502526225)
              ·
                refine ⟨9065543402863028626894669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12087391203817371502526225 9065543402863028626894669)
                ·
                  refine ⟨3399578776073635735085501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9065543402863028626894669 3399578776073635735085501)
                  ·
                    refine ⟨1274842041027613400657063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3399578776073635735085501 1274842041027613400657063)
                    ·
                      rfl

theorem cell22_3724119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 1, 2, 3, 3].length) (baseStart_3724119 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3724119 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3724119 prefixEnd_3724119 := by exact prefixLift 3724119
  have htrace : WordTrace (prefixWord ++ tailWord_3724119) baseStart_3724119 baseEnd_3724119 := by
    simpa [prefixWord, tailWord_3724119, baseEnd_3724119] using wordTrace_append hprefix tailTrace_3724119
  have hstable : (prefixWord ++ tailWord_3724119).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3724119).length < 2 ^ (prefixWord ++ tailWord_3724119).sum := by decide
  have hdescent : baseEnd_3724119 < baseStart_3724119 := by decide
  rcases family_descends (prefixWord ++ tailWord_3724119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3724136 : List Nat := [2, 1, 4, 2, 1, 2, 1, 5, 1, 3]
def baseStart_3724136 : Nat := 118140960795 + 3724136 * 2 ^ 59
def prefixEnd_3724136 : Nat := 4983230072969 + 3 ^ 40 * 3724136 * 2
def baseEnd_3724136 : Nat := 1274847860475031022982011

theorem tailTrace_3724136 : CollatzResearch.WordTrace tailWord_3724136 prefixEnd_3724136 1274847860475031022982011 := by
  unfold tailWord_3724136
  simp only [CollatzResearch.WordTrace]
  refine ⟨67915199418049389318416131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90553599224065852424554841 67915199418049389318416131)
  ·
    refine ⟨101872799127074083977624197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67915199418049389318416131 101872799127074083977624197)
    ·
      refine ⟨19101149836326390745804537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 101872799127074083977624197 19101149836326390745804537)
      ·
        refine ⟨14325862377244793059353403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19101149836326390745804537 14325862377244793059353403)
        ·
          refine ⟨21488793565867189589030105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14325862377244793059353403 21488793565867189589030105)
          ·
            refine ⟨16116595174400392191772579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21488793565867189589030105 16116595174400392191772579)
            ·
              refine ⟨24174892761600588287658869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16116595174400392191772579 24174892761600588287658869)
              ·
                refine ⟨2266396196400055151968019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24174892761600588287658869 2266396196400055151968019)
                ·
                  refine ⟨3399594294600082727952029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2266396196400055151968019 3399594294600082727952029)
                  ·
                    refine ⟨1274847860475031022982011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3399594294600082727952029 1274847860475031022982011)
                    ·
                      rfl

theorem cell22_3724136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 1, 5, 1, 3].length) (baseStart_3724136 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3724136 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3724136 prefixEnd_3724136 := by exact prefixLift 3724136
  have htrace : WordTrace (prefixWord ++ tailWord_3724136) baseStart_3724136 baseEnd_3724136 := by
    simpa [prefixWord, tailWord_3724136, baseEnd_3724136] using wordTrace_append hprefix tailTrace_3724136
  have hstable : (prefixWord ++ tailWord_3724136).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3724136).length < 2 ^ (prefixWord ++ tailWord_3724136).sum := by decide
  have hdescent : baseEnd_3724136 < baseStart_3724136 := by decide
  rcases family_descends (prefixWord ++ tailWord_3724136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3724149 : List Nat := [1, 3, 4, 1, 1, 2, 3, 2, 5]
def baseStart_3724149 : Nat := 118140960795 + 3724149 * 2 ^ 59
def prefixEnd_3724149 : Nat := 4983230072969 + 3 ^ 40 * 3724149 * 2
def baseEnd_3724149 : Nat := 424950770213567774135657

theorem tailTrace_3724149 : CollatzResearch.WordTrace tailWord_3724149 prefixEnd_3724149 424950770213567774135657 := by
  unfold tailWord_3724149
  simp only [CollatzResearch.WordTrace]
  refine ⟨135830872985051681857055501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90553915323367787904703667 135830872985051681857055501)
  ·
    refine ⟨50936577369394380696395813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135830872985051681857055501 50936577369394380696395813)
    ·
      refine ⟨9550608256761446380574215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50936577369394380696395813 9550608256761446380574215)
      ·
        refine ⟨14325912385142169570861323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9550608256761446380574215 14325912385142169570861323)
        ·
          refine ⟨21488868577713254356291985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14325912385142169570861323 21488868577713254356291985)
          ·
            refine ⟨16116651433284940767218989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21488868577713254356291985 16116651433284940767218989)
            ·
              refine ⟨6043744287481852787707121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16116651433284940767218989 6043744287481852787707121)
              ·
                refine ⟨4532808215611389590780341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6043744287481852787707121 4532808215611389590780341)
                ·
                  refine ⟨424950770213567774135657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4532808215611389590780341 424950770213567774135657)
                  ·
                    rfl

theorem cell22_3724149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 3, 2, 5].length) (baseStart_3724149 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3724149 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3724149 prefixEnd_3724149 := by exact prefixLift 3724149
  have htrace : WordTrace (prefixWord ++ tailWord_3724149) baseStart_3724149 baseEnd_3724149 := by
    simpa [prefixWord, tailWord_3724149, baseEnd_3724149] using wordTrace_append hprefix tailTrace_3724149
  have hstable : (prefixWord ++ tailWord_3724149).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3724149).length < 2 ^ (prefixWord ++ tailWord_3724149).sum := by decide
  have hdescent : baseEnd_3724149 < baseStart_3724149 := by decide
  rcases family_descends (prefixWord ++ tailWord_3724149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3724192 : List Nat := [2, 1, 1, 4, 1, 1, 2, 4, 1, 5]
def baseStart_3724192 : Nat := 118140960795 + 3724192 * 2 ^ 59
def prefixEnd_3724192 : Nat := 4983230072969 + 3 ^ 40 * 3724192 * 2
def baseEnd_3724192 : Nat := 1274867030419465543581839

theorem tailTrace_3724192 : CollatzResearch.WordTrace tailWord_3724192 prefixEnd_3724192 1274867030419465543581839 := by
  unfold tailWord_3724192
  simp only [CollatzResearch.WordTrace]
  refine ⟨67916220661947950100435415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90554960882597266800580553 67916220661947950100435415)
  ·
    refine ⟨101874330992921925150653123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67916220661947950100435415 101874330992921925150653123)
    ·
      refine ⟨152811496489382887725979685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101874330992921925150653123 152811496489382887725979685)
      ·
        refine ⟨28652155591759291448621191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 152811496489382887725979685 28652155591759291448621191)
        ·
          refine ⟨42978233387638937172931787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28652155591759291448621191 42978233387638937172931787)
          ·
            refine ⟨64467350081458405759397681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42978233387638937172931787 64467350081458405759397681)
            ·
              refine ⟨48350512561093804319548261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64467350081458405759397681 48350512561093804319548261)
              ·
                refine ⟨9065721105205088309915299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48350512561093804319548261 9065721105205088309915299)
                ·
                  refine ⟨13598581657807632464872949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9065721105205088309915299 13598581657807632464872949)
                  ·
                    refine ⟨1274867030419465543581839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13598581657807632464872949 1274867030419465543581839)
                    ·
                      rfl

theorem cell22_3724192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 4, 1, 5].length) (baseStart_3724192 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3724192 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3724192 prefixEnd_3724192 := by exact prefixLift 3724192
  have htrace : WordTrace (prefixWord ++ tailWord_3724192) baseStart_3724192 baseEnd_3724192 := by
    simpa [prefixWord, tailWord_3724192, baseEnd_3724192] using wordTrace_append hprefix tailTrace_3724192
  have hstable : (prefixWord ++ tailWord_3724192).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3724192).length < 2 ^ (prefixWord ++ tailWord_3724192).sum := by decide
  have hdescent : baseEnd_3724192 < baseStart_3724192 := by decide
  rcases family_descends (prefixWord ++ tailWord_3724192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3724284 : List Nat := [2, 2, 2, 1, 2, 3, 2, 3, 5]
def baseStart_3724284 : Nat := 118140960795 + 3724284 * 2 ^ 59
def prefixEnd_3724284 : Nat := 4983230072969 + 3 ^ 40 * 3724284 * 2
def baseEnd_3724284 : Nat := 424966174633202656760519

theorem tailTrace_3724284 : CollatzResearch.WordTrace tailWord_3724284 prefixEnd_3724284 424966174633202656760519 := by
  unfold tailWord_3724284
  simp only [CollatzResearch.WordTrace]
  refine ⟨67917898419781299956609953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90557197893041733275479937 67917898419781299956609953)
  ·
    refine ⟨50938423814835974967457465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67917898419781299956609953 50938423814835974967457465)
    ·
      refine ⟨38203817861126981225593099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50938423814835974967457465 38203817861126981225593099)
      ·
        refine ⟨57305726791690471838389649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38203817861126981225593099 57305726791690471838389649)
        ·
          refine ⟨42979295093767853878792237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57305726791690471838389649 42979295093767853878792237)
          ·
            refine ⟨16117235660162945204547089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42979295093767853878792237 16117235660162945204547089)
            ·
              refine ⟨12087926745122208903410317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16117235660162945204547089 12087926745122208903410317)
              ·
                refine ⟨4532972529420828338778869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12087926745122208903410317 4532972529420828338778869)
                ·
                  refine ⟨424966174633202656760519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4532972529420828338778869 424966174633202656760519)
                  ·
                    rfl

theorem cell22_3724284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 2, 3, 5].length) (baseStart_3724284 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3724284 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3724284 prefixEnd_3724284 := by exact prefixLift 3724284
  have htrace : WordTrace (prefixWord ++ tailWord_3724284) baseStart_3724284 baseEnd_3724284 := by
    simpa [prefixWord, tailWord_3724284, baseEnd_3724284] using wordTrace_append hprefix tailTrace_3724284
  have hstable : (prefixWord ++ tailWord_3724284).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3724284).length < 2 ^ (prefixWord ++ tailWord_3724284).sum := by decide
  have hdescent : baseEnd_3724284 < baseStart_3724284 := by decide
  rcases family_descends (prefixWord ++ tailWord_3724284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3724359 : List Nat := [1, 1, 4, 1, 3, 2, 2, 1, 1, 6]
def baseStart_3724359 : Nat := 118140960795 + 3724359 * 2 ^ 59
def prefixEnd_3724359 : Nat := 4983230072969 + 3 ^ 40 * 3724359 * 2
def baseEnd_3724359 : Nat := 1274924197932332774656327

theorem tailTrace_3724359 : CollatzResearch.WordTrace tailWord_3724359 prefixEnd_3724359 1274924197932332774656327 := by
  unfold tailWord_3724359
  simp only [CollatzResearch.WordTrace]
  refine ⟨135838532314290887722200131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90559021542860591814800087 135838532314290887722200131)
  ·
    refine ⟨203757798471436331583300197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135838532314290887722200131 203757798471436331583300197)
    ·
      refine ⟨38204587213394312171868787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 203757798471436331583300197 38204587213394312171868787)
      ·
        refine ⟨57306880820091468257803181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38204587213394312171868787 57306880820091468257803181)
        ·
          refine ⟨21490080307534300596676193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57306880820091468257803181 21490080307534300596676193)
          ·
            refine ⟨16117560230650725447507145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21490080307534300596676193 16117560230650725447507145)
            ·
              refine ⟨12088170172988044085630359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16117560230650725447507145 12088170172988044085630359)
              ·
                refine ⟨18132255259482066128445539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12088170172988044085630359 18132255259482066128445539)
                ·
                  refine ⟨27198382889223099192668309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18132255259482066128445539 27198382889223099192668309)
                  ·
                    refine ⟨1274924197932332774656327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27198382889223099192668309 1274924197932332774656327)
                    ·
                      rfl

theorem cell22_3724359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 2, 1, 1, 6].length) (baseStart_3724359 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3724359 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3724359 prefixEnd_3724359 := by exact prefixLift 3724359
  have htrace : WordTrace (prefixWord ++ tailWord_3724359) baseStart_3724359 baseEnd_3724359 := by
    simpa [prefixWord, tailWord_3724359, baseEnd_3724359] using wordTrace_append hprefix tailTrace_3724359
  have hstable : (prefixWord ++ tailWord_3724359).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3724359).length < 2 ^ (prefixWord ++ tailWord_3724359).sum := by decide
  have hdescent : baseEnd_3724359 < baseStart_3724359 := by decide
  rcases family_descends (prefixWord ++ tailWord_3724359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3724423 : List Nat := [1, 1, 4, 2, 1, 1, 1, 7, 1, 3]
def baseStart_3724423 : Nat := 118140960795 + 3724423 * 2 ^ 59
def prefixEnd_3724423 : Nat := 4983230072969 + 3 ^ 40 * 3724423 * 2
def baseEnd_3724423 : Nat := 1274946106440257941056131

theorem tailTrace_3724423 : CollatzResearch.WordTrace tailWord_3724423 prefixEnd_3724423 1274946106440257941056131 := by
  unfold tailWord_3724423
  simp only [CollatzResearch.WordTrace]
  refine ⟨135840866586059026652529923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90560577724039351101686615 135840866586059026652529923)
  ·
    refine ⟨203761299879088539978794885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135840866586059026652529923 203761299879088539978794885)
    ·
      refine ⟨38205243727329101246024041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 203761299879088539978794885 38205243727329101246024041)
      ·
        refine ⟨28653932795496825934518031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38205243727329101246024041 28653932795496825934518031)
        ·
          refine ⟨42980899193245238901777047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28653932795496825934518031 42980899193245238901777047)
          ·
            refine ⟨64471348789867858352665571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42980899193245238901777047 64471348789867858352665571)
            ·
              refine ⟨96707023184801787528998357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64471348789867858352665571 96707023184801787528998357)
              ·
                refine ⟨2266570855893791895210899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 96707023184801787528998357 2266570855893791895210899)
                ·
                  refine ⟨3399856283840687842816349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2266570855893791895210899 3399856283840687842816349)
                  ·
                    refine ⟨1274946106440257941056131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3399856283840687842816349 1274946106440257941056131)
                    ·
                      rfl

theorem cell22_3724423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 7, 1, 3].length) (baseStart_3724423 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3724423 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3724423 prefixEnd_3724423 := by exact prefixLift 3724423
  have htrace : WordTrace (prefixWord ++ tailWord_3724423) baseStart_3724423 baseEnd_3724423 := by
    simpa [prefixWord, tailWord_3724423, baseEnd_3724423] using wordTrace_append hprefix tailTrace_3724423
  have hstable : (prefixWord ++ tailWord_3724423).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3724423).length < 2 ^ (prefixWord ++ tailWord_3724423).sum := by decide
  have hdescent : baseEnd_3724423 < baseStart_3724423 := by decide
  rcases family_descends (prefixWord ++ tailWord_3724423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3724440 : List Nat := [2, 1, 2, 4, 2, 2, 1, 4, 1, 3]
def baseStart_3724440 : Nat := 118140960795 + 3724440 * 2 ^ 59
def prefixEnd_3724440 : Nat := 4983230072969 + 3 ^ 40 * 3724440 * 2
def baseEnd_3724440 : Nat := 1274951925887675563381079

theorem tailTrace_3724440 : CollatzResearch.WordTrace tailWord_3724440 prefixEnd_3724440 1274951925887675563381079 := by
  unfold tailWord_3724440
  simp only [CollatzResearch.WordTrace]
  refine ⟨67920743313498719277949387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90560991084664959037265849 67920743313498719277949387)
  ·
    refine ⟨101881114970248078916924081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67920743313498719277949387 101881114970248078916924081)
    ·
      refine ⟨76410836227686059187693061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101881114970248078916924081 76410836227686059187693061)
      ·
        refine ⟨14327031792691136097692449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 76410836227686059187693061 14327031792691136097692449)
        ·
          refine ⟨10745273844518352073269337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14327031792691136097692449 10745273844518352073269337)
          ·
            refine ⟨8058955383388764054952003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10745273844518352073269337 8058955383388764054952003)
            ·
              refine ⟨12088433075083146082428005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8058955383388764054952003 12088433075083146082428005)
              ·
                refine ⟨2266581201578089890455251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12088433075083146082428005 2266581201578089890455251)
                ·
                  refine ⟨3399871802367134835682877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2266581201578089890455251 3399871802367134835682877)
                  ·
                    refine ⟨1274951925887675563381079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3399871802367134835682877 1274951925887675563381079)
                    ·
                      rfl

theorem cell22_3724440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 1, 4, 1, 3].length) (baseStart_3724440 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3724440 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3724440 prefixEnd_3724440 := by exact prefixLift 3724440
  have htrace : WordTrace (prefixWord ++ tailWord_3724440) baseStart_3724440 baseEnd_3724440 := by
    simpa [prefixWord, tailWord_3724440, baseEnd_3724440] using wordTrace_append hprefix tailTrace_3724440
  have hstable : (prefixWord ++ tailWord_3724440).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3724440).length < 2 ^ (prefixWord ++ tailWord_3724440).sum := by decide
  have hdescent : baseEnd_3724440 < baseStart_3724440 := by decide
  rcases family_descends (prefixWord ++ tailWord_3724440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3724464 : List Nat := [2, 1, 1, 1, 2, 1, 2, 6, 6]
def baseStart_3724464 : Nat := 118140960795 + 3724464 * 2 ^ 59
def prefixEnd_3724464 : Nat := 4983230072969 + 3 ^ 40 * 3724464 * 2
def baseEnd_3724464 : Nat := 424986713859382500260335

theorem tailTrace_3724464 : CollatzResearch.WordTrace tailWord_3724464 prefixEnd_3724464 424986713859382500260335 := by
  unfold tailWord_3724464
  simp only [CollatzResearch.WordTrace]
  refine ⟨67921180989455245327386223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90561574652606993769848297 67921180989455245327386223)
  ·
    refine ⟨101881771484182867991079335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67921180989455245327386223 101881771484182867991079335)
    ·
      refine ⟨152822657226274301986619003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101881771484182867991079335 152822657226274301986619003)
      ·
        refine ⟨229233985839411452979928505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152822657226274301986619003 229233985839411452979928505)
        ·
          refine ⟨171925489379558589734946379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 229233985839411452979928505 171925489379558589734946379)
          ·
            refine ⟨257888234069337884602419569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 171925489379558589734946379 257888234069337884602419569)
            ·
              refine ⟨193416175552003413451814677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 257888234069337884602419569 193416175552003413451814677)
              ·
                refine ⟨9066383229000160005553813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 193416175552003413451814677 9066383229000160005553813)
                ·
                  refine ⟨424986713859382500260335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9066383229000160005553813 424986713859382500260335)
                  ·
                    rfl

theorem cell22_3724464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 6, 6].length) (baseStart_3724464 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3724464 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3724464 prefixEnd_3724464 := by exact prefixLift 3724464
  have htrace : WordTrace (prefixWord ++ tailWord_3724464) baseStart_3724464 baseEnd_3724464 := by
    simpa [prefixWord, tailWord_3724464, baseEnd_3724464] using wordTrace_append hprefix tailTrace_3724464
  have hstable : (prefixWord ++ tailWord_3724464).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3724464).length < 2 ^ (prefixWord ++ tailWord_3724464).sum := by decide
  have hdescent : baseEnd_3724464 < baseStart_3724464 := by decide
  rcases family_descends (prefixWord ++ tailWord_3724464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3724466 : List Nat := [3, 2, 1, 1, 1, 4, 2, 1, 3, 4]
def baseStart_3724466 : Nat := 118140960795 + 3724466 * 2 ^ 59
def prefixEnd_3724466 : Nat := 4983230072969 + 3 ^ 40 * 3724466 * 2
def baseEnd_3724466 : Nat := 1274960826219020162230999

theorem tailTrace_3724466 : CollatzResearch.WordTrace tailWord_3724466 prefixEnd_3724466 1274960826219020162230999 := by
  unfold tailWord_3724466
  simp only [CollatzResearch.WordTrace]
  refine ⟨33960608731225811249086313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90561623283268829997563501 33960608731225811249086313)
  ·
    refine ⟨25470456548419358436814735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33960608731225811249086313 25470456548419358436814735)
    ·
      refine ⟨38205684822629037655222103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25470456548419358436814735 38205684822629037655222103)
      ·
        refine ⟨57308527233943556482833155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38205684822629037655222103 57308527233943556482833155)
        ·
          refine ⟨85962790850915334724249733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57308527233943556482833155 85962790850915334724249733)
          ·
            refine ⟨16118023284546625260796825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 85962790850915334724249733 16118023284546625260796825)
            ·
              refine ⟨12088517463409968945597619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16118023284546625260796825 12088517463409968945597619)
              ·
                refine ⟨18132776195114953418396429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12088517463409968945597619 18132776195114953418396429)
                ·
                  refine ⟨6799791073168107531898661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18132776195114953418396429 6799791073168107531898661)
                  ·
                    refine ⟨1274960826219020162230999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6799791073168107531898661 1274960826219020162230999)
                    ·
                      rfl

theorem cell22_3724466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 2, 1, 3, 4].length) (baseStart_3724466 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3724466 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3724466 prefixEnd_3724466 := by exact prefixLift 3724466
  have htrace : WordTrace (prefixWord ++ tailWord_3724466) baseStart_3724466 baseEnd_3724466 := by
    simpa [prefixWord, tailWord_3724466, baseEnd_3724466] using wordTrace_append hprefix tailTrace_3724466
  have hstable : (prefixWord ++ tailWord_3724466).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3724466).length < 2 ^ (prefixWord ++ tailWord_3724466).sum := by decide
  have hdescent : baseEnd_3724466 < baseStart_3724466 := by decide
  rcases family_descends (prefixWord ++ tailWord_3724466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3724498 : List Nat := [3, 2, 2, 2, 1, 1, 1, 6, 4]
def baseStart_3724498 : Nat := 118140960795 + 3724498 * 2 ^ 59
def prefixEnd_3724498 : Nat := 4983230072969 + 3 ^ 40 * 3724498 * 2
def baseEnd_3724498 : Nat := 424990593490994248476967

theorem tailTrace_3724498 : CollatzResearch.WordTrace tailWord_3724498 prefixEnd_3724498 424990593490994248476967 := by
  unfold tailWord_3724498
  simp only [CollatzResearch.WordTrace]
  refine ⟨33960900515196828615377537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90562401373858209641006765 33960900515196828615377537)
  ·
    refine ⟨25470675386397621461533153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33960900515196828615377537 25470675386397621461533153)
    ·
      refine ⟨19103006539798216096149865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25470675386397621461533153 19103006539798216096149865)
      ·
        refine ⟨14327254904848662072112399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19103006539798216096149865 14327254904848662072112399)
        ·
          refine ⟨21490882357272993108168599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14327254904848662072112399 21490882357272993108168599)
          ·
            refine ⟨32236323535909489662252899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21490882357272993108168599 32236323535909489662252899)
            ·
              refine ⟨48354485303864234493379349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32236323535909489662252899 48354485303864234493379349)
              ·
                refine ⟨2266616498618635991877157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 48354485303864234493379349 2266616498618635991877157)
                ·
                  refine ⟨424990593490994248476967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2266616498618635991877157 424990593490994248476967)
                  ·
                    rfl

theorem cell22_3724498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 6, 4].length) (baseStart_3724498 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3724498 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3724498 prefixEnd_3724498 := by exact prefixLift 3724498
  have htrace : WordTrace (prefixWord ++ tailWord_3724498) baseStart_3724498 baseEnd_3724498 := by
    simpa [prefixWord, tailWord_3724498, baseEnd_3724498] using wordTrace_append hprefix tailTrace_3724498
  have hstable : (prefixWord ++ tailWord_3724498).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3724498).length < 2 ^ (prefixWord ++ tailWord_3724498).sum := by decide
  have hdescent : baseEnd_3724498 < baseStart_3724498 := by decide
  rcases family_descends (prefixWord ++ tailWord_3724498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3724513 : List Nat := [1, 2, 3, 1, 3, 4, 1, 1, 1, 5]
def baseStart_3724513 : Nat := 118140960795 + 3724513 * 2 ^ 59
def prefixEnd_3724513 : Nat := 4983230072969 + 3 ^ 40 * 3724513 * 2
def baseEnd_3724513 : Nat := 1274976915279527706305855

theorem tailTrace_3724513 : CollatzResearch.WordTrace tailWord_3724513 prefixEnd_3724513 1274976915279527706305855 := by
  unfold tailWord_3724513
  simp only [CollatzResearch.WordTrace]
  refine ⟨135844149155732972023306193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90562766103821981348870795 135844149155732972023306193)
  ·
    refine ⟨101883111866799729017479645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135844149155732972023306193 101883111866799729017479645)
    ·
      refine ⟨38206166950049898381554867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101883111866799729017479645 38206166950049898381554867)
      ·
        refine ⟨57309250425074847572332301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38206166950049898381554867 57309250425074847572332301)
        ·
          refine ⟨21490968909403067839624613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57309250425074847572332301 21490968909403067839624613)
          ·
            refine ⟨4029556670513075219929615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21490968909403067839624613 4029556670513075219929615)
            ·
              refine ⟨6044335005769612829894423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4029556670513075219929615 6044335005769612829894423)
              ·
                refine ⟨9066502508654419244841635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6044335005769612829894423 9066502508654419244841635)
                ·
                  refine ⟨13599753762981628867262453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9066502508654419244841635 13599753762981628867262453)
                  ·
                    refine ⟨1274976915279527706305855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13599753762981628867262453 1274976915279527706305855)
                    ·
                      rfl

theorem cell22_3724513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 4, 1, 1, 1, 5].length) (baseStart_3724513 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3724513 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3724513 prefixEnd_3724513 := by exact prefixLift 3724513
  have htrace : WordTrace (prefixWord ++ tailWord_3724513) baseStart_3724513 baseEnd_3724513 := by
    simpa [prefixWord, tailWord_3724513, baseEnd_3724513] using wordTrace_append hprefix tailTrace_3724513
  have hstable : (prefixWord ++ tailWord_3724513).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3724513).length < 2 ^ (prefixWord ++ tailWord_3724513).sum := by decide
  have hdescent : baseEnd_3724513 < baseStart_3724513 := by decide
  rcases family_descends (prefixWord ++ tailWord_3724513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3724609 : List Nat := [1, 2, 5, 2, 1, 1, 4, 2, 1, 3]
def baseStart_3724609 : Nat := 118140960795 + 3724609 * 2 ^ 59
def prefixEnd_3724609 : Nat := 4983230072969 + 3 ^ 40 * 3724609 * 2
def baseEnd_3724609 : Nat := 1275009778041415455905561

theorem tailTrace_3724609 : CollatzResearch.WordTrace tailWord_3724609 prefixEnd_3724609 1275009778041415455905561 := by
  unfold tailWord_3724609
  simp only [CollatzResearch.WordTrace]
  refine ⟨135847650563385180418800881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90565100375590120279200587 135847650563385180418800881)
  ·
    refine ⟨101885737922538885314100661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135847650563385180418800881 101885737922538885314100661)
    ·
      refine ⟨9551787930238020498196937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 101885737922538885314100661 9551787930238020498196937)
      ·
        refine ⟨7163840947678515373647703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9551787930238020498196937 7163840947678515373647703)
        ·
          refine ⟨10745761421517773060471555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7163840947678515373647703 10745761421517773060471555)
          ·
            refine ⟨16118642132276659590707333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10745761421517773060471555 16118642132276659590707333)
            ·
              refine ⟨3022245399801873673257625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16118642132276659590707333 3022245399801873673257625)
              ·
                refine ⟨2266684049851405254943219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3022245399801873673257625 2266684049851405254943219)
                ·
                  refine ⟨3400026074777107882414829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2266684049851405254943219 3400026074777107882414829)
                  ·
                    refine ⟨1275009778041415455905561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3400026074777107882414829 1275009778041415455905561)
                    ·
                      rfl

theorem cell22_3724609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 4, 2, 1, 3].length) (baseStart_3724609 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3724609 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3724609 prefixEnd_3724609 := by exact prefixLift 3724609
  have htrace : WordTrace (prefixWord ++ tailWord_3724609) baseStart_3724609 baseEnd_3724609 := by
    simpa [prefixWord, tailWord_3724609, baseEnd_3724609] using wordTrace_append hprefix tailTrace_3724609
  have hstable : (prefixWord ++ tailWord_3724609).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3724609).length < 2 ^ (prefixWord ++ tailWord_3724609).sum := by decide
  have hdescent : baseEnd_3724609 < baseStart_3724609 := by decide
  rcases family_descends (prefixWord ++ tailWord_3724609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3724616 : List Nat := [2, 1, 3, 1, 1, 2, 1, 5, 6]
def baseStart_3724616 : Nat := 118140960795 + 3724616 * 2 ^ 59
def prefixEnd_3724616 : Nat := 4983230072969 + 3 ^ 40 * 3724616 * 2
def baseEnd_3724616 : Nat := 425004058094823256993513

theorem tailTrace_3724616 : CollatzResearch.WordTrace tailWord_3724616 prefixEnd_3724616 425004058094823256993513 := by
  unfold tailWord_3724616
  simp only [CollatzResearch.WordTrace]
  refine ⟨67923952937179910307152851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90565270582906547076203801 67923952937179910307152851)
  ·
    refine ⟨101885929405769865460729277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67923952937179910307152851 101885929405769865460729277)
    ·
      refine ⟨38207223527163699547773479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101885929405769865460729277 38207223527163699547773479)
      ·
        refine ⟨57310835290745549321660219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38207223527163699547773479 57310835290745549321660219)
        ·
          refine ⟨85966252936118323982490329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57310835290745549321660219 85966252936118323982490329)
          ·
            refine ⟨64474689702088742986867747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85966252936118323982490329 64474689702088742986867747)
            ·
              refine ⟨96712034553133114480301621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64474689702088742986867747 96712034553133114480301621)
              ·
                refine ⟨9066753239356229482528277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 96712034553133114480301621 9066753239356229482528277)
                ·
                  refine ⟨425004058094823256993513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9066753239356229482528277 425004058094823256993513)
                  ·
                    rfl

theorem cell22_3724616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 5, 6].length) (baseStart_3724616 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3724616 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3724616 prefixEnd_3724616 := by exact prefixLift 3724616
  have htrace : WordTrace (prefixWord ++ tailWord_3724616) baseStart_3724616 baseEnd_3724616 := by
    simpa [prefixWord, tailWord_3724616, baseEnd_3724616] using wordTrace_append hprefix tailTrace_3724616
  have hstable : (prefixWord ++ tailWord_3724616).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3724616).length < 2 ^ (prefixWord ++ tailWord_3724616).sum := by decide
  have hdescent : baseEnd_3724616 < baseStart_3724616 := by decide
  rcases family_descends (prefixWord ++ tailWord_3724616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3724652 : List Nat := [2, 2, 1, 1, 5, 3, 2, 1, 1, 4]
def baseStart_3724652 : Nat := 118140960795 + 3724652 * 2 ^ 59
def prefixEnd_3724652 : Nat := 4983230072969 + 3 ^ 40 * 3724652 * 2
def baseEnd_3724652 : Nat := 1275024497820177677080429

theorem tailTrace_3724652 : CollatzResearch.WordTrace tailWord_3724652 prefixEnd_3724652 1275024497820177677080429 := by
  unfold tailWord_3724652
  simp only [CollatzResearch.WordTrace]
  refine ⟨67924609451114699381308105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90566145934819599175077473 67924609451114699381308105)
  ·
    refine ⟨50943457088336024535981079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67924609451114699381308105 50943457088336024535981079)
    ·
      refine ⟨76415185632504036803971619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50943457088336024535981079 76415185632504036803971619)
      ·
        refine ⟨114622778448756055205957429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76415185632504036803971619 114622778448756055205957429)
        ·
          refine ⟨10745885479570880175558509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 114622778448756055205957429 10745885479570880175558509)
          ·
            refine ⟨4029707054839080065834441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10745885479570880175558509 4029707054839080065834441)
            ·
              refine ⟨3022280291129310049375831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4029707054839080065834441 3022280291129310049375831)
              ·
                refine ⟨4533420436693965074063747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3022280291129310049375831 4533420436693965074063747)
                ·
                  refine ⟨6800130655040947611095621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4533420436693965074063747 6800130655040947611095621)
                  ·
                    refine ⟨1275024497820177677080429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6800130655040947611095621 1275024497820177677080429)
                    ·
                      rfl

theorem cell22_3724652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 4].length) (baseStart_3724652 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3724652 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3724652 prefixEnd_3724652 := by exact prefixLift 3724652
  have htrace : WordTrace (prefixWord ++ tailWord_3724652) baseStart_3724652 baseEnd_3724652 := by
    simpa [prefixWord, tailWord_3724652, baseEnd_3724652] using wordTrace_append hprefix tailTrace_3724652
  have hstable : (prefixWord ++ tailWord_3724652).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3724652).length < 2 ^ (prefixWord ++ tailWord_3724652).sum := by decide
  have hdescent : baseEnd_3724652 < baseStart_3724652 := by decide
  rcases family_descends (prefixWord ++ tailWord_3724652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3724665 : List Nat := [1, 2, 1, 3, 2, 1, 5, 2, 2, 3]
def baseStart_3724665 : Nat := 118140960795 + 3724665 * 2 ^ 59
def prefixEnd_3724665 : Nat := 4983230072969 + 3 ^ 40 * 3724665 * 2
def baseEnd_3724665 : Nat := 1275028947985849976505389

theorem tailTrace_3724665 : CollatzResearch.WordTrace tailWord_3724665 prefixEnd_3724665 1275028947985849976505389 := by
  unfold tailWord_3724665
  simp only [CollatzResearch.WordTrace]
  refine ⟨135849693051182301982839449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90566462034121534655226299 135849693051182301982839449)
  ·
    refine ⟨101887269788386726487129587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135849693051182301982839449 101887269788386726487129587)
    ·
      refine ⟨152830904682580089730694381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101887269788386726487129587 152830904682580089730694381)
      ·
        refine ⟨57311589255967533649010393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 152830904682580089730694381 57311589255967533649010393)
        ·
          refine ⟨42983691941975650236757795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57311589255967533649010393 42983691941975650236757795)
          ·
            refine ⟨64475537912963475355136693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42983691941975650236757795 64475537912963475355136693)
            ·
              refine ⟨6044581679340325814544065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 64475537912963475355136693 6044581679340325814544065)
              ·
                refine ⟨4533436259505244360908049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6044581679340325814544065 4533436259505244360908049)
                ·
                  refine ⟨3400077194628933270681037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4533436259505244360908049 3400077194628933270681037)
                  ·
                    refine ⟨1275028947985849976505389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3400077194628933270681037 1275028947985849976505389)
                    ·
                      rfl

theorem cell22_3724665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 5, 2, 2, 3].length) (baseStart_3724665 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3724665 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3724665 prefixEnd_3724665 := by exact prefixLift 3724665
  have htrace : WordTrace (prefixWord ++ tailWord_3724665) baseStart_3724665 baseEnd_3724665 := by
    simpa [prefixWord, tailWord_3724665, baseEnd_3724665] using wordTrace_append hprefix tailTrace_3724665
  have hstable : (prefixWord ++ tailWord_3724665).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3724665).length < 2 ^ (prefixWord ++ tailWord_3724665).sum := by decide
  have hdescent : baseEnd_3724665 < baseStart_3724665 := by decide
  rcases family_descends (prefixWord ++ tailWord_3724665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3724712 : List Nat := [2, 1, 6, 1, 3, 1, 8]
def baseStart_3724712 : Nat := 118140960795 + 3724712 * 2 ^ 59
def prefixEnd_3724712 : Nat := 4983230072969 + 3 ^ 40 * 3724712 * 2
def baseEnd_3724712 : Nat := 47223890260976204465935

theorem tailTrace_3724712 : CollatzResearch.WordTrace tailWord_3724712 prefixEnd_3724712 47223890260976204465935 := by
  unfold tailWord_3724712
  simp only [CollatzResearch.WordTrace]
  refine ⟨67925703641006014504900195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90567604854674686006533593 67925703641006014504900195)
  ·
    refine ⟨101888555461509021757350293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67925703641006014504900195 101888555461509021757350293)
    ·
      refine ⟨4776026037258235394875795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 101888555461509021757350293 4776026037258235394875795)
      ·
        refine ⟨7164039055887353092313693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4776026037258235394875795 7164039055887353092313693)
        ·
          refine ⟨2686514645957757409617635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7164039055887353092313693 2686514645957757409617635)
          ·
            refine ⟨4029771968936636114426453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2686514645957757409617635 4029771968936636114426453)
            ·
              refine ⟨47223890260976204465935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4029771968936636114426453 47223890260976204465935)
              ·
                rfl

theorem cell22_3724712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 3, 1, 8].length) (baseStart_3724712 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3724712 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3724712 prefixEnd_3724712 := by exact prefixLift 3724712
  have htrace : WordTrace (prefixWord ++ tailWord_3724712) baseStart_3724712 baseEnd_3724712 := by
    simpa [prefixWord, tailWord_3724712, baseEnd_3724712] using wordTrace_append hprefix tailTrace_3724712
  have hstable : (prefixWord ++ tailWord_3724712).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3724712).length < 2 ^ (prefixWord ++ tailWord_3724712).sum := by decide
  have hdescent : baseEnd_3724712 < baseStart_3724712 := by decide
  rcases family_descends (prefixWord ++ tailWord_3724712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3724778 : List Nat := [3, 1, 3, 1, 5, 1, 2, 2, 1, 3]
def baseStart_3724778 : Nat := 118140960795 + 3724778 * 2 ^ 59
def prefixEnd_3724778 : Nat := 4983230072969 + 3 ^ 40 * 3724778 * 2
def baseEnd_3724778 : Nat := 1275067630195155348430043

theorem tailTrace_3724778 : CollatzResearch.WordTrace tailWord_3724778 prefixEnd_3724778 1275067630195155348430043 := by
  unfold tailWord_3724778
  simp only [CollatzResearch.WordTrace]
  refine ⟨33963453624943230570425747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90569209666515281521135325 33963453624943230570425747)
  ·
    refine ⟨50945180437414845855638621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33963453624943230570425747 50945180437414845855638621)
    ·
      refine ⟨19104442664030567195864483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50945180437414845855638621 19104442664030567195864483)
      ·
        refine ⟨28656663996045850793796725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19104442664030567195864483 28656663996045850793796725)
        ·
          refine ⟨2686562249629298511918443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 28656663996045850793796725 2686562249629298511918443)
          ·
            refine ⟨4029843374443947767877665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2686562249629298511918443 4029843374443947767877665)
            ·
              refine ⟨3022382530832960825908249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4029843374443947767877665 3022382530832960825908249)
              ·
                refine ⟨2266786898124720619431187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3022382530832960825908249 2266786898124720619431187)
                ·
                  refine ⟨3400180347187080929146781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2266786898124720619431187 3400180347187080929146781)
                  ·
                    refine ⟨1275067630195155348430043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3400180347187080929146781 1275067630195155348430043)
                    ·
                      rfl

theorem cell22_3724778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 5, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 5, 1, 2, 2, 1, 3].length) (baseStart_3724778 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3724778 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3724778 prefixEnd_3724778 := by exact prefixLift 3724778
  have htrace : WordTrace (prefixWord ++ tailWord_3724778) baseStart_3724778 baseEnd_3724778 := by
    simpa [prefixWord, tailWord_3724778, baseEnd_3724778] using wordTrace_append hprefix tailTrace_3724778
  have hstable : (prefixWord ++ tailWord_3724778).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3724778).length < 2 ^ (prefixWord ++ tailWord_3724778).sum := by decide
  have hdescent : baseEnd_3724778 < baseStart_3724778 := by decide
  rcases family_descends (prefixWord ++ tailWord_3724778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3724802 : List Nat := [3, 4, 1, 2, 1, 2, 1, 2, 6]
def baseStart_3724802 : Nat := 118140960795 + 3724802 * 2 ^ 59
def prefixEnd_3724802 : Nat := 4983230072969 + 3 ^ 40 * 3724802 * 2
def baseEnd_3724802 : Nat := 425025281961875761943323

theorem tailTrace_3724802 : CollatzResearch.WordTrace tailWord_3724802 prefixEnd_3724802 425025281961875761943323 := by
  unfold tailWord_3724802
  simp only [CollatzResearch.WordTrace]
  refine ⟨33963672462921493595144165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90569793234457316253717773 33963672462921493595144165)
  ·
    refine ⟨6368188586797780049089531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33963672462921493595144165 6368188586797780049089531)
    ·
      refine ⟨9552282880196670073634297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6368188586797780049089531 9552282880196670073634297)
      ·
        refine ⟨7164212160147502555225723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9552282880196670073634297 7164212160147502555225723)
        ·
          refine ⟨10746318240221253832838585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7164212160147502555225723 10746318240221253832838585)
          ·
            refine ⟨8059738680165940374628939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10746318240221253832838585 8059738680165940374628939)
            ·
              refine ⟨12089608020248910561943409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8059738680165940374628939 12089608020248910561943409)
              ·
                refine ⟨9067206015186682921457557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12089608020248910561943409 9067206015186682921457557)
                ·
                  refine ⟨425025281961875761943323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9067206015186682921457557 425025281961875761943323)
                  ·
                    rfl

theorem cell22_3724802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 1, 2, 6].length) (baseStart_3724802 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3724802 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3724802 prefixEnd_3724802 := by exact prefixLift 3724802
  have htrace : WordTrace (prefixWord ++ tailWord_3724802) baseStart_3724802 baseEnd_3724802 := by
    simpa [prefixWord, tailWord_3724802, baseEnd_3724802] using wordTrace_append hprefix tailTrace_3724802
  have hstable : (prefixWord ++ tailWord_3724802).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3724802).length < 2 ^ (prefixWord ++ tailWord_3724802).sum := by decide
  have hdescent : baseEnd_3724802 < baseStart_3724802 := by decide
  rcases family_descends (prefixWord ++ tailWord_3724802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3724873 : List Nat := [1, 2, 1, 1, 2, 2, 1, 4, 1, 7]
def baseStart_3724873 : Nat := 118140960795 + 3724873 * 2 ^ 59
def prefixEnd_3724873 : Nat := 4983230072969 + 3 ^ 40 * 3724873 * 2
def baseEnd_3724873 : Nat := 1275100150636606767304751

theorem tailTrace_3724873 : CollatzResearch.WordTrace tailWord_3724873 prefixEnd_3724873 1275100150636606767304751 := by
  unfold tailWord_3724873
  simp only [CollatzResearch.WordTrace]
  refine ⟨135857279434428753506411273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90571519622952502337607515 135857279434428753506411273)
  ·
    refine ⟨101892959575821565129808455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135857279434428753506411273 101892959575821565129808455)
    ·
      refine ⟨152839439363732347694712683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101892959575821565129808455 152839439363732347694712683)
      ·
        refine ⟨229259159045598521542069025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152839439363732347694712683 229259159045598521542069025)
        ·
          refine ⟨171944369284198891156551769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 229259159045598521542069025 171944369284198891156551769)
          ·
            refine ⟨128958276963149168367413827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 171944369284198891156551769 128958276963149168367413827)
            ·
              refine ⟨193437415444723752551120741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 128958276963149168367413827 193437415444723752551120741)
              ·
                refine ⟨36269515395885703603335139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 193437415444723752551120741 36269515395885703603335139)
                ·
                  refine ⟨54404273093828555405002709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36269515395885703603335139 54404273093828555405002709)
                  ·
                    refine ⟨1275100150636606767304751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 54404273093828555405002709 1275100150636606767304751)
                    ·
                      rfl

theorem cell22_3724873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 4, 1, 7].length) (baseStart_3724873 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3724873 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3724873 prefixEnd_3724873 := by exact prefixLift 3724873
  have htrace : WordTrace (prefixWord ++ tailWord_3724873) baseStart_3724873 baseEnd_3724873 := by
    simpa [prefixWord, tailWord_3724873, baseEnd_3724873] using wordTrace_append hprefix tailTrace_3724873
  have hstable : (prefixWord ++ tailWord_3724873).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3724873).length < 2 ^ (prefixWord ++ tailWord_3724873).sum := by decide
  have hdescent : baseEnd_3724873 < baseStart_3724873 := by decide
  rcases family_descends (prefixWord ++ tailWord_3724873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3724935 : List Nat := [1, 1, 4, 2, 1, 3, 1, 1, 3, 5]
def baseStart_3724935 : Nat := 118140960795 + 3724935 * 2 ^ 59
def prefixEnd_3724935 : Nat := 4983230072969 + 3 ^ 40 * 3724935 * 2
def baseEnd_3724935 : Nat := 1275121374503659272254561

theorem tailTrace_3724935 : CollatzResearch.WordTrace tailWord_3724935 prefixEnd_3724935 1275121374503659272254561 := by
  unfold tailWord_3724935
  simp only [CollatzResearch.WordTrace]
  refine ⟨135859540760204138095168259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90573027173469425396778839 135859540760204138095168259)
  ·
    refine ⟨203789311140306207142752389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135859540760204138095168259 203789311140306207142752389)
    ·
      refine ⟨38210495838807413839266073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 203789311140306207142752389 38210495838807413839266073)
      ·
        refine ⟨28657871879105560379449555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38210495838807413839266073 28657871879105560379449555)
        ·
          refine ⟨42986807818658340569174333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28657871879105560379449555 42986807818658340569174333)
          ·
            refine ⟨16120052931996877713440375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42986807818658340569174333 16120052931996877713440375)
            ·
              refine ⟨24180079397995316570160563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16120052931996877713440375 24180079397995316570160563)
              ·
                refine ⟨36270119096992974855240845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24180079397995316570160563 36270119096992974855240845)
                ·
                  refine ⟨13601294661372365570715317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36270119096992974855240845 13601294661372365570715317)
                  ·
                    refine ⟨1275121374503659272254561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13601294661372365570715317 1275121374503659272254561)
                    ·
                      rfl

theorem cell22_3724935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 1, 1, 3, 5].length) (baseStart_3724935 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3724935 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3724935 prefixEnd_3724935 := by exact prefixLift 3724935
  have htrace : WordTrace (prefixWord ++ tailWord_3724935) baseStart_3724935 baseEnd_3724935 := by
    simpa [prefixWord, tailWord_3724935, baseEnd_3724935] using wordTrace_append hprefix tailTrace_3724935
  have hstable : (prefixWord ++ tailWord_3724935).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3724935).length < 2 ^ (prefixWord ++ tailWord_3724935).sum := by decide
  have hdescent : baseEnd_3724935 < baseStart_3724935 := by decide
  rcases family_descends (prefixWord ++ tailWord_3724935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3724965 : List Nat := [1, 3, 1, 2, 1, 2, 5, 7]
def baseStart_3724965 : Nat := 118140960795 + 3724965 * 2 ^ 59
def prefixEnd_3724965 : Nat := 4983230072969 + 3 ^ 40 * 3724965 * 2
def baseEnd_3724965 : Nat := 141681293790749910444941

theorem tailTrace_3724965 : CollatzResearch.WordTrace tailWord_3724965 prefixEnd_3724965 141681293790749910444941 := by
  unfold tailWord_3724965
  simp only [CollatzResearch.WordTrace]
  refine ⟨135860634950095453218760349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90573756633396968812506899 135860634950095453218760349)
  ·
    refine ⟨50947738106285794957035131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135860634950095453218760349 50947738106285794957035131)
    ·
      refine ⟨76421607159428692435552697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50947738106285794957035131 76421607159428692435552697)
      ·
        refine ⟨57316205369571519326664523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76421607159428692435552697 57316205369571519326664523)
        ·
          refine ⟨85974308054357278989996785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57316205369571519326664523 85974308054357278989996785)
          ·
            refine ⟨64480731040767959242497589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85974308054357278989996785 64480731040767959242497589)
            ·
              refine ⟨6045068535071996178984149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 64480731040767959242497589 6045068535071996178984149)
              ·
                refine ⟨141681293790749910444941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6045068535071996178984149 141681293790749910444941)
                ·
                  rfl

theorem cell22_3724965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 5, 7].length) (baseStart_3724965 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3724965 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3724965 prefixEnd_3724965 := by exact prefixLift 3724965
  have htrace : WordTrace (prefixWord ++ tailWord_3724965) baseStart_3724965 baseEnd_3724965 := by
    simpa [prefixWord, tailWord_3724965, baseEnd_3724965] using wordTrace_append hprefix tailTrace_3724965
  have hstable : (prefixWord ++ tailWord_3724965).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3724965).length < 2 ^ (prefixWord ++ tailWord_3724965).sum := by decide
  have hdescent : baseEnd_3724965 < baseStart_3724965 := by decide
  rcases family_descends (prefixWord ++ tailWord_3724965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3725055 : List Nat := [1, 1, 2, 2, 1, 3, 2, 2, 8]
def baseStart_3725055 : Nat := 118140960795 + 3725055 * 2 ^ 59
def prefixEnd_3725055 : Nat := 4983230072969 + 3 ^ 40 * 3725055 * 2
def baseEnd_3725055 : Nat := 425054150985339653084731

theorem tailTrace_3725055 : CollatzResearch.WordTrace tailWord_3725055 prefixEnd_3725055 425054150985339653084731 := by
  unfold tailWord_3725055
  simp only [CollatzResearch.WordTrace]
  refine ⟨135863917519769398589536619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90575945013179599059691079 135863917519769398589536619)
  ·
    refine ⟨203795876279654097884304929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135863917519769398589536619 203795876279654097884304929)
    ·
      refine ⟨152846907209740573413228697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 203795876279654097884304929 152846907209740573413228697)
      ·
        refine ⟨114635180407305430059921523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152846907209740573413228697 114635180407305430059921523)
        ·
          refine ⟨171952770610958145089882285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114635180407305430059921523 171952770610958145089882285)
          ·
            refine ⟨64482288979109304408705857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 171952770610958145089882285 64482288979109304408705857)
            ·
              refine ⟨48361716734331978306529393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64482288979109304408705857 48361716734331978306529393)
              ·
                refine ⟨36271287550748983729897045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48361716734331978306529393 36271287550748983729897045)
                ·
                  refine ⟨425054150985339653084731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 36271287550748983729897045 425054150985339653084731)
                  ·
                    rfl

theorem cell22_3725055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 2, 8].length) (baseStart_3725055 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3725055 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3725055 prefixEnd_3725055 := by exact prefixLift 3725055
  have htrace : WordTrace (prefixWord ++ tailWord_3725055) baseStart_3725055 baseEnd_3725055 := by
    simpa [prefixWord, tailWord_3725055, baseEnd_3725055] using wordTrace_append hprefix tailTrace_3725055
  have hstable : (prefixWord ++ tailWord_3725055).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3725055).length < 2 ^ (prefixWord ++ tailWord_3725055).sum := by decide
  have hdescent : baseEnd_3725055 < baseStart_3725055 := by decide
  rcases family_descends (prefixWord ++ tailWord_3725055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3725087 : List Nat := [1, 1, 2, 4, 2, 1, 2, 3, 1, 5]
def baseStart_3725087 : Nat := 118140960795 + 3725087 * 2 ^ 59
def prefixEnd_3725087 : Nat := 4983230072969 + 3 ^ 40 * 3725087 * 2
def baseEnd_3725087 : Nat := 1275173407209981542454095

theorem tailTrace_3725087 : CollatzResearch.WordTrace tailWord_3725087 prefixEnd_3725087 1275173407209981542454095 := by
  unfold tailWord_3725087
  simp only [CollatzResearch.WordTrace]
  refine ⟨135865084655653468054701515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90576723103768978703134343 135865084655653468054701515)
  ·
    refine ⟨203797626983480202082052273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135865084655653468054701515 203797626983480202082052273)
    ·
      refine ⟨152848220237610151561539205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 203797626983480202082052273 152848220237610151561539205)
      ·
        refine ⟨28659041294551903417788601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 152848220237610151561539205 28659041294551903417788601)
        ·
          refine ⟨21494280970913927563341451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28659041294551903417788601 21494280970913927563341451)
          ·
            refine ⟨32241421456370891345012177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21494280970913927563341451 32241421456370891345012177)
            ·
              refine ⟨24181066092278168508759133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32241421456370891345012177 24181066092278168508759133)
              ·
                refine ⟨9067899784604313190784675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24181066092278168508759133 9067899784604313190784675)
                ·
                  refine ⟨13601849676906469786177013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9067899784604313190784675 13601849676906469786177013)
                  ·
                    refine ⟨1275173407209981542454095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13601849676906469786177013 1275173407209981542454095)
                    ·
                      rfl

theorem cell22_3725087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 2, 3, 1, 5].length) (baseStart_3725087 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3725087 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3725087 prefixEnd_3725087 := by exact prefixLift 3725087
  have htrace : WordTrace (prefixWord ++ tailWord_3725087) baseStart_3725087 baseEnd_3725087 := by
    simpa [prefixWord, tailWord_3725087, baseEnd_3725087] using wordTrace_append hprefix tailTrace_3725087
  have hstable : (prefixWord ++ tailWord_3725087).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3725087).length < 2 ^ (prefixWord ++ tailWord_3725087).sum := by decide
  have hdescent : baseEnd_3725087 < baseStart_3725087 := by decide
  rcases family_descends (prefixWord ++ tailWord_3725087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3725108 : List Nat := [2, 5, 1, 1, 2, 2, 3, 1, 1, 4]
def baseStart_3725108 : Nat := 118140960795 + 3725108 * 2 ^ 59
def prefixEnd_3725108 : Nat := 4983230072969 + 3 ^ 40 * 3725108 * 2
def baseEnd_3725108 : Nat := 1275180595939144487679031

theorem tailTrace_3725108 : CollatzResearch.WordTrace tailWord_3725108 prefixEnd_3725108 1275180595939144487679031 := by
  unfold tailWord_3725108
  simp only [CollatzResearch.WordTrace]
  refine ⟨67932925294288694320607989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90577233725718259094143985 67932925294288694320607989)
  ·
    refine ⟨6368711746339565092556999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 67932925294288694320607989 6368711746339565092556999)
    ·
      refine ⟨9553067619509347638835499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6368711746339565092556999 9553067619509347638835499)
      ·
        refine ⟨14329601429264021458253249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9553067619509347638835499 14329601429264021458253249)
        ·
          refine ⟨10747201071948016093689937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14329601429264021458253249 10747201071948016093689937)
          ·
            refine ⟨8060400803961012070267453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10747201071948016093689937 8060400803961012070267453)
            ·
              refine ⟨3022650301485379526350295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8060400803961012070267453 3022650301485379526350295)
              ·
                refine ⟨4533975452228069289525443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3022650301485379526350295 4533975452228069289525443)
                ·
                  refine ⟨6800963178342103934288165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4533975452228069289525443 6800963178342103934288165)
                  ·
                    refine ⟨1275180595939144487679031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6800963178342103934288165 1275180595939144487679031)
                    ·
                      rfl

theorem cell22_3725108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 3, 1, 1, 4].length) (baseStart_3725108 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3725108 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3725108 prefixEnd_3725108 := by exact prefixLift 3725108
  have htrace : WordTrace (prefixWord ++ tailWord_3725108) baseStart_3725108 baseEnd_3725108 := by
    simpa [prefixWord, tailWord_3725108, baseEnd_3725108] using wordTrace_append hprefix tailTrace_3725108
  have hstable : (prefixWord ++ tailWord_3725108).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3725108).length < 2 ^ (prefixWord ++ tailWord_3725108).sum := by decide
  have hdescent : baseEnd_3725108 < baseStart_3725108 := by decide
  rcases family_descends (prefixWord ++ tailWord_3725108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3725117 : List Nat := [1, 4, 1, 4, 1, 11]
def baseStart_3725117 : Nat := 118140960795 + 3725117 * 2 ^ 59
def prefixEnd_3725117 : Nat := 4983230072969 + 3 ^ 40 * 3725117 * 2
def baseEnd_3725117 : Nat := 15743008355840388446963

theorem tailTrace_3725117 : CollatzResearch.WordTrace tailWord_3725117 prefixEnd_3725117 15743008355840388446963 := by
  unfold tailWord_3725117
  simp only [CollatzResearch.WordTrace]
  refine ⟨135866178845544783178293605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90577452563696522118862403 135866178845544783178293605)
  ·
    refine ⟨25474908533539646845930051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 135866178845544783178293605 25474908533539646845930051)
    ·
      refine ⟨38212362800309470268895077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25474908533539646845930051 38212362800309470268895077)
      ·
        refine ⟨7164818025058025675417827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38212362800309470268895077 7164818025058025675417827)
        ·
          refine ⟨10747227037587038513126741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7164818025058025675417827 10747227037587038513126741)
          ·
            refine ⟨15743008355840388446963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 10747227037587038513126741 15743008355840388446963)
            ·
              rfl

theorem cell22_3725117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 11].length) (baseStart_3725117 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3725117 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3725117 prefixEnd_3725117 := by exact prefixLift 3725117
  have htrace : WordTrace (prefixWord ++ tailWord_3725117) baseStart_3725117 baseEnd_3725117 := by
    simpa [prefixWord, tailWord_3725117, baseEnd_3725117] using wordTrace_append hprefix tailTrace_3725117
  have hstable : (prefixWord ++ tailWord_3725117).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3725117).length < 2 ^ (prefixWord ++ tailWord_3725117).sum := by decide
  have hdescent : baseEnd_3725117 < baseStart_3725117 := by decide
  rcases family_descends (prefixWord ++ tailWord_3725117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3725177 : List Nat := [1, 2, 1, 3, 2, 2, 1, 1, 4, 5]
def baseStart_3725177 : Nat := 118140960795 + 3725177 * 2 ^ 59
def prefixEnd_3725177 : Nat := 4983230072969 + 3 ^ 40 * 3725177 * 2
def baseEnd_3725177 : Nat := 1275204216049251307703819

theorem tailTrace_3725177 : CollatzResearch.WordTrace tailWord_3725177 prefixEnd_3725177 1275204216049251307703819 := by
  unfold tailWord_3725177
  simp only [CollatzResearch.WordTrace]
  refine ⟨135868367225327413425477785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90578911483551608950318523 135868367225327413425477785)
  ·
    refine ⟨101901275418995560069108339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135868367225327413425477785 101901275418995560069108339)
    ·
      refine ⟨152851913128493340103662509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101901275418995560069108339 152851913128493340103662509)
      ·
        refine ⟨57319467423185002538873441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 152851913128493340103662509 57319467423185002538873441)
        ·
          refine ⟨42989600567388751904155081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57319467423185002538873441 42989600567388751904155081)
          ·
            refine ⟨32242200425541563928116311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42989600567388751904155081 32242200425541563928116311)
            ·
              refine ⟨48363300638312345892174467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32242200425541563928116311 48363300638312345892174467)
              ·
                refine ⟨72544950957468518838261701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48363300638312345892174467 72544950957468518838261701)
                ·
                  refine ⟨13602178304525347282174069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 72544950957468518838261701 13602178304525347282174069)
                  ·
                    refine ⟨1275204216049251307703819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13602178304525347282174069 1275204216049251307703819)
                    ·
                      rfl

theorem cell22_3725177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 1, 4, 5].length) (baseStart_3725177 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3725177 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3725177 prefixEnd_3725177 := by exact prefixLift 3725177
  have htrace : WordTrace (prefixWord ++ tailWord_3725177) baseStart_3725177 baseEnd_3725177 := by
    simpa [prefixWord, tailWord_3725177, baseEnd_3725177] using wordTrace_append hprefix tailTrace_3725177
  have hstable : (prefixWord ++ tailWord_3725177).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3725177).length < 2 ^ (prefixWord ++ tailWord_3725177).sum := by decide
  have hdescent : baseEnd_3725177 < baseStart_3725177 := by decide
  rcases family_descends (prefixWord ++ tailWord_3725177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3725209 : List Nat := [1, 2, 1, 2, 1, 3, 3, 4, 1, 4]
def baseStart_3725209 : Nat := 118140960795 + 3725209 * 2 ^ 59
def prefixEnd_3725209 : Nat := 4983230072969 + 3 ^ 40 * 3725209 * 2
def baseEnd_3725209 : Nat := 1275215170303213890903721

theorem tailTrace_3725209 : CollatzResearch.WordTrace tailWord_3725209 prefixEnd_3725209 1275215170303213890903721 := by
  unfold tailWord_3725209
  simp only [CollatzResearch.WordTrace]
  refine ⟨135869534361211482890642681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90579689574140988593761787 135869534361211482890642681)
  ·
    refine ⟨101902150770908612167982011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135869534361211482890642681 101902150770908612167982011)
    ·
      refine ⟨152853226156362918251973017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101902150770908612167982011 152853226156362918251973017)
      ·
        refine ⟨114639919617272188688979763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152853226156362918251973017 114639919617272188688979763)
        ·
          refine ⟨171959879425908283033469645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114639919617272188688979763 171959879425908283033469645)
          ·
            refine ⟨64484954784715606137551117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 171959879425908283033469645 64484954784715606137551117)
            ·
              refine ⟨24181858044268352301581669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64484954784715606137551117 24181858044268352301581669)
              ·
                refine ⟨4534098383300316056546563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24181858044268352301581669 4534098383300316056546563)
                ·
                  refine ⟨6801147574950474084819845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4534098383300316056546563 6801147574950474084819845)
                  ·
                    refine ⟨1275215170303213890903721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6801147574950474084819845 1275215170303213890903721)
                    ·
                      rfl

theorem cell22_3725209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 3, 4, 1, 4].length) (baseStart_3725209 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3725209 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3725209 prefixEnd_3725209 := by exact prefixLift 3725209
  have htrace : WordTrace (prefixWord ++ tailWord_3725209) baseStart_3725209 baseEnd_3725209 := by
    simpa [prefixWord, tailWord_3725209, baseEnd_3725209] using wordTrace_append hprefix tailTrace_3725209
  have hstable : (prefixWord ++ tailWord_3725209).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3725209).length < 2 ^ (prefixWord ++ tailWord_3725209).sum := by decide
  have hdescent : baseEnd_3725209 < baseStart_3725209 := by decide
  rcases family_descends (prefixWord ++ tailWord_3725209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3725217 : List Nat := [1, 2, 3, 4, 3, 1, 1, 3, 1, 3]
def baseStart_3725217 : Nat := 118140960795 + 3725217 * 2 ^ 59
def prefixEnd_3725217 : Nat := 4983230072969 + 3 ^ 40 * 3725217 * 2
def baseEnd_3725217 : Nat := 1275217908866704536703697

theorem tailTrace_3725217 : CollatzResearch.WordTrace tailWord_3725217 prefixEnd_3725217 1275217908866704536703697 := by
  unfold tailWord_3725217
  simp only [CollatzResearch.WordTrace]
  refine ⟨135869826145182500256933905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90579884096788333504622603 135869826145182500256933905)
  ·
    refine ⟨101902369608886875192700429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135869826145182500256933905 101902369608886875192700429)
    ·
      refine ⟨38213388603332578197262661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101902369608886875192700429 38213388603332578197262661)
      ·
        refine ⟨7165010363124858411986749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38213388603332578197262661 7165010363124858411986749)
        ·
          refine ⟨2686878886171821904495031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7165010363124858411986749 2686878886171821904495031)
          ·
            refine ⟨4030318329257732856742547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2686878886171821904495031 4030318329257732856742547)
            ·
              refine ⟨6045477493886599285113821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4030318329257732856742547 6045477493886599285113821)
              ·
                refine ⟨2267054060207474731917683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6045477493886599285113821 2267054060207474731917683)
                ·
                  refine ⟨3400581090311212097876525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2267054060207474731917683 3400581090311212097876525)
                  ·
                    refine ⟨1275217908866704536703697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3400581090311212097876525 1275217908866704536703697)
                    ·
                      rfl

theorem cell22_3725217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 3, 1, 1, 3, 1, 3].length) (baseStart_3725217 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3725217 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3725217 prefixEnd_3725217 := by exact prefixLift 3725217
  have htrace : WordTrace (prefixWord ++ tailWord_3725217) baseStart_3725217 baseEnd_3725217 := by
    simpa [prefixWord, tailWord_3725217, baseEnd_3725217] using wordTrace_append hprefix tailTrace_3725217
  have hstable : (prefixWord ++ tailWord_3725217).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3725217).length < 2 ^ (prefixWord ++ tailWord_3725217).sum := by decide
  have hdescent : baseEnd_3725217 < baseStart_3725217 := by decide
  rcases family_descends (prefixWord ++ tailWord_3725217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3725269 : List Nat := [1, 3, 2, 3, 2, 1, 2, 8]
def baseStart_3725269 : Nat := 118140960795 + 3725269 * 2 ^ 59
def prefixEnd_3725269 : Nat := 4983230072969 + 3 ^ 40 * 3725269 * 2
def baseEnd_3725269 : Nat := 141692856614377081600393

theorem tailTrace_3725269 : CollatzResearch.WordTrace tailWord_3725269 prefixEnd_3725269 141692856614377081600393 := by
  unfold tailWord_3725269
  simp only [CollatzResearch.WordTrace]
  refine ⟨135871722740994113137826861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90581148493996075425217907 135871722740994113137826861)
  ·
    refine ⟨50951896027872792426685073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135871722740994113137826861 50951896027872792426685073)
    ·
      refine ⟨38213922020904594320013805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50951896027872792426685073 38213922020904594320013805)
      ·
        refine ⟨14330220757839222870005177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38213922020904594320013805 14330220757839222870005177)
        ·
          refine ⟨10747665568379417152503883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14330220757839222870005177 10747665568379417152503883)
          ·
            refine ⟨16121498352569125728755825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10747665568379417152503883 16121498352569125728755825)
            ·
              refine ⟨12091123764426844296566869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16121498352569125728755825 12091123764426844296566869)
              ·
                refine ⟨141692856614377081600393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12091123764426844296566869 141692856614377081600393)
                ·
                  rfl

theorem cell22_3725269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 2, 8].length) (baseStart_3725269 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3725269 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3725269 prefixEnd_3725269 := by exact prefixLift 3725269
  have htrace : WordTrace (prefixWord ++ tailWord_3725269) baseStart_3725269 baseEnd_3725269 := by
    simpa [prefixWord, tailWord_3725269, baseEnd_3725269] using wordTrace_append hprefix tailTrace_3725269
  have hstable : (prefixWord ++ tailWord_3725269).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3725269).length < 2 ^ (prefixWord ++ tailWord_3725269).sum := by decide
  have hdescent : baseEnd_3725269 < baseStart_3725269 := by decide
  rcases family_descends (prefixWord ++ tailWord_3725269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3725410 : List Nat := [3, 3, 2, 2, 2, 2, 1, 1, 6]
def baseStart_3725410 : Nat := 118140960795 + 3725410 * 2 ^ 59
def prefixEnd_3725410 : Nat := 4983230072969 + 3 ^ 40 * 3725410 * 2
def baseEnd_3725410 : Nat := 425094658903638788876035

theorem tailTrace_3725410 : CollatzResearch.WordTrace tailWord_3725410 prefixEnd_3725410 425094658903638788876035 := by
  unfold tailWord_3725410
  simp only [CollatzResearch.WordTrace]
  refine ⟨33969216358370823554677421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90584576955655529479139789 33969216358370823554677421)
  ·
    refine ⟨12738456134389058833004033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33969216358370823554677421 12738456134389058833004033)
    ·
      refine ⟨9553842100791794124753025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12738456134389058833004033 9553842100791794124753025)
      ·
        refine ⟨7165381575593845593564769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9553842100791794124753025 7165381575593845593564769)
        ·
          refine ⟨5374036181695384195173577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7165381575593845593564769 5374036181695384195173577)
          ·
            refine ⟨4030527136271538146380183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5374036181695384195173577 4030527136271538146380183)
            ·
              refine ⟨6045790704407307219570275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4030527136271538146380183 6045790704407307219570275)
              ·
                refine ⟨9068686056610960829355413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6045790704407307219570275 9068686056610960829355413)
                ·
                  refine ⟨425094658903638788876035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9068686056610960829355413 425094658903638788876035)
                  ·
                    rfl

theorem cell22_3725410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 2, 1, 1, 6].length) (baseStart_3725410 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3725410 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3725410 prefixEnd_3725410 := by exact prefixLift 3725410
  have htrace : WordTrace (prefixWord ++ tailWord_3725410) baseStart_3725410 baseEnd_3725410 := by
    simpa [prefixWord, tailWord_3725410, baseEnd_3725410] using wordTrace_append hprefix tailTrace_3725410
  have hstable : (prefixWord ++ tailWord_3725410).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3725410).length < 2 ^ (prefixWord ++ tailWord_3725410).sum := by decide
  have hdescent : baseEnd_3725410 < baseStart_3725410 := by decide
  rcases family_descends (prefixWord ++ tailWord_3725410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3725421 : List Nat := [1, 5, 1, 1, 2, 1, 4, 7]
def baseStart_3725421 : Nat := 118140960795 + 3725421 * 2 ^ 59
def prefixEnd_3725421 : Nat := 4983230072969 + 3 ^ 40 * 3725421 * 2
def baseEnd_3725421 : Nat := 141698638026190667178119

theorem tailTrace_3725421 : CollatzResearch.WordTrace tailWord_3725421 prefixEnd_3725421 141698638026190667178119 := by
  unfold tailWord_3725421
  simp only [CollatzResearch.WordTrace]
  refine ⟨135877266636443443097360117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90584844424295628731573411 135877266636443443097360117)
  ·
    refine ⟨12738493747166572790377511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 135877266636443443097360117 12738493747166572790377511)
    ·
      refine ⟨19107740620749859185566267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12738493747166572790377511 19107740620749859185566267)
      ·
        refine ⟨28661610931124788778349401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19107740620749859185566267 28661610931124788778349401)
        ·
          refine ⟨21496208198343591583762051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28661610931124788778349401 21496208198343591583762051)
          ·
            refine ⟨32244312297515387375643077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21496208198343591583762051 32244312297515387375643077)
            ·
              refine ⟨6045808555784135132933077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32244312297515387375643077 6045808555784135132933077)
              ·
                refine ⟨141698638026190667178119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6045808555784135132933077 141698638026190667178119)
                ·
                  rfl

theorem cell22_3725421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 4, 7].length) (baseStart_3725421 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3725421 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3725421 prefixEnd_3725421 := by exact prefixLift 3725421
  have htrace : WordTrace (prefixWord ++ tailWord_3725421) baseStart_3725421 baseEnd_3725421 := by
    simpa [prefixWord, tailWord_3725421, baseEnd_3725421] using wordTrace_append hprefix tailTrace_3725421
  have hstable : (prefixWord ++ tailWord_3725421).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3725421).length < 2 ^ (prefixWord ++ tailWord_3725421).sum := by decide
  have hdescent : baseEnd_3725421 < baseStart_3725421 := by decide
  rcases family_descends (prefixWord ++ tailWord_3725421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3725496 : List Nat := [2, 1, 2, 1, 2, 1, 3, 3, 3, 4]
def baseStart_3725496 : Nat := 118140960795 + 3725496 * 2 ^ 59
def prefixEnd_3725496 : Nat := 4983230072969 + 3 ^ 40 * 3725496 * 2
def baseEnd_3725496 : Nat := 1275313416268440808977841

theorem tailTrace_3725496 : CollatzResearch.WordTrace tailWord_3725496 prefixEnd_3725496 1275313416268440808977841 := by
  unfold tailWord_3725496
  simp only [CollatzResearch.WordTrace]
  refine ⟨67940001055585865453170171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90586668074114487270893561 67940001055585865453170171)
  ·
    refine ⟨101910001583378798179755257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67940001055585865453170171 101910001583378798179755257)
    ·
      refine ⟨76432501187534098634816443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101910001583378798179755257 76432501187534098634816443)
      ·
        refine ⟨114648751781301147952224665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76432501187534098634816443 114648751781301147952224665)
        ·
          refine ⟨85986563835975860964168499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114648751781301147952224665 85986563835975860964168499)
          ·
            refine ⟨128979845753963791446252749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85986563835975860964168499 128979845753963791446252749)
            ·
              refine ⟨48367442157736421792344781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 128979845753963791446252749 48367442157736421792344781)
              ·
                refine ⟨18137790809151158172129293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48367442157736421792344781 18137790809151158172129293)
                ·
                  refine ⟨6801671553431684314548485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18137790809151158172129293 6801671553431684314548485)
                  ·
                    refine ⟨1275313416268440808977841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6801671553431684314548485 1275313416268440808977841)
                    ·
                      rfl

theorem cell22_3725496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 3, 3, 4].length) (baseStart_3725496 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3725496 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3725496 prefixEnd_3725496 := by exact prefixLift 3725496
  have htrace : WordTrace (prefixWord ++ tailWord_3725496) baseStart_3725496 baseEnd_3725496 := by
    simpa [prefixWord, tailWord_3725496, baseEnd_3725496] using wordTrace_append hprefix tailTrace_3725496
  have hstable : (prefixWord ++ tailWord_3725496).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3725496).length < 2 ^ (prefixWord ++ tailWord_3725496).sum := by decide
  have hdescent : baseEnd_3725496 < baseStart_3725496 := by decide
  rcases family_descends (prefixWord ++ tailWord_3725496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3725528 : List Nat := [2, 1, 2, 2, 4, 2, 2, 1, 6]
def baseStart_3725528 : Nat := 118140960795 + 3725528 * 2 ^ 59
def prefixEnd_3725528 : Nat := 4983230072969 + 3 ^ 40 * 3725528 * 2
def baseEnd_3725528 : Nat := 425108123507467797392581

theorem tailTrace_3725528 : CollatzResearch.WordTrace tailWord_3725528 prefixEnd_3725528 425108123507467797392581 := by
  unfold tailWord_3725528
  simp only [CollatzResearch.WordTrace]
  refine ⟨67940584623527900185752619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90587446164703866914336825 67940584623527900185752619)
  ·
    refine ⟨101910876935291850278628929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67940584623527900185752619 101910876935291850278628929)
    ·
      refine ⟨76433157701468887708971697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101910876935291850278628929 76433157701468887708971697)
      ·
        refine ⟨57324868276101665781728773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76433157701468887708971697 57324868276101665781728773)
        ·
          refine ⟨10748412801769062334074145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 57324868276101665781728773 10748412801769062334074145)
          ·
            refine ⟨8061309601326796750555609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10748412801769062334074145 8061309601326796750555609)
            ·
              refine ⟨6045982200995097562916707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8061309601326796750555609 6045982200995097562916707)
              ·
                refine ⟨9068973301492646344375061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6045982200995097562916707 9068973301492646344375061)
                ·
                  refine ⟨425108123507467797392581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9068973301492646344375061 425108123507467797392581)
                  ·
                    rfl

theorem cell22_3725528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 2, 1, 6].length) (baseStart_3725528 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3725528 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3725528 prefixEnd_3725528 := by exact prefixLift 3725528
  have htrace : WordTrace (prefixWord ++ tailWord_3725528) baseStart_3725528 baseEnd_3725528 := by
    simpa [prefixWord, tailWord_3725528, baseEnd_3725528] using wordTrace_append hprefix tailTrace_3725528
  have hstable : (prefixWord ++ tailWord_3725528).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3725528).length < 2 ^ (prefixWord ++ tailWord_3725528).sum := by decide
  have hdescent : baseEnd_3725528 < baseStart_3725528 := by decide
  rcases family_descends (prefixWord ++ tailWord_3725528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3725558 : List Nat := [5, 1, 1, 1, 1, 1, 4, 1, 1, 6]
def baseStart_3725558 : Nat := 118140960795 + 3725558 * 2 ^ 59
def prefixEnd_3725558 : Nat := 4983230072969 + 3 ^ 40 * 3725558 * 2
def baseEnd_3725558 : Nat := 1275334640135493313927651

theorem tailTrace_3725558 : CollatzResearch.WordTrace tailWord_3725558 prefixEnd_3725558 1275334640135493313927651 := by
  unfold tailWord_3725558
  simp only [CollatzResearch.WordTrace]
  refine ⟨8492641464809194718443583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 90588175624631410330064885 8492641464809194718443583)
  ·
    refine ⟨12738962197213792077665375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8492641464809194718443583 12738962197213792077665375)
    ·
      refine ⟨19108443295820688116498063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12738962197213792077665375 19108443295820688116498063)
      ·
        refine ⟨28662664943731032174747095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19108443295820688116498063 28662664943731032174747095)
        ·
          refine ⟨42993997415596548262120643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28662664943731032174747095 42993997415596548262120643)
          ·
            refine ⟨64490996123394822393180965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42993997415596548262120643 64490996123394822393180965)
            ·
              refine ⟨12092061773136529198721431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 64490996123394822393180965 12092061773136529198721431)
              ·
                refine ⟨18138092659704793798082147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12092061773136529198721431 18138092659704793798082147)
                ·
                  refine ⟨27207138989557190697123221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18138092659704793798082147 27207138989557190697123221)
                  ·
                    refine ⟨1275334640135493313927651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27207138989557190697123221 1275334640135493313927651)
                    ·
                      rfl

theorem cell22_3725558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 4, 1, 1, 6].length) (baseStart_3725558 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3725558 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3725558 prefixEnd_3725558 := by exact prefixLift 3725558
  have htrace : WordTrace (prefixWord ++ tailWord_3725558) baseStart_3725558 baseEnd_3725558 := by
    simpa [prefixWord, tailWord_3725558, baseEnd_3725558] using wordTrace_append hprefix tailTrace_3725558
  have hstable : (prefixWord ++ tailWord_3725558).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3725558).length < 2 ^ (prefixWord ++ tailWord_3725558).sum := by decide
  have hdescent : baseEnd_3725558 < baseStart_3725558 := by decide
  rcases family_descends (prefixWord ++ tailWord_3725558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3725594 : List Nat := [3, 1, 1, 3, 4, 2, 2, 1, 2, 3]
def baseStart_3725594 : Nat := 118140960795 + 3725594 * 2 ^ 59
def prefixEnd_3725594 : Nat := 4983230072969 + 3 ^ 40 * 3725594 * 2
def baseEnd_3725594 : Nat := 1275346963671201220027541

theorem tailTrace_3725594 : CollatzResearch.WordTrace tailWord_3725594 prefixEnd_3725594 1275346963671201220027541 := by
  unfold tailWord_3725594
  simp only [CollatzResearch.WordTrace]
  refine ⟨33970894116204173410851959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90589050976544462428938557 33970894116204173410851959)
  ·
    refine ⟨50956341174306260116277939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33970894116204173410851959 50956341174306260116277939)
    ·
      refine ⟨76434511761459390174416909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50956341174306260116277939 76434511761459390174416909)
      ·
        refine ⟨28662941910547271315406341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76434511761459390174416909 28662941910547271315406341)
        ·
          refine ⟨5374301608227613371638689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28662941910547271315406341 5374301608227613371638689)
          ·
            refine ⟨4030726206170710028729017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5374301608227613371638689 4030726206170710028729017)
            ·
              refine ⟨3023044654628032521546763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4030726206170710028729017 3023044654628032521546763)
              ·
                refine ⟨4534566981942048782320145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3023044654628032521546763 4534566981942048782320145)
                ·
                  refine ⟨3400925236456536586740109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4534566981942048782320145 3400925236456536586740109)
                  ·
                    refine ⟨1275346963671201220027541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3400925236456536586740109 1275346963671201220027541)
                    ·
                      rfl

theorem cell22_3725594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 2, 2, 1, 2, 3].length) (baseStart_3725594 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3725594 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3725594 prefixEnd_3725594 := by exact prefixLift 3725594
  have htrace : WordTrace (prefixWord ++ tailWord_3725594) baseStart_3725594 baseEnd_3725594 := by
    simpa [prefixWord, tailWord_3725594, baseEnd_3725594] using wordTrace_append hprefix tailTrace_3725594
  have hstable : (prefixWord ++ tailWord_3725594).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3725594).length < 2 ^ (prefixWord ++ tailWord_3725594).sum := by decide
  have hdescent : baseEnd_3725594 < baseStart_3725594 := by decide
  rcases family_descends (prefixWord ++ tailWord_3725594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3725616 : List Nat := [2, 1, 1, 1, 2, 2, 2, 1, 3, 7]
def baseStart_3725616 : Nat := 118140960795 + 3725616 * 2 ^ 59
def prefixEnd_3725616 : Nat := 4983230072969 + 3 ^ 40 * 3725616 * 2
def baseEnd_3725616 : Nat := 1275354494720800495977473

theorem tailTrace_3725616 : CollatzResearch.WordTrace tailWord_3725616 prefixEnd_3725616 1275354494720800495977473 := by
  unfold tailWord_3725616
  simp only [CollatzResearch.WordTrace]
  refine ⟨67942189435368495700354351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90589585913824660933805801 67942189435368495700354351)
  ·
    refine ⟨101913284153052743550531527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67942189435368495700354351 101913284153052743550531527)
    ·
      refine ⟨152869926229579115325797291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101913284153052743550531527 152869926229579115325797291)
      ·
        refine ⟨229304889344368672988695937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152869926229579115325797291 229304889344368672988695937)
        ·
          refine ⟨171978667008276504741521953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 229304889344368672988695937 171978667008276504741521953)
          ·
            refine ⟨128984000256207378556141465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 171978667008276504741521953 128984000256207378556141465)
            ·
              refine ⟨96738000192155533917106099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 128984000256207378556141465 96738000192155533917106099)
              ·
                refine ⟨145107000288233300875659149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96738000192155533917106099 145107000288233300875659149)
                ·
                  refine ⟨54415125108087487828372181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 145107000288233300875659149 54415125108087487828372181)
                  ·
                    refine ⟨1275354494720800495977473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 54415125108087487828372181 1275354494720800495977473)
                    ·
                      rfl

theorem cell22_3725616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 1, 3, 7].length) (baseStart_3725616 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3725616 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3725616 prefixEnd_3725616 := by exact prefixLift 3725616
  have htrace : WordTrace (prefixWord ++ tailWord_3725616) baseStart_3725616 baseEnd_3725616 := by
    simpa [prefixWord, tailWord_3725616, baseEnd_3725616] using wordTrace_append hprefix tailTrace_3725616
  have hstable : (prefixWord ++ tailWord_3725616).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3725616).length < 2 ^ (prefixWord ++ tailWord_3725616).sum := by decide
  have hdescent : baseEnd_3725616 < baseStart_3725616 := by decide
  rcases family_descends (prefixWord ++ tailWord_3725616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3725648 : List Nat := [2, 1, 1, 1, 1, 6, 1, 2, 3, 4]
def baseStart_3725648 : Nat := 118140960795 + 3725648 * 2 ^ 59
def prefixEnd_3725648 : Nat := 4983230072969 + 3 ^ 40 * 3725648 * 2
def baseEnd_3725648 : Nat := 1275365448974763079177375

theorem tailTrace_3725648 : CollatzResearch.WordTrace tailWord_3725648 prefixEnd_3725648 1275365448974763079177375 := by
  unfold tailWord_3725648
  simp only [CollatzResearch.WordTrace]
  refine ⟨67942773003310530432936799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90590364004414040577249065 67942773003310530432936799)
  ·
    refine ⟨101914159504965795649405199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67942773003310530432936799 101914159504965795649405199)
    ·
      refine ⟨152871239257448693474107799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101914159504965795649405199 152871239257448693474107799)
      ·
        refine ⟨229306858886173040211161699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152871239257448693474107799 229306858886173040211161699)
        ·
          refine ⟨343960288329259560316742549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 229306858886173040211161699 343960288329259560316742549)
          ·
            refine ⟨16123138515434041889847307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 343960288329259560316742549 16123138515434041889847307)
            ·
              refine ⟨24184707773151062834770961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16123138515434041889847307 24184707773151062834770961)
              ·
                refine ⟨18138530829863297126078221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24184707773151062834770961 18138530829863297126078221)
                ·
                  refine ⟨6801949061198736422279333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18138530829863297126078221 6801949061198736422279333)
                  ·
                    refine ⟨1275365448974763079177375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6801949061198736422279333 1275365448974763079177375)
                    ·
                      rfl

theorem cell22_3725648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 1, 2, 3, 4].length) (baseStart_3725648 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3725648 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3725648 prefixEnd_3725648 := by exact prefixLift 3725648
  have htrace : WordTrace (prefixWord ++ tailWord_3725648) baseStart_3725648 baseEnd_3725648 := by
    simpa [prefixWord, tailWord_3725648, baseEnd_3725648] using wordTrace_append hprefix tailTrace_3725648
  have hstable : (prefixWord ++ tailWord_3725648).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3725648).length < 2 ^ (prefixWord ++ tailWord_3725648).sum := by decide
  have hdescent : baseEnd_3725648 < baseStart_3725648 := by decide
  rcases family_descends (prefixWord ++ tailWord_3725648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3725680 : List Nat := [2, 1, 1, 1, 4, 3, 1, 5, 4]
def baseStart_3725680 : Nat := 118140960795 + 3725680 * 2 ^ 59
def prefixEnd_3725680 : Nat := 4983230072969 + 3 ^ 40 * 3725680 * 2
def baseEnd_3725680 : Nat := 425125467742908554125759

theorem tailTrace_3725680 : CollatzResearch.WordTrace tailWord_3725680 prefixEnd_3725680 425125467742908554125759 := by
  unfold tailWord_3725680
  simp only [CollatzResearch.WordTrace]
  refine ⟨67943356571252565165519247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90591142095003420220692329 67943356571252565165519247)
  ·
    refine ⟨101915034856878847748278871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67943356571252565165519247 101915034856878847748278871)
    ·
      refine ⟨152872552285318271622418307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101915034856878847748278871 152872552285318271622418307)
      ·
        refine ⟨229308828427977407433627461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152872552285318271622418307 229308828427977407433627461)
        ·
          refine ⟨42995405330245763893805149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 229308828427977407433627461 42995405330245763893805149)
          ·
            refine ⟨16123276998842161460176931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42995405330245763893805149 16123276998842161460176931)
            ·
              refine ⟨24184915498263242190265397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16123276998842161460176931 24184915498263242190265397)
              ·
                refine ⟨2267335827962178955337381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24184915498263242190265397 2267335827962178955337381)
                ·
                  refine ⟨425125467742908554125759, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2267335827962178955337381 425125467742908554125759)
                  ·
                    rfl

theorem cell22_3725680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 1, 5, 4].length) (baseStart_3725680 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3725680 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3725680 prefixEnd_3725680 := by exact prefixLift 3725680
  have htrace : WordTrace (prefixWord ++ tailWord_3725680) baseStart_3725680 baseEnd_3725680 := by
    simpa [prefixWord, tailWord_3725680, baseEnd_3725680] using wordTrace_append hprefix tailTrace_3725680
  have hstable : (prefixWord ++ tailWord_3725680).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3725680).length < 2 ^ (prefixWord ++ tailWord_3725680).sum := by decide
  have hdescent : baseEnd_3725680 < baseStart_3725680 := by decide
  rcases family_descends (prefixWord ++ tailWord_3725680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3725682 : List Nat := [3, 2, 1, 2, 1, 3, 4, 1, 1, 4]
def baseStart_3725682 : Nat := 118140960795 + 3725682 * 2 ^ 59
def prefixEnd_3725682 : Nat := 4983230072969 + 3 ^ 40 * 3725682 * 2
def baseEnd_3725682 : Nat := 1275377087869598323827271

theorem tailTrace_3725682 : CollatzResearch.WordTrace tailWord_3725682 prefixEnd_3725682 1275377087869598323827271 := by
  unfold tailWord_3725682
  simp only [CollatzResearch.WordTrace]
  refine ⟨33971696522124471168152825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90591190725665256448407533 33971696522124471168152825)
  ·
    refine ⟨25478772391593353376114619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33971696522124471168152825 25478772391593353376114619)
    ·
      refine ⟨38218158587390030064171929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25478772391593353376114619 38218158587390030064171929)
      ·
        refine ⟨28663618940542522548128947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38218158587390030064171929 28663618940542522548128947)
        ·
          refine ⟨42995428410813783822193421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28663618940542522548128947 42995428410813783822193421)
          ·
            refine ⟨16123285654055168933322533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42995428410813783822193421 16123285654055168933322533)
            ·
              refine ⟨3023116060135344174997975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16123285654055168933322533 3023116060135344174997975)
              ·
                refine ⟨4534674090203016262496963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3023116060135344174997975 4534674090203016262496963)
                ·
                  refine ⟨6802011135304524393745445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4534674090203016262496963 6802011135304524393745445)
                  ·
                    refine ⟨1275377087869598323827271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6802011135304524393745445 1275377087869598323827271)
                    ·
                      rfl

theorem cell22_3725682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 4, 1, 1, 4].length) (baseStart_3725682 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3725682 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3725682 prefixEnd_3725682 := by exact prefixLift 3725682
  have htrace : WordTrace (prefixWord ++ tailWord_3725682) baseStart_3725682 baseEnd_3725682 := by
    simpa [prefixWord, tailWord_3725682, baseEnd_3725682] using wordTrace_append hprefix tailTrace_3725682
  have hstable : (prefixWord ++ tailWord_3725682).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3725682).length < 2 ^ (prefixWord ++ tailWord_3725682).sum := by decide
  have hdescent : baseEnd_3725682 < baseStart_3725682 := by decide
  rcases family_descends (prefixWord ++ tailWord_3725682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3725686 : List Nat := [5, 1, 1, 4, 2, 1, 1, 2, 5]
def baseStart_3725686 : Nat := 118140960795 + 3725686 * 2 ^ 59
def prefixEnd_3725686 : Nat := 4983230072969 + 3 ^ 40 * 3725686 * 2
def baseEnd_3725686 : Nat := 425126152383781215575753

theorem tailTrace_3725686 : CollatzResearch.WordTrace tailWord_3725686 prefixEnd_3725686 425126152383781215575753 := by
  unfold tailWord_3725686
  simp only [CollatzResearch.WordTrace]
  refine ⟨8492933248780212084734807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 90591287986988928903837941 8492933248780212084734807)
  ·
    refine ⟨12739399873170318127102211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8492933248780212084734807 12739399873170318127102211)
    ·
      refine ⟨19109099809755477190653317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12739399873170318127102211 19109099809755477190653317)
      ·
        refine ⟨3582956214329151973247497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19109099809755477190653317 3582956214329151973247497)
        ·
          refine ⟨2687217160746863979935623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3582956214329151973247497 2687217160746863979935623)
          ·
            refine ⟨4030825741120295969903435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2687217160746863979935623 4030825741120295969903435)
            ·
              refine ⟨6046238611680443954855153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4030825741120295969903435 6046238611680443954855153)
              ·
                refine ⟨4534678958760332966141365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6046238611680443954855153 4534678958760332966141365)
                ·
                  refine ⟨425126152383781215575753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4534678958760332966141365 425126152383781215575753)
                  ·
                    rfl

theorem cell22_3725686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 2, 1, 1, 2, 5].length) (baseStart_3725686 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3725686 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3725686 prefixEnd_3725686 := by exact prefixLift 3725686
  have htrace : WordTrace (prefixWord ++ tailWord_3725686) baseStart_3725686 baseEnd_3725686 := by
    simpa [prefixWord, tailWord_3725686, baseEnd_3725686] using wordTrace_append hprefix tailTrace_3725686
  have hstable : (prefixWord ++ tailWord_3725686).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3725686).length < 2 ^ (prefixWord ++ tailWord_3725686).sum := by decide
  have hdescent : baseEnd_3725686 < baseStart_3725686 := by decide
  rcases family_descends (prefixWord ++ tailWord_3725686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3725697 : List Nat := [1, 2, 4, 3, 1, 1, 2, 4, 4]
def baseStart_3725697 : Nat := 118140960795 + 3725697 * 2 ^ 59
def prefixEnd_3725697 : Nat := 4983230072969 + 3 ^ 40 * 3725697 * 2
def baseEnd_3725697 : Nat := 425127407558714428234075

theorem tailTrace_3725697 : CollatzResearch.WordTrace tailWord_3725697 prefixEnd_3725697 425127407558714428234075 := by
  unfold tailWord_3725697
  simp only [CollatzResearch.WordTrace]
  refine ⟨135887333183443542234407345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90591555455629028156271563 135887333183443542234407345)
  ·
    refine ⟨101915499887582656675805509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135887333183443542234407345 101915499887582656675805509)
    ·
      refine ⟨19109156228921748126713533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 101915499887582656675805509 19109156228921748126713533)
      ·
        refine ⟨7165933585845655547517575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19109156228921748126713533 7165933585845655547517575)
        ·
          refine ⟨10748900378768483321276363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7165933585845655547517575 10748900378768483321276363)
          ·
            refine ⟨16123350568152724981914545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10748900378768483321276363 16123350568152724981914545)
            ·
              refine ⟨12092512926114543736435909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16123350568152724981914545 12092512926114543736435909)
              ·
                refine ⟨2267346173646476950581733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12092512926114543736435909 2267346173646476950581733)
                ·
                  refine ⟨425127407558714428234075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2267346173646476950581733 425127407558714428234075)
                  ·
                    rfl

theorem cell22_3725697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 2, 4, 4].length) (baseStart_3725697 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3725697 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3725697 prefixEnd_3725697 := by exact prefixLift 3725697
  have htrace : WordTrace (prefixWord ++ tailWord_3725697) baseStart_3725697 baseEnd_3725697 := by
    simpa [prefixWord, tailWord_3725697, baseEnd_3725697] using wordTrace_append hprefix tailTrace_3725697
  have hstable : (prefixWord ++ tailWord_3725697).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3725697).length < 2 ^ (prefixWord ++ tailWord_3725697).sum := by decide
  have hdescent : baseEnd_3725697 < baseStart_3725697 := by decide
  rcases family_descends (prefixWord ++ tailWord_3725697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3725710 : List Nat := [4, 1, 1, 4, 1, 1, 1, 2, 1, 6]
def baseStart_3725710 : Nat := 118140960795 + 3725710 * 2 ^ 59
def prefixEnd_3725710 : Nat := 4983230072969 + 3 ^ 40 * 3725710 * 2
def baseEnd_3725710 : Nat := 1275386672841815584127185

theorem tailTrace_3725710 : CollatzResearch.WordTrace tailWord_3725710 prefixEnd_3725710 1275386672841815584127185 := by
  unfold tailWord_3725710
  simp only [CollatzResearch.WordTrace]
  refine ⟨16985975916549555681828823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 90591871554930963636420389 16985975916549555681828823)
  ·
    refine ⟨25478963874824333522743235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16985975916549555681828823 25478963874824333522743235)
    ·
      refine ⟨38218445812236500284114853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25478963874824333522743235 38218445812236500284114853)
      ·
        refine ⟨7165958589794343803271535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38218445812236500284114853 7165958589794343803271535)
        ·
          refine ⟨10748937884691515704907303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7165958589794343803271535 10748937884691515704907303)
          ·
            refine ⟨16123406827037273557360955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10748937884691515704907303 16123406827037273557360955)
            ·
              refine ⟨24185110240555910336041433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16123406827037273557360955 24185110240555910336041433)
              ·
                refine ⟨18138832680416932752031075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24185110240555910336041433 18138832680416932752031075)
                ·
                  refine ⟨27208249020625399128046613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18138832680416932752031075 27208249020625399128046613)
                  ·
                    refine ⟨1275386672841815584127185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27208249020625399128046613 1275386672841815584127185)
                    ·
                      rfl

theorem cell22_3725710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 1, 2, 1, 6].length) (baseStart_3725710 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3725710 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3725710 prefixEnd_3725710 := by exact prefixLift 3725710
  have htrace : WordTrace (prefixWord ++ tailWord_3725710) baseStart_3725710 baseEnd_3725710 := by
    simpa [prefixWord, tailWord_3725710, baseEnd_3725710] using wordTrace_append hprefix tailTrace_3725710
  have hstable : (prefixWord ++ tailWord_3725710).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3725710).length < 2 ^ (prefixWord ++ tailWord_3725710).sum := by decide
  have hdescent : baseEnd_3725710 < baseStart_3725710 := by decide
  rcases family_descends (prefixWord ++ tailWord_3725710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3725725 : List Nat := [1, 4, 2, 1, 4, 1, 1, 8]
def baseStart_3725725 : Nat := 118140960795 + 3725725 * 2 ^ 59
def prefixEnd_3725725 : Nat := 4983230072969 + 3 ^ 40 * 3725725 * 2
def baseEnd_3725725 : Nat := 141710200849817838333571

theorem tailTrace_3725725 : CollatzResearch.WordTrace tailWord_3725725 prefixEnd_3725725 141710200849817838333571 := by
  unfold tailWord_3725725
  simp only [CollatzResearch.WordTrace]
  refine ⟨135888354427342103016426629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90592236284894735344284419 135888354427342103016426629)
  ·
    refine ⟨25479066455126644315579993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 135888354427342103016426629 25479066455126644315579993)
    ·
      refine ⟨19109299841344983236684995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25479066455126644315579993 19109299841344983236684995)
      ·
        refine ⟨28663949762017474855027493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19109299841344983236684995 28663949762017474855027493)
        ·
          refine ⟨5374490580378276535317655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28663949762017474855027493 5374490580378276535317655)
          ·
            refine ⟨8061735870567414802976483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5374490580378276535317655 8061735870567414802976483)
            ·
              refine ⟨12092603805851122204464725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8061735870567414802976483 12092603805851122204464725)
              ·
                refine ⟨141710200849817838333571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12092603805851122204464725 141710200849817838333571)
                ·
                  rfl

theorem cell22_3725725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 1, 8].length) (baseStart_3725725 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3725725 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3725725 prefixEnd_3725725 := by exact prefixLift 3725725
  have htrace : WordTrace (prefixWord ++ tailWord_3725725) baseStart_3725725 baseEnd_3725725 := by
    simpa [prefixWord, tailWord_3725725, baseEnd_3725725] using wordTrace_append hprefix tailTrace_3725725
  have hstable : (prefixWord ++ tailWord_3725725).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3725725).length < 2 ^ (prefixWord ++ tailWord_3725725).sum := by decide
  have hdescent : baseEnd_3725725 < baseStart_3725725 := by decide
  rcases family_descends (prefixWord ++ tailWord_3725725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3725748 : List Nat := [2, 5, 2, 2, 1, 1, 3, 2, 4]
def baseStart_3725748 : Nat := 118140960795 + 3725748 * 2 ^ 59
def prefixEnd_3725748 : Nat := 4983230072969 + 3 ^ 40 * 3725748 * 2
def baseEnd_3725748 : Nat := 425133227006132050559023

theorem tailTrace_3725748 : CollatzResearch.WordTrace tailWord_3725748 prefixEnd_3725748 425133227006132050559023 := by
  unfold tailWord_3725748
  simp only [CollatzResearch.WordTrace]
  refine ⟨67944596653129388972256949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90592795537505851963009265 67944596653129388972256949)
  ·
    refine ⟨6369805936230880216149089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 67944596653129388972256949 6369805936230880216149089)
    ·
      refine ⟨4777354452173160162111817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6369805936230880216149089 4777354452173160162111817)
      ·
        refine ⟨3583015839129870121583863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4777354452173160162111817 3583015839129870121583863)
        ·
          refine ⟨5374523758694805182375795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3583015839129870121583863 5374523758694805182375795)
          ·
            refine ⟨8061785638042207773563693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5374523758694805182375795 8061785638042207773563693)
            ·
              refine ⟨3023169614265827915086385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8061785638042207773563693 3023169614265827915086385)
              ·
                refine ⟨2267377210699370936314789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3023169614265827915086385 2267377210699370936314789)
                ·
                  refine ⟨425133227006132050559023, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2267377210699370936314789 425133227006132050559023)
                  ·
                    rfl

theorem cell22_3725748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 3, 2, 4].length) (baseStart_3725748 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3725748 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3725748 prefixEnd_3725748 := by exact prefixLift 3725748
  have htrace : WordTrace (prefixWord ++ tailWord_3725748) baseStart_3725748 baseEnd_3725748 := by
    simpa [prefixWord, tailWord_3725748, baseEnd_3725748] using wordTrace_append hprefix tailTrace_3725748
  have hstable : (prefixWord ++ tailWord_3725748).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3725748).length < 2 ^ (prefixWord ++ tailWord_3725748).sum := by decide
  have hdescent : baseEnd_3725748 < baseStart_3725748 := by decide
  rcases family_descends (prefixWord ++ tailWord_3725748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3725757 : List Nat := [1, 4, 1, 2, 2, 2, 3, 1, 3, 3]
def baseStart_3725757 : Nat := 118140960795 + 3725757 * 2 ^ 59
def prefixEnd_3725757 : Nat := 4983230072969 + 3 ^ 40 * 3725757 * 2
def baseEnd_3725757 : Nat := 1275402761902323128202041

theorem tailTrace_3725757 : CollatzResearch.WordTrace tailWord_3725757 prefixEnd_3725757 1275402761902323128202041 := by
  unfold tailWord_3725757
  simp only [CollatzResearch.WordTrace]
  refine ⟨135889521563226172481591525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90593014375484114987727683 135889521563226172481591525)
  ·
    refine ⟨25479285293104907340298411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 135889521563226172481591525 25479285293104907340298411)
    ·
      refine ⟨38218927939657361010447617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25479285293104907340298411 38218927939657361010447617)
      ·
        refine ⟨28664195954743020757835713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38218927939657361010447617 28664195954743020757835713)
        ·
          refine ⟨21498146966057265568376785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28664195954743020757835713 21498146966057265568376785)
          ·
            refine ⟨16123610224542949176282589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21498146966057265568376785 16123610224542949176282589)
            ·
              refine ⟨6046353834203605941105971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16123610224542949176282589 6046353834203605941105971)
              ·
                refine ⟨9069530751305408911658957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6046353834203605941105971 9069530751305408911658957)
                ·
                  refine ⟨3401074031739528341872109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9069530751305408911658957 3401074031739528341872109)
                  ·
                    refine ⟨1275402761902323128202041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3401074031739528341872109 1275402761902323128202041)
                    ·
                      rfl

theorem cell22_3725757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 3, 1, 3, 3].length) (baseStart_3725757 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3725757 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3725757 prefixEnd_3725757 := by exact prefixLift 3725757
  have htrace : WordTrace (prefixWord ++ tailWord_3725757) baseStart_3725757 baseEnd_3725757 := by
    simpa [prefixWord, tailWord_3725757, baseEnd_3725757] using wordTrace_append hprefix tailTrace_3725757
  have hstable : (prefixWord ++ tailWord_3725757).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3725757).length < 2 ^ (prefixWord ++ tailWord_3725757).sum := by decide
  have hdescent : baseEnd_3725757 < baseStart_3725757 := by decide
  rcases family_descends (prefixWord ++ tailWord_3725757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3725770 : List Nat := [3, 1, 2, 1, 2, 2, 3, 3, 5]
def baseStart_3725770 : Nat := 118140960795 + 3725770 * 2 ^ 59
def prefixEnd_3725770 : Nat := 4983230072969 + 3 ^ 40 * 3725770 * 2
def baseEnd_3725770 : Nat := 425135737355998475875667

theorem tailTrace_3725770 : CollatzResearch.WordTrace tailWord_3725770 prefixEnd_3725770 425135737355998475875667 := by
  unfold tailWord_3725770
  simp only [CollatzResearch.WordTrace]
  refine ⟨33972498928044768925453691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90593330474786050467876509 33972498928044768925453691)
  ·
    refine ⟨50958748392067153388180537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33972498928044768925453691 50958748392067153388180537)
    ·
      refine ⟨38219061294050365041135403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50958748392067153388180537 38219061294050365041135403)
      ·
        refine ⟨57328591941075547561703105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38219061294050365041135403 57328591941075547561703105)
        ·
          refine ⟨42996443955806660671277329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57328591941075547561703105 42996443955806660671277329)
          ·
            refine ⟨32247332966854995503457997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42996443955806660671277329 32247332966854995503457997)
            ·
              refine ⟨12092749862570623313796749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32247332966854995503457997 12092749862570623313796749)
              ·
                refine ⟨4534781198463983742673781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12092749862570623313796749 4534781198463983742673781)
                ·
                  refine ⟨425135737355998475875667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4534781198463983742673781 425135737355998475875667)
                  ·
                    rfl

theorem cell22_3725770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 3, 3, 5].length) (baseStart_3725770 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3725770 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3725770 prefixEnd_3725770 := by exact prefixLift 3725770
  have htrace : WordTrace (prefixWord ++ tailWord_3725770) baseStart_3725770 baseEnd_3725770 := by
    simpa [prefixWord, tailWord_3725770, baseEnd_3725770] using wordTrace_append hprefix tailTrace_3725770
  have hstable : (prefixWord ++ tailWord_3725770).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3725770).length < 2 ^ (prefixWord ++ tailWord_3725770).sum := by decide
  have hdescent : baseEnd_3725770 < baseStart_3725770 := by decide
  rcases family_descends (prefixWord ++ tailWord_3725770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3725845 : List Nat := [1, 3, 2, 1, 3, 1, 3, 1, 1, 6]
def baseStart_3725845 : Nat := 118140960795 + 3725845 * 2 ^ 59
def prefixEnd_3725845 : Nat := 4983230072969 + 3 ^ 40 * 3725845 * 2
def baseEnd_3725845 : Nat := 1275432886100720232001771

theorem tailTrace_3725845 : CollatzResearch.WordTrace tailWord_3725845 prefixEnd_3725845 1275432886100720232001771 := by
  unfold tailWord_3725845
  simp only [CollatzResearch.WordTrace]
  refine ⟨135892731186907363510794989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90595154124604909007196659 135892731186907363510794989)
  ·
    refine ⟨50959774195090261316548121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135892731186907363510794989 50959774195090261316548121)
    ·
      refine ⟨38219830646317695987411091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50959774195090261316548121 38219830646317695987411091)
      ·
        refine ⟨57329745969476543981116637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38219830646317695987411091 57329745969476543981116637)
        ·
          refine ⟨21498654738553703992918739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57329745969476543981116637 21498654738553703992918739)
          ·
            refine ⟨32247982107830555989378109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21498654738553703992918739 32247982107830555989378109)
            ·
              refine ⟨12092993290436458496016791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32247982107830555989378109 12092993290436458496016791)
              ·
                refine ⟨18139489935654687744025187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12092993290436458496016791 18139489935654687744025187)
                ·
                  refine ⟨27209234903482031616037781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18139489935654687744025187 27209234903482031616037781)
                  ·
                    refine ⟨1275432886100720232001771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27209234903482031616037781 1275432886100720232001771)
                    ·
                      rfl

theorem cell22_3725845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 3, 1, 1, 6].length) (baseStart_3725845 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3725845 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3725845 prefixEnd_3725845 := by exact prefixLift 3725845
  have htrace : WordTrace (prefixWord ++ tailWord_3725845) baseStart_3725845 baseEnd_3725845 := by
    simpa [prefixWord, tailWord_3725845, baseEnd_3725845] using wordTrace_append hprefix tailTrace_3725845
  have hstable : (prefixWord ++ tailWord_3725845).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3725845).length < 2 ^ (prefixWord ++ tailWord_3725845).sum := by decide
  have hdescent : baseEnd_3725845 < baseStart_3725845 := by decide
  rcases family_descends (prefixWord ++ tailWord_3725845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3725864 : List Nat := [2, 1, 5, 2, 1, 2, 1, 1, 4, 3]
def baseStart_3725864 : Nat := 118140960795 + 3725864 * 2 ^ 59
def prefixEnd_3725864 : Nat := 4983230072969 + 3 ^ 40 * 3725864 * 2
def baseEnd_3725864 : Nat := 1275439390189010515776713

theorem tailTrace_3725864 : CollatzResearch.WordTrace tailWord_3725864 prefixEnd_3725864 1275439390189010515776713 := by
  unfold tailWord_3725864
  simp only [CollatzResearch.WordTrace]
  refine ⟨67946712086919264877868323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90595616115892353170491097 67946712086919264877868323)
  ·
    refine ⟨101920068130378897316802485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67946712086919264877868323 101920068130378897316802485)
    ·
      refine ⟨9555006387223021623450233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 101920068130378897316802485 9555006387223021623450233)
      ·
        refine ⟨7166254790417266217587675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9555006387223021623450233 7166254790417266217587675)
        ·
          refine ⟨10749382185625899326381513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7166254790417266217587675 10749382185625899326381513)
          ·
            refine ⟨8062036639219424494786135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10749382185625899326381513 8062036639219424494786135)
            ·
              refine ⟨12093054958829136742179203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8062036639219424494786135 12093054958829136742179203)
              ·
                refine ⟨18139582438243705113268805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12093054958829136742179203 18139582438243705113268805)
                ·
                  refine ⟨3401171707170694708737901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18139582438243705113268805 3401171707170694708737901)
                  ·
                    refine ⟨1275439390189010515776713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3401171707170694708737901 1275439390189010515776713)
                    ·
                      rfl

theorem cell22_3725864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 1, 1, 4, 3].length) (baseStart_3725864 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3725864 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3725864 prefixEnd_3725864 := by exact prefixLift 3725864
  have htrace : WordTrace (prefixWord ++ tailWord_3725864) baseStart_3725864 baseEnd_3725864 := by
    simpa [prefixWord, tailWord_3725864, baseEnd_3725864] using wordTrace_append hprefix tailTrace_3725864
  have hstable : (prefixWord ++ tailWord_3725864).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3725864).length < 2 ^ (prefixWord ++ tailWord_3725864).sum := by decide
  have hdescent : baseEnd_3725864 < baseStart_3725864 := by decide
  rcases family_descends (prefixWord ++ tailWord_3725864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3725894 : List Nat := [6, 1, 1, 1, 2, 2, 1, 8]
def baseStart_3725894 : Nat := 118140960795 + 3725894 * 2 ^ 59
def prefixEnd_3725894 : Nat := 4983230072969 + 3 ^ 40 * 3725894 * 2
def baseEnd_3725894 : Nat := 141716628866900048614069

theorem tailTrace_3725894 : CollatzResearch.WordTrace tailWord_3725894 prefixEnd_3725894 141716628866900048614069 := by
  unfold tailWord_3725894
  simp only [CollatzResearch.WordTrace]
  refine ⟨4246703698866557652479023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 90596345575819896586219157 4246703698866557652479023)
  ·
    refine ⟨6370055548299836478718535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4246703698866557652479023 6370055548299836478718535)
    ·
      refine ⟨9555083322449754718077803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6370055548299836478718535 9555083322449754718077803)
      ·
        refine ⟨14332624983674632077116705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9555083322449754718077803 14332624983674632077116705)
        ·
          refine ⟨10749468737755974057837529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14332624983674632077116705 10749468737755974057837529)
          ·
            refine ⟨8062101553316980543378147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10749468737755974057837529 8062101553316980543378147)
            ·
              refine ⟨12093152329975470815067221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8062101553316980543378147 12093152329975470815067221)
              ·
                refine ⟨141716628866900048614069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12093152329975470815067221 141716628866900048614069)
                ·
                  rfl

theorem cell22_3725894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 1, 8].length) (baseStart_3725894 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3725894 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3725894 prefixEnd_3725894 := by exact prefixLift 3725894
  have htrace : WordTrace (prefixWord ++ tailWord_3725894) baseStart_3725894 baseEnd_3725894 := by
    simpa [prefixWord, tailWord_3725894, baseEnd_3725894] using wordTrace_append hprefix tailTrace_3725894
  have hstable : (prefixWord ++ tailWord_3725894).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3725894).length < 2 ^ (prefixWord ++ tailWord_3725894).sum := by decide
  have hdescent : baseEnd_3725894 < baseStart_3725894 := by decide
  rcases family_descends (prefixWord ++ tailWord_3725894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3725905 : List Nat := [1, 2, 2, 1, 3, 3, 1, 2, 7]
def baseStart_3725905 : Nat := 118140960795 + 3725905 * 2 ^ 59
def prefixEnd_3725905 : Nat := 4983230072969 + 3 ^ 40 * 3725905 * 2
def baseEnd_3725905 : Nat := 425151141775633358500529

theorem tailTrace_3725905 : CollatzResearch.WordTrace tailWord_3725905 prefixEnd_3725905 425151141775633358500529 := by
  unfold tailWord_3725905
  simp only [CollatzResearch.WordTrace]
  refine ⟨135894919566689993757979169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90596613044459995838652779 135894919566689993757979169)
  ·
    refine ⟨101921189675017495318484377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135894919566689993757979169 101921189675017495318484377)
    ·
      refine ⟨76440892256263121488863283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101921189675017495318484377 76440892256263121488863283)
      ·
        refine ⟨114661338384394682233294925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76440892256263121488863283 114661338384394682233294925)
        ·
          refine ⟨42998001894148005837485597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 114661338384394682233294925 42998001894148005837485597)
          ·
            refine ⟨16124250710305502189057099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42998001894148005837485597 16124250710305502189057099)
            ·
              refine ⟨24186376065458253283585649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16124250710305502189057099 24186376065458253283585649)
              ·
                refine ⟨18139782049093689962689237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24186376065458253283585649 18139782049093689962689237)
                ·
                  refine ⟨425151141775633358500529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18139782049093689962689237 425151141775633358500529)
                  ·
                    rfl

theorem cell22_3725905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 1, 2, 7].length) (baseStart_3725905 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3725905 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3725905 prefixEnd_3725905 := by exact prefixLift 3725905
  have htrace : WordTrace (prefixWord ++ tailWord_3725905) baseStart_3725905 baseEnd_3725905 := by
    simpa [prefixWord, tailWord_3725905, baseEnd_3725905] using wordTrace_append hprefix tailTrace_3725905
  have hstable : (prefixWord ++ tailWord_3725905).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3725905).length < 2 ^ (prefixWord ++ tailWord_3725905).sum := by decide
  have hdescent : baseEnd_3725905 < baseStart_3725905 := by decide
  rcases family_descends (prefixWord ++ tailWord_3725905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3725920 : List Nat := [2, 1, 1, 3, 2, 1, 2, 1, 4, 5]
def baseStart_3725920 : Nat := 118140960795 + 3725920 * 2 ^ 59
def prefixEnd_3725920 : Nat := 4983230072969 + 3 ^ 40 * 3725920 * 2
def baseEnd_3725920 : Nat := 1275458560133445036376541

theorem tailTrace_3725920 : CollatzResearch.WordTrace tailWord_3725920 prefixEnd_3725920 1275458560133445036376541 := by
  unfold tailWord_3725920
  simp only [CollatzResearch.WordTrace]
  refine ⟨67947733330817825659887607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90596977774423767546516809 67947733330817825659887607)
  ·
    refine ⟨101921599996226738489831411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67947733330817825659887607 101921599996226738489831411)
    ·
      refine ⟨152882399994340107734747117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101921599996226738489831411 152882399994340107734747117)
      ·
        refine ⟨57330899997877540400530169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 152882399994340107734747117 57330899997877540400530169)
        ·
          refine ⟨42998174998408155300397627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57330899997877540400530169 42998174998408155300397627)
          ·
            refine ⟨64497262497612232950596441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42998174998408155300397627 64497262497612232950596441)
            ·
              refine ⟨48372946873209174712947331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64497262497612232950596441 48372946873209174712947331)
              ·
                refine ⟨72559420309813762069420997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48372946873209174712947331 72559420309813762069420997)
                ·
                  refine ⟨13604891308090080388016437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 72559420309813762069420997 13604891308090080388016437)
                  ·
                    refine ⟨1275458560133445036376541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13604891308090080388016437 1275458560133445036376541)
                    ·
                      rfl

theorem cell22_3725920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 1, 4, 5].length) (baseStart_3725920 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3725920 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3725920 prefixEnd_3725920 := by exact prefixLift 3725920
  have htrace : WordTrace (prefixWord ++ tailWord_3725920) baseStart_3725920 baseEnd_3725920 := by
    simpa [prefixWord, tailWord_3725920, baseEnd_3725920] using wordTrace_append hprefix tailTrace_3725920
  have hstable : (prefixWord ++ tailWord_3725920).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3725920).length < 2 ^ (prefixWord ++ tailWord_3725920).sum := by decide
  have hdescent : baseEnd_3725920 < baseStart_3725920 := by decide
  rcases family_descends (prefixWord ++ tailWord_3725920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3725952 : List Nat := [2, 1, 1, 2, 1, 6, 1, 1, 3, 4]
def baseStart_3725952 : Nat := 118140960795 + 3725952 * 2 ^ 59
def prefixEnd_3725952 : Nat := 4983230072969 + 3 ^ 40 * 3725952 * 2
def baseEnd_3725952 : Nat := 1275469514387407619576443

theorem tailTrace_3725952 : CollatzResearch.WordTrace tailWord_3725952 prefixEnd_3725952 1275469514387407619576443 := by
  unfold tailWord_3725952
  simp only [CollatzResearch.WordTrace]
  refine ⟨67948316898759860392470055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90597755865013147189960073 67948316898759860392470055)
  ·
    refine ⟨101922475348139790588705083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67948316898759860392470055 101922475348139790588705083)
    ·
      refine ⟨152883713022209685883057625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101922475348139790588705083 152883713022209685883057625)
      ·
        refine ⟨114662784766657264412293219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152883713022209685883057625 114662784766657264412293219)
        ·
          refine ⟨171994177149985896618439829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114662784766657264412293219 171994177149985896618439829)
          ·
            refine ⟨8062227053905588903989367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 171994177149985896618439829 8062227053905588903989367)
            ·
              refine ⟨12093340580858383355984051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8062227053905588903989367 12093340580858383355984051)
              ·
                refine ⟨18140010871287575033976077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12093340580858383355984051 18140010871287575033976077)
                ·
                  refine ⟨6802504076732840637741029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18140010871287575033976077 6802504076732840637741029)
                  ·
                    refine ⟨1275469514387407619576443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6802504076732840637741029 1275469514387407619576443)
                    ·
                      rfl

theorem cell22_3725952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 1, 1, 3, 4].length) (baseStart_3725952 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3725952 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3725952 prefixEnd_3725952 := by exact prefixLift 3725952
  have htrace : WordTrace (prefixWord ++ tailWord_3725952) baseStart_3725952 baseEnd_3725952 := by
    simpa [prefixWord, tailWord_3725952, baseEnd_3725952] using wordTrace_append hprefix tailTrace_3725952
  have hstable : (prefixWord ++ tailWord_3725952).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3725952).length < 2 ^ (prefixWord ++ tailWord_3725952).sum := by decide
  have hdescent : baseEnd_3725952 < baseStart_3725952 := by decide
  rcases family_descends (prefixWord ++ tailWord_3725952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3725999 : List Nat := [1, 1, 2, 1, 2, 5, 2, 3, 2, 3]
def baseStart_3725999 : Nat := 118140960795 + 3725999 * 2 ^ 59
def prefixEnd_3725999 : Nat := 4983230072969 + 3 ^ 40 * 3725999 * 2
def baseEnd_3725999 : Nat := 1275485603447915163651299

theorem tailTrace_3725999 : CollatzResearch.WordTrace tailWord_3725999 prefixEnd_3725999 1275485603447915163651299 := by
  unfold tailWord_3725999
  simp only [CollatzResearch.WordTrace]
  refine ⟨135898348028349447811901051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90598898685566298541267367 135898348028349447811901051)
  ·
    refine ⟨203847522042524171717851577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135898348028349447811901051 203847522042524171717851577)
    ·
      refine ⟨152885641531893128788388683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 203847522042524171717851577 152885641531893128788388683)
      ·
        refine ⟨229328462297839693182583025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152885641531893128788388683 229328462297839693182583025)
        ·
          refine ⟨171996346723379769886937269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 229328462297839693182583025 171996346723379769886937269)
          ·
            refine ⟨16124657505316853426900369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 171996346723379769886937269 16124657505316853426900369)
            ·
              refine ⟨12093493128987640070175277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16124657505316853426900369 12093493128987640070175277)
              ·
                refine ⟨4535059923370365026315729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12093493128987640070175277 4535059923370365026315729)
                ·
                  refine ⟨3401294942527773769736797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4535059923370365026315729 3401294942527773769736797)
                  ·
                    refine ⟨1275485603447915163651299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3401294942527773769736797 1275485603447915163651299)
                    ·
                      rfl

theorem cell22_3725999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 2, 3, 2, 3].length) (baseStart_3725999 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3725999 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3725999 prefixEnd_3725999 := by exact prefixLift 3725999
  have htrace : WordTrace (prefixWord ++ tailWord_3725999) baseStart_3725999 baseEnd_3725999 := by
    simpa [prefixWord, tailWord_3725999, baseEnd_3725999] using wordTrace_append hprefix tailTrace_3725999
  have hstable : (prefixWord ++ tailWord_3725999).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3725999).length < 2 ^ (prefixWord ++ tailWord_3725999).sum := by decide
  have hdescent : baseEnd_3725999 < baseStart_3725999 := by decide
  rcases family_descends (prefixWord ++ tailWord_3725999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3726057 : List Nat := [1, 2, 1, 1, 1, 2, 4, 5, 5]
def baseStart_3726057 : Nat := 118140960795 + 3726057 * 2 ^ 59
def prefixEnd_3726057 : Nat := 4983230072969 + 3 ^ 40 * 3726057 * 2
def baseEnd_3726057 : Nat := 425168486011074115233707

theorem tailTrace_3726057 : CollatzResearch.WordTrace tailWord_3726057 prefixEnd_3726057 425168486011074115233707 := by
  unfold tailWord_3726057
  simp only [CollatzResearch.WordTrace]
  refine ⟨135900463462139323717512425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90600308974759549145008283 135900463462139323717512425)
  ·
    refine ⟨101925347596604492788134319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135900463462139323717512425 101925347596604492788134319)
    ·
      refine ⟨152888021394906739182201479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101925347596604492788134319 152888021394906739182201479)
      ·
        refine ⟨229332032092360108773302219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152888021394906739182201479 229332032092360108773302219)
        ·
          refine ⟨343998048138540163159953329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 229332032092360108773302219 343998048138540163159953329)
          ·
            refine ⟨257998536103905122369964997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 343998048138540163159953329 257998536103905122369964997)
            ·
              refine ⟨48374725519482210444368437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 257998536103905122369964997 48374725519482210444368437)
              ·
                refine ⟨4535130517451457229159541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 48374725519482210444368437 4535130517451457229159541)
                ·
                  refine ⟨425168486011074115233707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4535130517451457229159541 425168486011074115233707)
                  ·
                    rfl

theorem cell22_3726057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 5, 5].length) (baseStart_3726057 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3726057 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3726057 prefixEnd_3726057 := by exact prefixLift 3726057
  have htrace : WordTrace (prefixWord ++ tailWord_3726057) baseStart_3726057 baseEnd_3726057 := by
    simpa [prefixWord, tailWord_3726057, baseEnd_3726057] using wordTrace_append hprefix tailTrace_3726057
  have hstable : (prefixWord ++ tailWord_3726057).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3726057).length < 2 ^ (prefixWord ++ tailWord_3726057).sum := by decide
  have hdescent : baseEnd_3726057 < baseStart_3726057 := by decide
  rcases family_descends (prefixWord ++ tailWord_3726057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3726138 : List Nat := [3, 1, 1, 1, 6, 1, 3, 1, 1, 4]
def baseStart_3726138 : Nat := 118140960795 + 3726138 * 2 ^ 59
def prefixEnd_3726138 : Nat := 4983230072969 + 3 ^ 40 * 3726138 * 2
def baseEnd_3726138 : Nat := 1275533185988565134425873

theorem tailTrace_3726138 : CollatzResearch.WordTrace tailWord_3726138 prefixEnd_3726138 1275533185988565134425873 := by
  unfold tailWord_3726138
  simp only [CollatzResearch.WordTrace]
  refine ⟨33975854443711468637802767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90602278516563916367474045 33975854443711468637802767)
  ·
    refine ⟨50963781665567202956704151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33975854443711468637802767 50963781665567202956704151)
    ·
      refine ⟨76445672498350804435056227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50963781665567202956704151 76445672498350804435056227)
      ·
        refine ⟨114668508747526206652584341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76445672498350804435056227 114668508747526206652584341)
        ·
          refine ⟨5375086347540290936839891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 114668508747526206652584341 5375086347540290936839891)
          ·
            refine ⟨8062629521310436405259837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5375086347540290936839891 8062629521310436405259837)
            ·
              refine ⟨3023486070491413651972439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8062629521310436405259837 3023486070491413651972439)
              ·
                refine ⟨4535229105737120477958659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3023486070491413651972439 4535229105737120477958659)
                ·
                  refine ⟨6802843658605680716937989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4535229105737120477958659 6802843658605680716937989)
                  ·
                    refine ⟨1275533185988565134425873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6802843658605680716937989 1275533185988565134425873)
                    ·
                      rfl

theorem cell22_3726138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 3, 1, 1, 4].length) (baseStart_3726138 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3726138 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3726138 prefixEnd_3726138 := by exact prefixLift 3726138
  have htrace : WordTrace (prefixWord ++ tailWord_3726138) baseStart_3726138 baseEnd_3726138 := by
    simpa [prefixWord, tailWord_3726138, baseEnd_3726138] using wordTrace_append hprefix tailTrace_3726138
  have hstable : (prefixWord ++ tailWord_3726138).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3726138).length < 2 ^ (prefixWord ++ tailWord_3726138).sum := by decide
  have hdescent : baseEnd_3726138 < baseStart_3726138 := by decide
  rcases family_descends (prefixWord ++ tailWord_3726138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3726153 : List Nat := [1, 2, 1, 1, 2, 7, 2, 2, 4]
def baseStart_3726153 : Nat := 118140960795 + 3726153 * 2 ^ 59
def prefixEnd_3726153 : Nat := 4983230072969 + 3 ^ 40 * 3726153 * 2
def baseEnd_3726153 : Nat := 425179440265036698433609

theorem tailTrace_3726153 : CollatzResearch.WordTrace tailWord_3726153 prefixEnd_3726153 425179440265036698433609 := by
  unfold tailWord_3726153
  simp only [CollatzResearch.WordTrace]
  refine ⟨135903964869791532113007113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90602643246527688075338075 135903964869791532113007113)
  ·
    refine ⟨101927973652343649084755335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135903964869791532113007113 101927973652343649084755335)
    ·
      refine ⟨152891960478515473627133003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101927973652343649084755335 152891960478515473627133003)
      ·
        refine ⟨229337940717773210440699505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152891960478515473627133003 229337940717773210440699505)
        ·
          refine ⟨172003455538329907830524629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 229337940717773210440699505 172003455538329907830524629)
          ·
            refine ⟨4031330989179607214777921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 172003455538329907830524629 4031330989179607214777921)
            ·
              refine ⟨3023498241884705411083441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4031330989179607214777921 3023498241884705411083441)
              ·
                refine ⟨2267623681413529058312581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3023498241884705411083441 2267623681413529058312581)
                ·
                  refine ⟨425179440265036698433609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2267623681413529058312581 425179440265036698433609)
                  ·
                    rfl

theorem cell22_3726153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 7, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 7, 2, 2, 4].length) (baseStart_3726153 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3726153 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3726153 prefixEnd_3726153 := by exact prefixLift 3726153
  have htrace : WordTrace (prefixWord ++ tailWord_3726153) baseStart_3726153 baseEnd_3726153 := by
    simpa [prefixWord, tailWord_3726153, baseEnd_3726153] using wordTrace_append hprefix tailTrace_3726153
  have hstable : (prefixWord ++ tailWord_3726153).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3726153).length < 2 ^ (prefixWord ++ tailWord_3726153).sum := by decide
  have hdescent : baseEnd_3726153 < baseStart_3726153 := by decide
  rcases family_descends (prefixWord ++ tailWord_3726153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3726213 : List Nat := [1, 3, 1, 1, 3, 3, 2, 4, 1, 3]
def baseStart_3726213 : Nat := 118140960795 + 3726213 * 2 ^ 59
def prefixEnd_3726213 : Nat := 4983230072969 + 3 ^ 40 * 3726213 * 2
def baseEnd_3726213 : Nat := 1275558860021289938800643

theorem tailTrace_3726213 : CollatzResearch.WordTrace tailWord_3726213 prefixEnd_3726213 1275558860021289938800643 := by
  unfold tailWord_3726213
  simp only [CollatzResearch.WordTrace]
  refine ⟨135906153249574162360191293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90604102166382774906794195 135906153249574162360191293)
  ·
    refine ⟨50964807468590310885071735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135906153249574162360191293 50964807468590310885071735)
    ·
      refine ⟨76447211202885466327607603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50964807468590310885071735 76447211202885466327607603)
      ·
        refine ⟨114670816804328199491411405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76447211202885466327607603 114670816804328199491411405)
        ·
          refine ⟨43001556301623074809279277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 114670816804328199491411405 43001556301623074809279277)
          ·
            refine ⟨16125583613108653053479729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43001556301623074809279277 16125583613108653053479729)
            ·
              refine ⟨12094187709831489790109797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16125583613108653053479729 12094187709831489790109797)
              ·
                refine ⟨2267660195593404335645587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12094187709831489790109797 2267660195593404335645587)
                ·
                  refine ⟨3401490293390106503468381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2267660195593404335645587 3401490293390106503468381)
                  ·
                    refine ⟨1275558860021289938800643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3401490293390106503468381 1275558860021289938800643)
                    ·
                      rfl

theorem cell22_3726213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 2, 4, 1, 3].length) (baseStart_3726213 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3726213 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3726213 prefixEnd_3726213 := by exact prefixLift 3726213
  have htrace : WordTrace (prefixWord ++ tailWord_3726213) baseStart_3726213 baseEnd_3726213 := by
    simpa [prefixWord, tailWord_3726213, baseEnd_3726213] using wordTrace_append hprefix tailTrace_3726213
  have hstable : (prefixWord ++ tailWord_3726213).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3726213).length < 2 ^ (prefixWord ++ tailWord_3726213).sum := by decide
  have hdescent : baseEnd_3726213 < baseStart_3726213 := by decide
  rcases family_descends (prefixWord ++ tailWord_3726213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3726247 : List Nat := [1, 1, 6, 1, 3, 2, 1, 3, 1, 3]
def baseStart_3726247 : Nat := 118140960795 + 3726247 * 2 ^ 59
def prefixEnd_3726247 : Nat := 4983230072969 + 3 ^ 40 * 3726247 * 2
def baseEnd_3726247 : Nat := 1275570498916125183450539

theorem tailTrace_3726247 : CollatzResearch.WordTrace tailWord_3726247 prefixEnd_3726247 1275570498916125183450539 := by
  unfold tailWord_3726247
  simp only [CollatzResearch.WordTrace]
  refine ⟨135907393331450986166928995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90604928887633990777952663 135907393331450986166928995)
  ·
    refine ⟨203861089997176479250393493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135907393331450986166928995 203861089997176479250393493)
    ·
      refine ⟨9555988593617647464862195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 203861089997176479250393493 9555988593617647464862195)
      ·
        refine ⟨14333982890426471197293293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9555988593617647464862195 14333982890426471197293293)
        ·
          refine ⟨5375243583909926698984985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14333982890426471197293293 5375243583909926698984985)
          ·
            refine ⟨4031432687932445024238739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5375243583909926698984985 4031432687932445024238739)
            ·
              refine ⟨6047149031898667536358109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4031432687932445024238739 6047149031898667536358109)
              ·
                refine ⟨2267680886962000326134291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6047149031898667536358109 2267680886962000326134291)
                ·
                  refine ⟨3401521330443000489201437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2267680886962000326134291 3401521330443000489201437)
                  ·
                    refine ⟨1275570498916125183450539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3401521330443000489201437 1275570498916125183450539)
                    ·
                      rfl

theorem cell22_3726247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 2, 1, 3, 1, 3].length) (baseStart_3726247 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3726247 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3726247 prefixEnd_3726247 := by exact prefixLift 3726247
  have htrace : WordTrace (prefixWord ++ tailWord_3726247) baseStart_3726247 baseEnd_3726247 := by
    simpa [prefixWord, tailWord_3726247, baseEnd_3726247] using wordTrace_append hprefix tailTrace_3726247
  have hstable : (prefixWord ++ tailWord_3726247).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3726247).length < 2 ^ (prefixWord ++ tailWord_3726247).sum := by decide
  have hdescent : baseEnd_3726247 < baseStart_3726247 := by decide
  rcases family_descends (prefixWord ++ tailWord_3726247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3726290 : List Nat := [3, 2, 2, 3, 1, 3, 1, 2, 1, 4]
def baseStart_3726290 : Nat := 118140960795 + 3726290 * 2 ^ 59
def prefixEnd_3726290 : Nat := 4983230072969 + 3 ^ 40 * 3726290 * 2
def baseEnd_3726290 : Nat := 1275585218694887404625407

theorem tailTrace_3726290 : CollatzResearch.WordTrace tailWord_3726290 prefixEnd_3726290 1275585218694887404625407 := by
  unfold tailWord_3726290
  simp only [CollatzResearch.WordTrace]
  refine ⟨33977240417573801127686081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90605974446863469673829549 33977240417573801127686081)
  ·
    refine ⟨25482930313180350845764561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33977240417573801127686081 25482930313180350845764561)
    ·
      refine ⟨19112197734885263134323421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25482930313180350845764561 19112197734885263134323421)
      ·
        refine ⟨7167074150581973675371283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19112197734885263134323421 7167074150581973675371283)
        ·
          refine ⟨10750611225872960513056925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7167074150581973675371283 10750611225872960513056925)
          ·
            refine ⟨4031479209702360192396347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10750611225872960513056925 4031479209702360192396347)
            ·
              refine ⟨6047218814553540288594521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4031479209702360192396347 6047218814553540288594521)
              ·
                refine ⟨4535414110915155216445891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6047218814553540288594521 4535414110915155216445891)
                ·
                  refine ⟨6803121166372732824668837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4535414110915155216445891 6803121166372732824668837)
                  ·
                    refine ⟨1275585218694887404625407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6803121166372732824668837 1275585218694887404625407)
                    ·
                      rfl

theorem cell22_3726290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 3, 1, 2, 1, 4].length) (baseStart_3726290 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3726290 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3726290 prefixEnd_3726290 := by exact prefixLift 3726290
  have htrace : WordTrace (prefixWord ++ tailWord_3726290) baseStart_3726290 baseEnd_3726290 := by
    simpa [prefixWord, tailWord_3726290, baseEnd_3726290] using wordTrace_append hprefix tailTrace_3726290
  have hstable : (prefixWord ++ tailWord_3726290).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3726290).length < 2 ^ (prefixWord ++ tailWord_3726290).sum := by decide
  have hdescent : baseEnd_3726290 < baseStart_3726290 := by decide
  rcases family_descends (prefixWord ++ tailWord_3726290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3726329 : List Nat := [1, 2, 1, 3, 1, 3, 1, 1, 1, 8]
def baseStart_3726329 : Nat := 118140960795 + 3726329 * 2 ^ 59
def prefixEnd_3726329 : Nat := 4983230072969 + 3 ^ 40 * 3726329 * 2
def baseEnd_3726329 : Nat := 1275598569191904302900287

theorem tailTrace_3726329 : CollatzResearch.WordTrace tailWord_3726329 prefixEnd_3726329 1275598569191904302900287 := by
  unfold tailWord_3726329
  simp only [CollatzResearch.WordTrace]
  refine ⟨135910384117153914171414041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90606922744769276114276027 135910384117153914171414041)
  ·
    refine ⟨101932788087865435628560531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135910384117153914171414041 101932788087865435628560531)
    ·
      refine ⟨152899182131798153442840797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101932788087865435628560531 152899182131798153442840797)
      ·
        refine ⟨57337193299424307541065299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 152899182131798153442840797 57337193299424307541065299)
        ·
          refine ⟨86005789949136461311597949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57337193299424307541065299 86005789949136461311597949)
          ·
            refine ⟨32252171230926172991849231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86005789949136461311597949 32252171230926172991849231)
            ·
              refine ⟨48378256846389259487773847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32252171230926172991849231 48378256846389259487773847)
              ·
                refine ⟨72567385269583889231660771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48378256846389259487773847 72567385269583889231660771)
                ·
                  refine ⟨108851077904375833847491157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 72567385269583889231660771 108851077904375833847491157)
                  ·
                    refine ⟨1275598569191904302900287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 108851077904375833847491157 1275598569191904302900287)
                    ·
                      rfl

theorem cell22_3726329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 1, 1, 8].length) (baseStart_3726329 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3726329 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3726329 prefixEnd_3726329 := by exact prefixLift 3726329
  have htrace : WordTrace (prefixWord ++ tailWord_3726329) baseStart_3726329 baseEnd_3726329 := by
    simpa [prefixWord, tailWord_3726329, baseEnd_3726329] using wordTrace_append hprefix tailTrace_3726329
  have hstable : (prefixWord ++ tailWord_3726329).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3726329).length < 2 ^ (prefixWord ++ tailWord_3726329).sum := by decide
  have hdescent : baseEnd_3726329 < baseStart_3726329 := by decide
  rcases family_descends (prefixWord ++ tailWord_3726329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3726331 : List Nat := [1, 1, 1, 1, 1, 3, 3, 5, 3, 3]
def baseStart_3726331 : Nat := 118140960795 + 3726331 * 2 ^ 59
def prefixEnd_3726331 : Nat := 4983230072969 + 3 ^ 40 * 3726331 * 2
def baseEnd_3726331 : Nat := 1275599253832776964350281

theorem tailTrace_3726331 : CollatzResearch.WordTrace tailWord_3726331 prefixEnd_3726331 1275599253832776964350281 := by
  unfold tailWord_3726331
  simp only [CollatzResearch.WordTrace]
  refine ⟨135910457063146668512986847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90606971375431112341991231 135910457063146668512986847)
  ·
    refine ⟨203865685594720002769480271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135910457063146668512986847 203865685594720002769480271)
    ·
      refine ⟨305798528392080004154220407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203865685594720002769480271 305798528392080004154220407)
      ·
        refine ⟨458697792588120006231330611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 305798528392080004154220407 458697792588120006231330611)
        ·
          refine ⟨688046688882180009346995917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 458697792588120006231330611 688046688882180009346995917)
          ·
            refine ⟨258017508330817503505123469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 688046688882180009346995917 258017508330817503505123469)
            ·
              refine ⟨96756565624056563814421301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 258017508330817503505123469 96756565624056563814421301)
              ·
                refine ⟨9070928027255302857601997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 96756565624056563814421301 9070928027255302857601997)
                ·
                  refine ⟨3401598010220738571600749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9070928027255302857601997 3401598010220738571600749)
                  ·
                    refine ⟨1275599253832776964350281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3401598010220738571600749 1275599253832776964350281)
                    ·
                      rfl

theorem cell22_3726331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 5, 3, 3].length) (baseStart_3726331 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3726331 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3726331 prefixEnd_3726331 := by exact prefixLift 3726331
  have htrace : WordTrace (prefixWord ++ tailWord_3726331) baseStart_3726331 baseEnd_3726331 := by
    simpa [prefixWord, tailWord_3726331, baseEnd_3726331] using wordTrace_append hprefix tailTrace_3726331
  have hstable : (prefixWord ++ tailWord_3726331).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3726331).length < 2 ^ (prefixWord ++ tailWord_3726331).sum := by decide
  have hdescent : baseEnd_3726331 < baseStart_3726331 := by decide
  rcases family_descends (prefixWord ++ tailWord_3726331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3726348 : List Nat := [2, 2, 1, 2, 3, 3, 1, 2, 3, 3]
def baseStart_3726348 : Nat := 118140960795 + 3726348 * 2 ^ 59
def prefixEnd_3726348 : Nat := 4983230072969 + 3 ^ 40 * 3726348 * 2
def baseEnd_3726348 : Nat := 1275605073280194586675229

theorem tailTrace_3726348 : CollatzResearch.WordTrace tailWord_3726348 prefixEnd_3726348 1275605073280194586675229 := by
  unfold tailWord_3726348
  simp only [CollatzResearch.WordTrace]
  refine ⟨67955538552042540208177849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90607384736056720277570465 67955538552042540208177849)
  ·
    refine ⟨50966653914031905156133387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67955538552042540208177849 50966653914031905156133387)
    ·
      refine ⟨76449980871047857734200081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50966653914031905156133387 76449980871047857734200081)
      ·
        refine ⟨57337485653285893300650061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76449980871047857734200081 57337485653285893300650061)
        ·
          refine ⟨21501557119982209987743773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57337485653285893300650061 21501557119982209987743773)
          ·
            refine ⟨8063083919993328745403915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21501557119982209987743773 8063083919993328745403915)
            ·
              refine ⟨12094625879989993118105873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8063083919993328745403915 12094625879989993118105873)
              ·
                refine ⟨9070969409992494838579405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12094625879989993118105873 9070969409992494838579405)
                ·
                  refine ⟨3401613528747185564467277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9070969409992494838579405 3401613528747185564467277)
                  ·
                    refine ⟨1275605073280194586675229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3401613528747185564467277 1275605073280194586675229)
                    ·
                      rfl

theorem cell22_3726348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 1, 2, 3, 3].length) (baseStart_3726348 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3726348 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3726348 prefixEnd_3726348 := by exact prefixLift 3726348
  have htrace : WordTrace (prefixWord ++ tailWord_3726348) baseStart_3726348 baseEnd_3726348 := by
    simpa [prefixWord, tailWord_3726348, baseEnd_3726348] using wordTrace_append hprefix tailTrace_3726348
  have hstable : (prefixWord ++ tailWord_3726348).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3726348).length < 2 ^ (prefixWord ++ tailWord_3726348).sum := by decide
  have hdescent : baseEnd_3726348 < baseStart_3726348 := by decide
  rcases family_descends (prefixWord ++ tailWord_3726348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3726378 : List Nat := [3, 1, 4, 1, 3, 1, 1, 1, 7]
def baseStart_3726378 : Nat := 118140960795 + 3726378 * 2 ^ 59
def prefixEnd_3726378 : Nat := 4983230072969 + 3 ^ 40 * 3726378 * 2
def baseEnd_3726378 : Nat := 425205114297761502808379

theorem tailTrace_3726378 : CollatzResearch.WordTrace tailWord_3726378 prefixEnd_3726378 425205114297761502808379 := by
  unfold tailWord_3726378
  simp only [CollatzResearch.WordTrace]
  refine ⟨33978042823494098884986947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90608114195984263693298525 33978042823494098884986947)
  ·
    refine ⟨50967064235241148327480421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33978042823494098884986947 50967064235241148327480421)
    ·
      refine ⟨9556324544107715311402579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50967064235241148327480421 9556324544107715311402579)
      ·
        refine ⟨14334486816161572967103869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9556324544107715311402579 14334486816161572967103869)
        ·
          refine ⟨5375432556060589862663951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14334486816161572967103869 5375432556060589862663951)
          ·
            refine ⟨8063148834090884793995927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5375432556060589862663951 8063148834090884793995927)
            ·
              refine ⟨12094723251136327190993891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8063148834090884793995927 12094723251136327190993891)
              ·
                refine ⟨18142084876704490786490837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12094723251136327190993891 18142084876704490786490837)
                ·
                  refine ⟨425205114297761502808379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18142084876704490786490837 425205114297761502808379)
                  ·
                    rfl

theorem cell22_3726378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 1, 1, 7].length) (baseStart_3726378 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3726378 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3726378 prefixEnd_3726378 := by exact prefixLift 3726378
  have htrace : WordTrace (prefixWord ++ tailWord_3726378) baseStart_3726378 baseEnd_3726378 := by
    simpa [prefixWord, tailWord_3726378, baseEnd_3726378] using wordTrace_append hprefix tailTrace_3726378
  have hstable : (prefixWord ++ tailWord_3726378).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3726378).length < 2 ^ (prefixWord ++ tailWord_3726378).sum := by decide
  have hdescent : baseEnd_3726378 < baseStart_3726378 := by decide
  rcases family_descends (prefixWord ++ tailWord_3726378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3726408 : List Nat := [2, 1, 3, 1, 1, 1, 6, 2, 1, 4]
def baseStart_3726408 : Nat := 118140960795 + 3726408 * 2 ^ 59
def prefixEnd_3726408 : Nat := 4983230072969 + 3 ^ 40 * 3726408 * 2
def baseEnd_3726408 : Nat := 1275625612506374430175045

theorem tailTrace_3726408 : CollatzResearch.WordTrace tailWord_3726408 prefixEnd_3726408 1275625612506374430175045 := by
  unfold tailWord_3726408
  simp only [CollatzResearch.WordTrace]
  refine ⟨67956632741933855331769939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90608843655911807109026585 67956632741933855331769939)
  ·
    refine ⟨101934949112900782997654909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67956632741933855331769939 101934949112900782997654909)
    ·
      refine ⟨38225605917337793624120591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101934949112900782997654909 38225605917337793624120591)
      ·
        refine ⟨57338408876006690436180887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38225605917337793624120591 57338408876006690436180887)
        ·
          refine ⟨86007613314010035654271331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57338408876006690436180887 86007613314010035654271331)
          ·
            refine ⟨129011419971015053481406997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86007613314010035654271331 129011419971015053481406997)
            ·
              refine ⟨6047410311141330631940953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 129011419971015053481406997 6047410311141330631940953)
              ·
                refine ⟨4535557733355997973955715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6047410311141330631940953 4535557733355997973955715)
                ·
                  refine ⟨6803336600033996960933573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4535557733355997973955715 6803336600033996960933573)
                  ·
                    refine ⟨1275625612506374430175045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6803336600033996960933573 1275625612506374430175045)
                    ·
                      rfl

theorem cell22_3726408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 6, 2, 1, 4].length) (baseStart_3726408 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3726408 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3726408 prefixEnd_3726408 := by exact prefixLift 3726408
  have htrace : WordTrace (prefixWord ++ tailWord_3726408) baseStart_3726408 baseEnd_3726408 := by
    simpa [prefixWord, tailWord_3726408, baseEnd_3726408] using wordTrace_append hprefix tailTrace_3726408
  have hstable : (prefixWord ++ tailWord_3726408).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3726408).length < 2 ^ (prefixWord ++ tailWord_3726408).sum := by decide
  have hdescent : baseEnd_3726408 < baseStart_3726408 := by decide
  rcases family_descends (prefixWord ++ tailWord_3726408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3726421 : List Nat := [1, 3, 2, 2, 1, 2, 2, 1, 3, 5]
def baseStart_3726421 : Nat := 118140960795 + 3726421 * 2 ^ 59
def prefixEnd_3726421 : Nat := 4983230072969 + 3 ^ 40 * 3726421 * 2
def baseEnd_3726421 : Nat := 1275630062672046729600005

theorem tailTrace_3726421 : CollatzResearch.WordTrace tailWord_3726421 prefixEnd_3726421 1275630062672046729600005 := by
  unfold tailWord_3726421
  simp only [CollatzResearch.WordTrace]
  refine ⟨135913739632820613883763117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90609159755213742589175411 135913739632820613883763117)
  ·
    refine ⟨50967652362307730206411169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135913739632820613883763117 50967652362307730206411169)
    ·
      refine ⟨38225739271730797654808377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50967652362307730206411169 38225739271730797654808377)
      ·
        refine ⟨28669304453798098241106283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38225739271730797654808377 28669304453798098241106283)
        ·
          refine ⟨43003956680697147361659425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28669304453798098241106283 43003956680697147361659425)
          ·
            refine ⟨32252967510522860521244569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43003956680697147361659425 32252967510522860521244569)
            ·
              refine ⟨24189725632892145390933427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32252967510522860521244569 24189725632892145390933427)
              ·
                refine ⟨36284588449338218086400141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24189725632892145390933427 36284588449338218086400141)
                ·
                  refine ⟨13606720668501831782400053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36284588449338218086400141 13606720668501831782400053)
                  ·
                    refine ⟨1275630062672046729600005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13606720668501831782400053 1275630062672046729600005)
                    ·
                      rfl

theorem cell22_3726421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 2, 1, 3, 5].length) (baseStart_3726421 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3726421 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3726421 prefixEnd_3726421 := by exact prefixLift 3726421
  have htrace : WordTrace (prefixWord ++ tailWord_3726421) baseStart_3726421 baseEnd_3726421 := by
    simpa [prefixWord, tailWord_3726421, baseEnd_3726421] using wordTrace_append hprefix tailTrace_3726421
  have hstable : (prefixWord ++ tailWord_3726421).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3726421).length < 2 ^ (prefixWord ++ tailWord_3726421).sum := by decide
  have hdescent : baseEnd_3726421 < baseStart_3726421 := by decide
  rcases family_descends (prefixWord ++ tailWord_3726421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3726511 : List Nat := [1, 1, 2, 1, 2, 3, 3, 1, 1, 7]
def baseStart_3726511 : Nat := 118140960795 + 3726511 * 2 ^ 59
def prefixEnd_3726511 : Nat := 4983230072969 + 3 ^ 40 * 3726511 * 2
def baseEnd_3726511 : Nat := 1275660871511316494849729

theorem tailTrace_3726511 : CollatzResearch.WordTrace tailWord_3726511 prefixEnd_3726511 1275660871511316494849729 := by
  unfold tailWord_3726511
  simp only [CollatzResearch.WordTrace]
  refine ⟨135917022202494559254539387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90611348134996372836359591 135917022202494559254539387)
  ·
    refine ⟨203875533303741838881809081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135917022202494559254539387 203875533303741838881809081)
    ·
      refine ⟨152906649977806379161356811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 203875533303741838881809081 152906649977806379161356811)
      ·
        refine ⟨229359974966709568742035217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152906649977806379161356811 229359974966709568742035217)
        ·
          refine ⟨172019981225032176556526413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 229359974966709568742035217 172019981225032176556526413)
          ·
            refine ⟨64507492959387066208697405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 172019981225032176556526413 64507492959387066208697405)
            ·
              refine ⟨24190309859770149828261527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64507492959387066208697405 24190309859770149828261527)
              ·
                refine ⟨36285464789655224742392291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24190309859770149828261527 36285464789655224742392291)
                ·
                  refine ⟨54428197184482837113588437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36285464789655224742392291 54428197184482837113588437)
                  ·
                    refine ⟨1275660871511316494849729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 54428197184482837113588437 1275660871511316494849729)
                    ·
                      rfl

theorem cell22_3726511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 3, 1, 1, 7].length) (baseStart_3726511 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3726511 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3726511 prefixEnd_3726511 := by exact prefixLift 3726511
  have htrace : WordTrace (prefixWord ++ tailWord_3726511) baseStart_3726511 baseEnd_3726511 := by
    simpa [prefixWord, tailWord_3726511, baseEnd_3726511] using wordTrace_append hprefix tailTrace_3726511
  have hstable : (prefixWord ++ tailWord_3726511).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3726511).length < 2 ^ (prefixWord ++ tailWord_3726511).sum := by decide
  have hdescent : baseEnd_3726511 < baseStart_3726511 := by decide
  rcases family_descends (prefixWord ++ tailWord_3726511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3726603 : List Nat := [1, 1, 1, 1, 5, 5, 8]
def baseStart_3726603 : Nat := 118140960795 + 3726603 * 2 ^ 59
def prefixEnd_3726603 : Nat := 4983230072969 + 3 ^ 40 * 3726603 * 2
def baseEnd_3726603 : Nat := 47247865370054034131461

theorem tailTrace_3726603 : CollatzResearch.WordTrace tailWord_3726603 prefixEnd_3726603 47247865370054034131461 := by
  unfold tailWord_3726603
  simp only [CollatzResearch.WordTrace]
  refine ⟨135920377718161258966888463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90613585145440839311258975 135920377718161258966888463)
  ·
    refine ⟨203880566577241888450332695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135920377718161258966888463 203880566577241888450332695)
    ·
      refine ⟨305820849865862832675499043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203880566577241888450332695 305820849865862832675499043)
      ·
        refine ⟨458731274798794249013248565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 305820849865862832675499043 458731274798794249013248565)
        ·
          refine ⟨43006057012386960844992053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 458731274798794249013248565 43006057012386960844992053)
          ·
            refine ⟨4031817844911277579218005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 43006057012386960844992053 4031817844911277579218005)
            ·
              refine ⟨47247865370054034131461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4031817844911277579218005 47247865370054034131461)
              ·
                rfl

theorem cell22_3726603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 5, 8].length) (baseStart_3726603 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3726603 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3726603 prefixEnd_3726603 := by exact prefixLift 3726603
  have htrace : WordTrace (prefixWord ++ tailWord_3726603) baseStart_3726603 baseEnd_3726603 := by
    simpa [prefixWord, tailWord_3726603, baseEnd_3726603] using wordTrace_append hprefix tailTrace_3726603
  have hstable : (prefixWord ++ tailWord_3726603).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3726603).length < 2 ^ (prefixWord ++ tailWord_3726603).sum := by decide
  have hdescent : baseEnd_3726603 < baseStart_3726603 := by decide
  rcases family_descends (prefixWord ++ tailWord_3726603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3726727 : List Nat := [1, 1, 4, 2, 2, 2, 2, 4, 4]
def baseStart_3726727 : Nat := 118140960795 + 3726727 * 2 ^ 59
def prefixEnd_3726727 : Nat := 4983230072969 + 3 ^ 40 * 3726727 * 2
def baseEnd_3726727 : Nat := 425244937575187977149689

theorem tailTrace_3726727 : CollatzResearch.WordTrace tailWord_3726727 prefixEnd_3726727 425244937575187977149689 := by
  unfold tailWord_3726727
  simp only [CollatzResearch.WordTrace]
  refine ⟨135924900369712028144402435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90616600246474685429601623 135924900369712028144402435)
  ·
    refine ⟨203887350554568042216603653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135924900369712028144402435 203887350554568042216603653)
    ·
      refine ⟨38228878228981507915613185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 203887350554568042216603653 38228878228981507915613185)
      ·
        refine ⟨28671658671736130936709889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38228878228981507915613185 28671658671736130936709889)
        ·
          refine ⟨21503744003802098202532417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28671658671736130936709889 21503744003802098202532417)
          ·
            refine ⟨16127808002851573651899313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21503744003802098202532417 16127808002851573651899313)
            ·
              refine ⟨12095856002138680238924485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16127808002851573651899313 12095856002138680238924485)
              ·
                refine ⟨2267973000401002544798341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12095856002138680238924485 2267973000401002544798341)
                ·
                  refine ⟨425244937575187977149689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2267973000401002544798341 425244937575187977149689)
                  ·
                    rfl

theorem cell22_3726727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 2, 4, 4].length) (baseStart_3726727 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3726727 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3726727 prefixEnd_3726727 := by exact prefixLift 3726727
  have htrace : WordTrace (prefixWord ++ tailWord_3726727) baseStart_3726727 baseEnd_3726727 := by
    simpa [prefixWord, tailWord_3726727, baseEnd_3726727] using wordTrace_append hprefix tailTrace_3726727
  have hstable : (prefixWord ++ tailWord_3726727).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3726727).length < 2 ^ (prefixWord ++ tailWord_3726727).sum := by decide
  have hdescent : baseEnd_3726727 < baseStart_3726727 := by decide
  rcases family_descends (prefixWord ++ tailWord_3726727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3726787 : List Nat := [1, 1, 1, 3, 1, 1, 7, 1, 3, 3]
def baseStart_3726787 : Nat := 118140960795 + 3726787 * 2 ^ 59
def prefixEnd_3726787 : Nat := 4983230072969 + 3 ^ 40 * 3726787 * 2
def baseEnd_3726787 : Nat := 1275755351951743774948883

theorem tailTrace_3726787 : CollatzResearch.WordTrace tailWord_3726787 prefixEnd_3726787 1275755351951743774948883 := by
  unfold tailWord_3726787
  simp only [CollatzResearch.WordTrace]
  refine ⟨135927088749494658391586615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90618059166329772261057743 135927088749494658391586615)
  ·
    refine ⟨203890633124241987587379923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135927088749494658391586615 203890633124241987587379923)
    ·
      refine ⟨305835949686362981381069885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203890633124241987587379923 305835949686362981381069885)
      ·
        refine ⟨114688481132386118017901207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 305835949686362981381069885 114688481132386118017901207)
        ·
          refine ⟨172032721698579177026851811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114688481132386118017901207 172032721698579177026851811)
          ·
            refine ⟨258049082547868765540277717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 172032721698579177026851811 258049082547868765540277717)
            ·
              refine ⟨6048025372215674192350259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 258049082547868765540277717 6048025372215674192350259)
              ·
                refine ⟨9072038058323511288525389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6048025372215674192350259 9072038058323511288525389)
                ·
                  refine ⟨3402014271871316733197021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9072038058323511288525389 3402014271871316733197021)
                  ·
                    refine ⟨1275755351951743774948883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3402014271871316733197021 1275755351951743774948883)
                    ·
                      rfl

theorem cell22_3726787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 7, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 7, 1, 3, 3].length) (baseStart_3726787 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3726787 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3726787 prefixEnd_3726787 := by exact prefixLift 3726787
  have htrace : WordTrace (prefixWord ++ tailWord_3726787) baseStart_3726787 baseEnd_3726787 := by
    simpa [prefixWord, tailWord_3726787, baseEnd_3726787] using wordTrace_append hprefix tailTrace_3726787
  have hstable : (prefixWord ++ tailWord_3726787).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3726787).length < 2 ^ (prefixWord ++ tailWord_3726787).sum := by decide
  have hdescent : baseEnd_3726787 < baseStart_3726787 := by decide
  rcases family_descends (prefixWord ++ tailWord_3726787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3726800 : List Nat := [2, 1, 1, 1, 1, 2, 2, 7, 5]
def baseStart_3726800 : Nat := 118140960795 + 3726800 * 2 ^ 59
def prefixEnd_3726800 : Nat := 4983230072969 + 3 ^ 40 * 3726800 * 2
def baseEnd_3726800 : Nat := 425253267372472024791281

theorem tailTrace_3726800 : CollatzResearch.WordTrace tailWord_3726800 prefixEnd_3726800 425253267372472024791281 := by
  unfold tailWord_3726800
  simp only [CollatzResearch.WordTrace]
  refine ⟨67963781449223780805904927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90618375265631707741206569 67963781449223780805904927)
  ·
    refine ⟨101945672173835671208857391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67963781449223780805904927 101945672173835671208857391)
    ·
      refine ⟨152918508260753506813286087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101945672173835671208857391 152918508260753506813286087)
      ·
        refine ⟨229377762391130260219929131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152918508260753506813286087 229377762391130260219929131)
        ·
          refine ⟨344066643586695390329893697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 229377762391130260219929131 344066643586695390329893697)
          ·
            refine ⟨258049982690021542747420273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 344066643586695390329893697 258049982690021542747420273)
            ·
              refine ⟨193537487017516157060565205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 258049982690021542747420273 193537487017516157060565205)
              ·
                refine ⟨4536034851973034931106997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 193537487017516157060565205 4536034851973034931106997)
                ·
                  refine ⟨425253267372472024791281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4536034851973034931106997 425253267372472024791281)
                  ·
                    rfl

theorem cell22_3726800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 7, 5].length) (baseStart_3726800 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3726800 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3726800 prefixEnd_3726800 := by exact prefixLift 3726800
  have htrace : WordTrace (prefixWord ++ tailWord_3726800) baseStart_3726800 baseEnd_3726800 := by
    simpa [prefixWord, tailWord_3726800, baseEnd_3726800] using wordTrace_append hprefix tailTrace_3726800
  have hstable : (prefixWord ++ tailWord_3726800).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3726800).length < 2 ^ (prefixWord ++ tailWord_3726800).sum := by decide
  have hdescent : baseEnd_3726800 < baseStart_3726800 := by decide
  rcases family_descends (prefixWord ++ tailWord_3726800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3726834 : List Nat := [3, 2, 1, 4, 1, 2, 2, 2, 5]
def baseStart_3726834 : Nat := 118140960795 + 3726834 * 2 ^ 59
def prefixEnd_3726834 : Nat := 4983230072969 + 3 ^ 40 * 3726834 * 2
def baseEnd_3726834 : Nat := 425257147004083773007913

theorem tailTrace_3726834 : CollatzResearch.WordTrace tailWord_3726834 prefixEnd_3726834 425257147004083773007913 := by
  unfold tailWord_3726834
  simp only [CollatzResearch.WordTrace]
  refine ⟨33982200745081096354636889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90619201986882923612365037 33982200745081096354636889)
  ·
    refine ⟨25486650558810822265977667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33982200745081096354636889 25486650558810822265977667)
    ·
      refine ⟨38229975838216233398966501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25486650558810822265977667 38229975838216233398966501)
      ·
        refine ⟨7168120469665543762306219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38229975838216233398966501 7168120469665543762306219)
        ·
          refine ⟨10752180704498315643459329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7168120469665543762306219 10752180704498315643459329)
          ·
            refine ⟨8064135528373736732594497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10752180704498315643459329 8064135528373736732594497)
            ·
              refine ⟨6048101646280302549445873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8064135528373736732594497 6048101646280302549445873)
              ·
                refine ⟨4536076234710226912084405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6048101646280302549445873 4536076234710226912084405)
                ·
                  refine ⟨425257147004083773007913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4536076234710226912084405 425257147004083773007913)
                  ·
                    rfl

theorem cell22_3726834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 2, 2, 5].length) (baseStart_3726834 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3726834 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3726834 prefixEnd_3726834 := by exact prefixLift 3726834
  have htrace : WordTrace (prefixWord ++ tailWord_3726834) baseStart_3726834 baseEnd_3726834 := by
    simpa [prefixWord, tailWord_3726834, baseEnd_3726834] using wordTrace_append hprefix tailTrace_3726834
  have hstable : (prefixWord ++ tailWord_3726834).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3726834).length < 2 ^ (prefixWord ++ tailWord_3726834).sum := by decide
  have hdescent : baseEnd_3726834 < baseStart_3726834 := by decide
  rcases family_descends (prefixWord ++ tailWord_3726834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3726838 : List Nat := [5, 1, 1, 1, 2, 2, 4, 2, 1, 3]
def baseStart_3726838 : Nat := 118140960795 + 3726838 * 2 ^ 59
def prefixEnd_3726838 : Nat := 4983230072969 + 3 ^ 40 * 3726838 * 2
def baseEnd_3726838 : Nat := 1275772810293996641923727

theorem tailTrace_3726838 : CollatzResearch.WordTrace tailWord_3726838 prefixEnd_3726838 1275772810293996641923727 := by
  unfold tailWord_3726838
  simp only [CollatzResearch.WordTrace]
  refine ⟨8495559304519368381355823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 90619299248206596067795445 8495559304519368381355823)
  ·
    refine ⟨12743338956779052572033735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8495559304519368381355823 12743338956779052572033735)
    ·
      refine ⟨19115008435168578858050603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12743338956779052572033735 19115008435168578858050603)
      ·
        refine ⟨28672512652752868287075905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19115008435168578858050603 28672512652752868287075905)
        ·
          refine ⟨21504384489564651215306929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28672512652752868287075905 21504384489564651215306929)
          ·
            refine ⟨16128288367173488411480197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21504384489564651215306929 16128288367173488411480197)
            ·
              refine ⟨3024054068845029077152537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16128288367173488411480197 3024054068845029077152537)
              ·
                refine ⟨2268040551633771807864403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3024054068845029077152537 2268040551633771807864403)
                ·
                  refine ⟨3402060827450657711796605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2268040551633771807864403 3402060827450657711796605)
                  ·
                    refine ⟨1275772810293996641923727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3402060827450657711796605 1275772810293996641923727)
                    ·
                      rfl

theorem cell22_3726838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 4, 2, 1, 3].length) (baseStart_3726838 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3726838 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3726838 prefixEnd_3726838 := by exact prefixLift 3726838
  have htrace : WordTrace (prefixWord ++ tailWord_3726838) baseStart_3726838 baseEnd_3726838 := by
    simpa [prefixWord, tailWord_3726838, baseEnd_3726838] using wordTrace_append hprefix tailTrace_3726838
  have hstable : (prefixWord ++ tailWord_3726838).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3726838).length < 2 ^ (prefixWord ++ tailWord_3726838).sum := by decide
  have hdescent : baseEnd_3726838 < baseStart_3726838 := by decide
  rcases family_descends (prefixWord ++ tailWord_3726838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3726877 : List Nat := [1, 4, 2, 2, 1, 1, 1, 4, 1, 5]
def baseStart_3726877 : Nat := 118140960795 + 3726877 * 2 ^ 59
def prefixEnd_3726877 : Nat := 4983230072969 + 3 ^ 40 * 3726877 * 2
def baseEnd_3726877 : Nat := 1275786160791013540198607

theorem tailTrace_3726877 : CollatzResearch.WordTrace tailWord_3726877 prefixEnd_3726877 1275786160791013540198607 := by
  unfold tailWord_3726877
  simp only [CollatzResearch.WordTrace]
  refine ⟨135930371319168603762362885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90620247546112402508241923 135930371319168603762362885)
  ·
    refine ⟨25486944622344113205443041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 135930371319168603762362885 25486944622344113205443041)
    ·
      refine ⟨19115208466758084904082281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25486944622344113205443041 19115208466758084904082281)
      ·
        refine ⟨14336406350068563678061711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19115208466758084904082281 14336406350068563678061711)
        ·
          refine ⟨21504609525102845517092567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14336406350068563678061711 21504609525102845517092567)
          ·
            refine ⟨32256914287654268275638851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21504609525102845517092567 32256914287654268275638851)
            ·
              refine ⟨48385371431481402413458277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32256914287654268275638851 48385371431481402413458277)
              ·
                refine ⟨9072257143402762952523427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48385371431481402413458277 9072257143402762952523427)
                ·
                  refine ⟨13608385715104144428785141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9072257143402762952523427 13608385715104144428785141)
                  ·
                    refine ⟨1275786160791013540198607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13608385715104144428785141 1275786160791013540198607)
                    ·
                      rfl

theorem cell22_3726877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 4, 1, 5].length) (baseStart_3726877 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3726877 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3726877 prefixEnd_3726877 := by exact prefixLift 3726877
  have htrace : WordTrace (prefixWord ++ tailWord_3726877) baseStart_3726877 baseEnd_3726877 := by
    simpa [prefixWord, tailWord_3726877, baseEnd_3726877] using wordTrace_append hprefix tailTrace_3726877
  have hstable : (prefixWord ++ tailWord_3726877).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3726877).length < 2 ^ (prefixWord ++ tailWord_3726877).sum := by decide
  have hdescent : baseEnd_3726877 < baseStart_3726877 := by decide
  rcases family_descends (prefixWord ++ tailWord_3726877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3726881 : List Nat := [1, 2, 3, 2, 2, 4, 2, 1, 1, 4]
def baseStart_3726881 : Nat := 118140960795 + 3726881 * 2 ^ 59
def prefixEnd_3726881 : Nat := 4983230072969 + 3 ^ 40 * 3726881 * 2
def baseEnd_3726881 : Nat := 1275787530072758863098595

theorem tailTrace_3726881 : CollatzResearch.WordTrace tailWord_3726881 prefixEnd_3726881 1275787530072758863098595 := by
  unfold tailWord_3726881
  simp only [CollatzResearch.WordTrace]
  refine ⟨135930517211154112445508497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90620344807436074963672331 135930517211154112445508497)
  ·
    refine ⟨101947887908365584334131373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135930517211154112445508497 101947887908365584334131373)
    ·
      refine ⟨38230457965637094125299265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101947887908365584334131373 38230457965637094125299265)
      ·
        refine ⟨28672843474227820593974449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38230457965637094125299265 28672843474227820593974449)
        ·
          refine ⟨21504632605670865445480837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28672843474227820593974449 21504632605670865445480837)
          ·
            refine ⟨4032118613563287271027657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21504632605670865445480837 4032118613563287271027657)
            ·
              refine ⟨3024088960172465453270743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4032118613563287271027657 3024088960172465453270743)
              ·
                refine ⟨4536133440258698179906115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3024088960172465453270743 4536133440258698179906115)
                ·
                  refine ⟨6804200160388047269859173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4536133440258698179906115 6804200160388047269859173)
                  ·
                    refine ⟨1275787530072758863098595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6804200160388047269859173 1275787530072758863098595)
                    ·
                      rfl

theorem cell22_3726881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 4, 2, 1, 1, 4].length) (baseStart_3726881 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3726881 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3726881 prefixEnd_3726881 := by exact prefixLift 3726881
  have htrace : WordTrace (prefixWord ++ tailWord_3726881) baseStart_3726881 baseEnd_3726881 := by
    simpa [prefixWord, tailWord_3726881, baseEnd_3726881] using wordTrace_append hprefix tailTrace_3726881
  have hstable : (prefixWord ++ tailWord_3726881).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3726881).length < 2 ^ (prefixWord ++ tailWord_3726881).sum := by decide
  have hdescent : baseEnd_3726881 < baseStart_3726881 := by decide
  rcases family_descends (prefixWord ++ tailWord_3726881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3726911 : List Nat := [1, 1, 2, 2, 3, 4, 3, 1, 2, 3]
def baseStart_3726911 : Nat := 118140960795 + 3726911 * 2 ^ 59
def prefixEnd_3726911 : Nat := 4983230072969 + 3 ^ 40 * 3726911 * 2
def baseEnd_3726911 : Nat := 1275797799685848784848503

theorem tailTrace_3726911 : CollatzResearch.WordTrace tailWord_3726911 prefixEnd_3726911 1275797799685848784848503 := by
  unfold tailWord_3726911
  simp only [CollatzResearch.WordTrace]
  refine ⟨135931611401045427569100587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90621074267363618379400391 135931611401045427569100587)
  ·
    refine ⟨203897417101568141353650881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135931611401045427569100587 203897417101568141353650881)
    ·
      refine ⟨152923062826176106015238161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 203897417101568141353650881 152923062826176106015238161)
      ·
        refine ⟨114692297119632079511428621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152923062826176106015238161 114692297119632079511428621)
        ·
          refine ⟨43009611419862029816785733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 114692297119632079511428621 43009611419862029816785733)
          ·
            refine ⟨8064302141224130590647325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43009611419862029816785733 8064302141224130590647325)
            ·
              refine ⟨3024113302959048971492747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8064302141224130590647325 3024113302959048971492747)
              ·
                refine ⟨4536169954438573457239121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3024113302959048971492747 4536169954438573457239121)
                ·
                  refine ⟨3402127465828930092929341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4536169954438573457239121 3402127465828930092929341)
                  ·
                    refine ⟨1275797799685848784848503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3402127465828930092929341 1275797799685848784848503)
                    ·
                      rfl

theorem cell22_3726911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 3, 1, 2, 3].length) (baseStart_3726911 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3726911 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3726911 prefixEnd_3726911 := by exact prefixLift 3726911
  have htrace : WordTrace (prefixWord ++ tailWord_3726911) baseStart_3726911 baseEnd_3726911 := by
    simpa [prefixWord, tailWord_3726911, baseEnd_3726911] using wordTrace_append hprefix tailTrace_3726911
  have hstable : (prefixWord ++ tailWord_3726911).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3726911).length < 2 ^ (prefixWord ++ tailWord_3726911).sum := by decide
  have hdescent : baseEnd_3726911 < baseStart_3726911 := by decide
  rcases family_descends (prefixWord ++ tailWord_3726911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3726924 : List Nat := [2, 2, 1, 3, 1, 5, 2, 6]
def baseStart_3726924 : Nat := 118140960795 + 3726924 * 2 ^ 59
def prefixEnd_3726924 : Nat := 4983230072969 + 3 ^ 40 * 3726924 * 2
def baseEnd_3726924 : Nat := 141755805539057898252607

theorem tailTrace_3726924 : CollatzResearch.WordTrace tailWord_3726924 prefixEnd_3726924 141755805539057898252607 := by
  unfold tailWord_3726924
  simp only [CollatzResearch.WordTrace]
  refine ⟨67966042774999165394661913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90621390366665553859549217 67966042774999165394661913)
  ·
    refine ⟨50974532081249374045996435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67966042774999165394661913 50974532081249374045996435)
    ·
      refine ⟨76461798121874061068994653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50974532081249374045996435 76461798121874061068994653)
      ·
        refine ⟨28673174295702772900872995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76461798121874061068994653 28673174295702772900872995)
        ·
          refine ⟨43009761443554159351309493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28673174295702772900872995 43009761443554159351309493)
          ·
            refine ⟨4032165135333202439185265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 43009761443554159351309493 4032165135333202439185265)
            ·
              refine ⟨3024123851499901829388949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4032165135333202439185265 3024123851499901829388949)
              ·
                refine ⟨141755805539057898252607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3024123851499901829388949 141755805539057898252607)
                ·
                  rfl

theorem cell22_3726924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 5, 2, 6].length) (baseStart_3726924 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3726924 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3726924 prefixEnd_3726924 := by exact prefixLift 3726924
  have htrace : WordTrace (prefixWord ++ tailWord_3726924) baseStart_3726924 baseEnd_3726924 := by
    simpa [prefixWord, tailWord_3726924, baseEnd_3726924] using wordTrace_append hprefix tailTrace_3726924
  have hstable : (prefixWord ++ tailWord_3726924).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3726924).length < 2 ^ (prefixWord ++ tailWord_3726924).sum := by decide
  have hdescent : baseEnd_3726924 < baseStart_3726924 := by decide
  rcases family_descends (prefixWord ++ tailWord_3726924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3726941 : List Nat := [1, 4, 4, 2, 1, 2, 8]
def baseStart_3726941 : Nat := 118140960795 + 3726941 * 2 ^ 59
def prefixEnd_3726941 : Nat := 4983230072969 + 3 ^ 40 * 3726941 * 2
def baseEnd_3726941 : Nat := 47252150714775507651793

theorem tailTrace_3726941 : CollatzResearch.WordTrace tailWord_3726941 prefixEnd_3726941 47252150714775507651793 := by
  unfold tailWord_3726941
  simp only [CollatzResearch.WordTrace]
  refine ⟨135932705590936742692692677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90621803727291161795128451 135932705590936742692692677)
  ·
    refine ⟨25487382298300639254879877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 135932705590936742692692677 25487382298300639254879877)
    ·
      refine ⟨4778884180931369860289977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25487382298300639254879877 4778884180931369860289977)
      ·
        refine ⟨3584163135698527395217483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4778884180931369860289977 3584163135698527395217483)
        ·
          refine ⟨5376244703547791092826225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3584163135698527395217483 5376244703547791092826225)
          ·
            refine ⟨4032183527660843319619669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5376244703547791092826225 4032183527660843319619669)
            ·
              refine ⟨47252150714775507651793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4032183527660843319619669 47252150714775507651793)
              ·
                rfl

theorem cell22_3726941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 2, 8].length) (baseStart_3726941 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3726941 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3726941 prefixEnd_3726941 := by exact prefixLift 3726941
  have htrace : WordTrace (prefixWord ++ tailWord_3726941) baseStart_3726941 baseEnd_3726941 := by
    simpa [prefixWord, tailWord_3726941, baseEnd_3726941] using wordTrace_append hprefix tailTrace_3726941
  have hstable : (prefixWord ++ tailWord_3726941).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3726941).length < 2 ^ (prefixWord ++ tailWord_3726941).sum := by decide
  have hdescent : baseEnd_3726941 < baseStart_3726941 := by decide
  rcases family_descends (prefixWord ++ tailWord_3726941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3727007 : List Nat := [1, 1, 2, 7, 1, 2, 2, 2, 1, 3]
def baseStart_3727007 : Nat := 118140960795 + 3727007 * 2 ^ 59
def prefixEnd_3727007 : Nat := 4983230072969 + 3 ^ 40 * 3727007 * 2
def baseEnd_3727007 : Nat := 1275830662447736534448209

theorem tailTrace_3727007 : CollatzResearch.WordTrace tailWord_3727007 prefixEnd_3727007 1275830662447736534448209 := by
  unfold tailWord_3727007
  simp only [CollatzResearch.WordTrace]
  refine ⟨135935112808697635964595275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90623408539131757309730183 135935112808697635964595275)
  ·
    refine ⟨203902669213046453946892913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135935112808697635964595275 203902669213046453946892913)
    ·
      refine ⟨152927001909784840460169685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 203902669213046453946892913 152927001909784840460169685)
      ·
        refine ⟨3584226607260582198285227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 152927001909784840460169685 3584226607260582198285227)
        ·
          refine ⟨5376339910890873297427841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3584226607260582198285227 5376339910890873297427841)
          ·
            refine ⟨4032254933168154973070881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5376339910890873297427841 4032254933168154973070881)
            ·
              refine ⟨3024191199876116229803161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4032254933168154973070881 3024191199876116229803161)
              ·
                refine ⟨2268143399907087172352371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3024191199876116229803161 2268143399907087172352371)
                ·
                  refine ⟨3402215099860630758528557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2268143399907087172352371 3402215099860630758528557)
                  ·
                    refine ⟨1275830662447736534448209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3402215099860630758528557 1275830662447736534448209)
                    ·
                      rfl

theorem cell22_3727007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 2, 2, 2, 1, 3].length) (baseStart_3727007 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3727007 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3727007 prefixEnd_3727007 := by exact prefixLift 3727007
  have htrace : WordTrace (prefixWord ++ tailWord_3727007) baseStart_3727007 baseEnd_3727007 := by
    simpa [prefixWord, tailWord_3727007, baseEnd_3727007] using wordTrace_append hprefix tailTrace_3727007
  have hstable : (prefixWord ++ tailWord_3727007).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3727007).length < 2 ^ (prefixWord ++ tailWord_3727007).sum := by decide
  have hdescent : baseEnd_3727007 < baseStart_3727007 := by decide
  rcases family_descends (prefixWord ++ tailWord_3727007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3727027 : List Nat := [1, 1, 1, 2, 3, 3, 2, 2, 1, 6]
def baseStart_3727027 : Nat := 118140960795 + 3727027 * 2 ^ 59
def prefixEnd_3727027 : Nat := 4983230072969 + 3 ^ 40 * 3727027 * 2
def baseEnd_3727027 : Nat := 1275837508856463148948147

theorem tailTrace_3727027 : CollatzResearch.WordTrace tailWord_3727027 prefixEnd_3727027 1275837508856463148948147 := by
  unfold tailWord_3727027
  simp only [CollatzResearch.WordTrace]
  refine ⟨135935842268625179380323335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90623894845750119586882223 135935842268625179380323335)
  ·
    refine ⟨203903763402937769070485003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135935842268625179380323335 203903763402937769070485003)
    ·
      refine ⟨305855645104406653605727505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203903763402937769070485003 305855645104406653605727505)
      ·
        refine ⟨229391733828304990204295629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 305855645104406653605727505 229391733828304990204295629)
        ·
          refine ⟨86021900185614371326610861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 229391733828304990204295629 86021900185614371326610861)
          ·
            refine ⟨32258212569605389247479073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86021900185614371326610861 32258212569605389247479073)
            ·
              refine ⟨24193659427204041935609305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32258212569605389247479073 24193659427204041935609305)
              ·
                refine ⟨18145244570403031451706979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24193659427204041935609305 18145244570403031451706979)
                ·
                  refine ⟨27217866855604547177560469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18145244570403031451706979 27217866855604547177560469)
                  ·
                    refine ⟨1275837508856463148948147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27217866855604547177560469 1275837508856463148948147)
                    ·
                      rfl

theorem cell22_3727027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 2, 2, 1, 6].length) (baseStart_3727027 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3727027 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3727027 prefixEnd_3727027 := by exact prefixLift 3727027
  have htrace : WordTrace (prefixWord ++ tailWord_3727027) baseStart_3727027 baseEnd_3727027 := by
    simpa [prefixWord, tailWord_3727027, baseEnd_3727027] using wordTrace_append hprefix tailTrace_3727027
  have hstable : (prefixWord ++ tailWord_3727027).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3727027).length < 2 ^ (prefixWord ++ tailWord_3727027).sum := by decide
  have hdescent : baseEnd_3727027 < baseStart_3727027 := by decide
  rcases family_descends (prefixWord ++ tailWord_3727027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3727044 : List Nat := [2, 3, 3, 1, 1, 1, 3, 1, 1, 6]
def baseStart_3727044 : Nat := 118140960795 + 3727044 * 2 ^ 59
def prefixEnd_3727044 : Nat := 4983230072969 + 3 ^ 40 * 3727044 * 2
def baseEnd_3727044 : Nat := 1275843328303880771273095

theorem tailTrace_3727044 : CollatzResearch.WordTrace tailWord_3727044 prefixEnd_3727044 1275843328303880771273095 := by
  unfold tailWord_3727044
  simp only [CollatzResearch.WordTrace]
  refine ⟨67968231154781795641846093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90624308206375727522461457 67968231154781795641846093)
  ·
    refine ⟨25488086683043173365692285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67968231154781795641846093 25488086683043173365692285)
    ·
      refine ⟨9558032506141190012134607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25488086683043173365692285 9558032506141190012134607)
      ·
        refine ⟨14337048759211785018201911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9558032506141190012134607 14337048759211785018201911)
        ·
          refine ⟨21505573138817677527302867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14337048759211785018201911 21505573138817677527302867)
          ·
            refine ⟨32258359708226516290954301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21505573138817677527302867 32258359708226516290954301)
            ·
              refine ⟨12096884890584943609107863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32258359708226516290954301 12096884890584943609107863)
              ·
                refine ⟨18145327335877415413661795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12096884890584943609107863 18145327335877415413661795)
                ·
                  refine ⟨27217991003816123120492693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18145327335877415413661795 27217991003816123120492693)
                  ·
                    refine ⟨1275843328303880771273095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27217991003816123120492693 1275843328303880771273095)
                    ·
                      rfl

theorem cell22_3727044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 3, 1, 1, 6].length) (baseStart_3727044 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3727044 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3727044 prefixEnd_3727044 := by exact prefixLift 3727044
  have htrace : WordTrace (prefixWord ++ tailWord_3727044) baseStart_3727044 baseEnd_3727044 := by
    simpa [prefixWord, tailWord_3727044, baseEnd_3727044] using wordTrace_append hprefix tailTrace_3727044
  have hstable : (prefixWord ++ tailWord_3727044).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3727044).length < 2 ^ (prefixWord ++ tailWord_3727044).sum := by decide
  have hdescent : baseEnd_3727044 < baseStart_3727044 := by decide
  rcases family_descends (prefixWord ++ tailWord_3727044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3727050 : List Nat := [3, 1, 2, 1, 6, 1, 2, 1, 1, 4]
def baseStart_3727050 : Nat := 118140960795 + 3727050 * 2 ^ 59
def prefixEnd_3727050 : Nat := 4983230072969 + 3 ^ 40 * 3727050 * 2
def baseEnd_3727050 : Nat := 1275845382226498755623077

theorem tailTrace_3727050 : CollatzResearch.WordTrace tailWord_3727050 prefixEnd_3727050 1275845382226498755623077 := by
  unfold tailWord_3727050
  simp only [CollatzResearch.WordTrace]
  refine ⟨33984170286885463577102651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90624454098361236205607069 33984170286885463577102651)
  ·
    refine ⟨50976255430328195365653977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33984170286885463577102651 50976255430328195365653977)
    ·
      refine ⟨38232191572746146524240483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50976255430328195365653977 38232191572746146524240483)
      ·
        refine ⟨57348287359119219786360725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38232191572746146524240483 57348287359119219786360725)
        ·
          refine ⟨2688200969958713427485659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 57348287359119219786360725 2688200969958713427485659)
          ·
            refine ⟨4032301454938070141228489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2688200969958713427485659 4032301454938070141228489)
            ·
              refine ⟨3024226091203552605921367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4032301454938070141228489 3024226091203552605921367)
              ·
                refine ⟨4536339136805328908882051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3024226091203552605921367 4536339136805328908882051)
                ·
                  refine ⟨6804508705207993363323077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4536339136805328908882051 6804508705207993363323077)
                  ·
                    refine ⟨1275845382226498755623077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6804508705207993363323077 1275845382226498755623077)
                    ·
                      rfl

theorem cell22_3727050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 6, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 6, 1, 2, 1, 1, 4].length) (baseStart_3727050 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3727050 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3727050 prefixEnd_3727050 := by exact prefixLift 3727050
  have htrace : WordTrace (prefixWord ++ tailWord_3727050) baseStart_3727050 baseEnd_3727050 := by
    simpa [prefixWord, tailWord_3727050, baseEnd_3727050] using wordTrace_append hprefix tailTrace_3727050
  have hstable : (prefixWord ++ tailWord_3727050).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3727050).length < 2 ^ (prefixWord ++ tailWord_3727050).sum := by decide
  have hdescent : baseEnd_3727050 < baseStart_3727050 := by decide
  rcases family_descends (prefixWord ++ tailWord_3727050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3727072 : List Nat := [2, 1, 1, 3, 1, 2, 2, 1, 1, 8]
def baseStart_3727072 : Nat := 118140960795 + 3727072 * 2 ^ 59
def prefixEnd_3727072 : Nat := 4983230072969 + 3 ^ 40 * 3727072 * 2
def baseEnd_3727072 : Nat := 1275852913276098031573009

theorem tailTrace_3727072 : CollatzResearch.WordTrace tailWord_3727072 prefixEnd_3727072 1275852913276098031573009 := by
  unfold tailWord_3727072
  simp only [CollatzResearch.WordTrace]
  refine ⟨67968741776731076032855735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90624989035641434710474313 67968741776731076032855735)
  ·
    refine ⟨101953112665096614049283603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67968741776731076032855735 101953112665096614049283603)
    ·
      refine ⟨152929668997644921073925405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101953112665096614049283603 152929668997644921073925405)
      ·
        refine ⟨57348625874116845402722027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 152929668997644921073925405 57348625874116845402722027)
        ·
          refine ⟨86022938811175268104083041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57348625874116845402722027 86022938811175268104083041)
          ·
            refine ⟨64517204108381451078062281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86022938811175268104083041 64517204108381451078062281)
            ·
              refine ⟨48387903081286088308546711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64517204108381451078062281 48387903081286088308546711)
              ·
                refine ⟨72581854621929132462820067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48387903081286088308546711 72581854621929132462820067)
                ·
                  refine ⟨108872781932893698694230101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 72581854621929132462820067 108872781932893698694230101)
                  ·
                    refine ⟨1275852913276098031573009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 108872781932893698694230101 1275852913276098031573009)
                    ·
                      rfl

theorem cell22_3727072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 1, 1, 8].length) (baseStart_3727072 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3727072 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3727072 prefixEnd_3727072 := by exact prefixLift 3727072
  have htrace : WordTrace (prefixWord ++ tailWord_3727072) baseStart_3727072 baseEnd_3727072 := by
    simpa [prefixWord, tailWord_3727072, baseEnd_3727072] using wordTrace_append hprefix tailTrace_3727072
  have hstable : (prefixWord ++ tailWord_3727072).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3727072).length < 2 ^ (prefixWord ++ tailWord_3727072).sum := by decide
  have hdescent : baseEnd_3727072 < baseStart_3727072 := by decide
  rcases family_descends (prefixWord ++ tailWord_3727072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3727125 : List Nat := [1, 3, 2, 1, 2, 4, 3, 2, 1, 3]
def baseStart_3727125 : Nat := 118140960795 + 3727125 * 2 ^ 59
def prefixEnd_3727125 : Nat := 4983230072969 + 3 ^ 40 * 3727125 * 2
def baseEnd_3727125 : Nat := 1275871056259223559997847

theorem tailTrace_3727125 : CollatzResearch.WordTrace tailWord_3727125 prefixEnd_3727125 1275871056259223559997847 := by
  unfold tailWord_3727125
  simp only [CollatzResearch.WordTrace]
  refine ⟨135939416622270142117390829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90626277748180094744927219 135939416622270142117390829)
  ·
    refine ⟨50977281233351303294021561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135939416622270142117390829 50977281233351303294021561)
    ·
      refine ⟨38232960925013477470516171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50977281233351303294021561 38232960925013477470516171)
      ·
        refine ⟨57349441387520216205774257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38232960925013477470516171 57349441387520216205774257)
        ·
          refine ⟨43012081040640162154330693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57349441387520216205774257 43012081040640162154330693)
          ·
            refine ⟨8064765195120030403937005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43012081040640162154330693 8064765195120030403937005)
            ·
              refine ⟨3024286948170011401476377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8064765195120030403937005 3024286948170011401476377)
              ·
                refine ⟨2268215211127508551107283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3024286948170011401476377 2268215211127508551107283)
                ·
                  refine ⟨3402322816691262826660925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2268215211127508551107283 3402322816691262826660925)
                  ·
                    refine ⟨1275871056259223559997847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3402322816691262826660925 1275871056259223559997847)
                    ·
                      rfl

theorem cell22_3727125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 3, 2, 1, 3].length) (baseStart_3727125 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3727125 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3727125 prefixEnd_3727125 := by exact prefixLift 3727125
  have htrace : WordTrace (prefixWord ++ tailWord_3727125) baseStart_3727125 baseEnd_3727125 := by
    simpa [prefixWord, tailWord_3727125, baseEnd_3727125] using wordTrace_append hprefix tailTrace_3727125
  have hstable : (prefixWord ++ tailWord_3727125).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3727125).length < 2 ^ (prefixWord ++ tailWord_3727125).sum := by decide
  have hdescent : baseEnd_3727125 < baseStart_3727125 := by decide
  rcases family_descends (prefixWord ++ tailWord_3727125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3727164 : List Nat := [2, 2, 2, 2, 1, 1, 3, 1, 3, 5]
def baseStart_3727164 : Nat := 118140960795 + 3727164 * 2 ^ 59
def prefixEnd_3727164 : Nat := 4983230072969 + 3 ^ 40 * 3727164 * 2
def baseEnd_3727164 : Nat := 1275884406756240458272727

theorem tailTrace_3727164 : CollatzResearch.WordTrace tailWord_3727164 prefixEnd_3727164 1275884406756240458272727 := by
  unfold tailWord_3727164
  simp only [CollatzResearch.WordTrace]
  refine ⟨67970419534564425889030273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90627226046085901185373697 67970419534564425889030273)
  ·
    refine ⟨50977814650923319416772705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67970419534564425889030273 50977814650923319416772705)
    ·
      refine ⟨38233360988192489562579529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50977814650923319416772705 38233360988192489562579529)
      ·
        refine ⟨28675020741144367171934647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38233360988192489562579529 28675020741144367171934647)
        ·
          refine ⟨43012531111716550757901971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28675020741144367171934647 43012531111716550757901971)
          ·
            refine ⟨64518796667574826136852957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43012531111716550757901971 64518796667574826136852957)
            ·
              refine ⟨24194548750340559801319859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64518796667574826136852957 24194548750340559801319859)
              ·
                refine ⟨36291823125510839701979789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24194548750340559801319859 36291823125510839701979789)
                ·
                  refine ⟨13609433672066564888242421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36291823125510839701979789 13609433672066564888242421)
                  ·
                    refine ⟨1275884406756240458272727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13609433672066564888242421 1275884406756240458272727)
                    ·
                      rfl

theorem cell22_3727164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 3, 1, 3, 5].length) (baseStart_3727164 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3727164 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3727164 prefixEnd_3727164 := by exact prefixLift 3727164
  have htrace : WordTrace (prefixWord ++ tailWord_3727164) baseStart_3727164 baseEnd_3727164 := by
    simpa [prefixWord, tailWord_3727164, baseEnd_3727164] using wordTrace_append hprefix tailTrace_3727164
  have hstable : (prefixWord ++ tailWord_3727164).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3727164).length < 2 ^ (prefixWord ++ tailWord_3727164).sum := by decide
  have hdescent : baseEnd_3727164 < baseStart_3727164 := by decide
  rcases family_descends (prefixWord ++ tailWord_3727164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3727262 : List Nat := [4, 3, 1, 3, 1, 2, 2, 6]
def baseStart_3727262 : Nat := 118140960795 + 3727262 * 2 ^ 59
def prefixEnd_3727262 : Nat := 4983230072969 + 3 ^ 40 * 3727262 * 2
def baseEnd_3727262 : Nat := 141768661573222318813603

theorem tailTrace_3727262 : CollatzResearch.WordTrace tailWord_3727262 prefixEnd_3727262 141768661573222318813603 := by
  unfold tailWord_3727262
  simp only [CollatzResearch.WordTrace]
  refine ⟨16993051677846726814391005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 90629608948515876343418693 16993051677846726814391005)
  ·
    refine ⟨6372394379192522555396627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16993051677846726814391005 6372394379192522555396627)
    ·
      refine ⟨9558591568788783833094941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6372394379192522555396627 9558591568788783833094941)
      ·
        refine ⟨3584471838295793937410603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9558591568788783833094941 3584471838295793937410603)
        ·
          refine ⟨5376707757443690906115905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3584471838295793937410603 5376707757443690906115905)
          ·
            refine ⟨4032530818082768179586929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5376707757443690906115905 4032530818082768179586929)
            ·
              refine ⟨3024398113562076134690197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4032530818082768179586929 3024398113562076134690197)
              ·
                refine ⟨141768661573222318813603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3024398113562076134690197 141768661573222318813603)
                ·
                  rfl

theorem cell22_3727262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 2, 2, 6].length) (baseStart_3727262 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3727262 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3727262 prefixEnd_3727262 := by exact prefixLift 3727262
  have htrace : WordTrace (prefixWord ++ tailWord_3727262) baseStart_3727262 baseEnd_3727262 := by
    simpa [prefixWord, tailWord_3727262, baseEnd_3727262] using wordTrace_append hprefix tailTrace_3727262
  have hstable : (prefixWord ++ tailWord_3727262).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3727262).length < 2 ^ (prefixWord ++ tailWord_3727262).sum := by decide
  have hdescent : baseEnd_3727262 < baseStart_3727262 := by decide
  rcases family_descends (prefixWord ++ tailWord_3727262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3727269 : List Nat := [1, 3, 1, 2, 1, 1, 1, 2, 2, 8]
def baseStart_3727269 : Nat := 118140960795 + 3727269 * 2 ^ 59
def prefixEnd_3727269 : Nat := 4983230072969 + 3 ^ 40 * 3727269 * 2
def baseEnd_3727269 : Nat := 1275920350402055184397405

theorem tailTrace_3727269 : CollatzResearch.WordTrace tailWord_3727269 prefixEnd_3727269 1275920350402055184397405 := by
  unfold tailWord_3727269
  simp only [CollatzResearch.WordTrace]
  refine ⟨135944668733748454710632861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90629779155832303140421907 135944668733748454710632861)
  ·
    refine ⟨50979250775155670516487323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135944668733748454710632861 50979250775155670516487323)
    ·
      refine ⟨76468876162733505774730985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50979250775155670516487323 76468876162733505774730985)
      ·
        refine ⟨57351657122050129331048239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76468876162733505774730985 57351657122050129331048239)
        ·
          refine ⟨86027485683075193996572359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57351657122050129331048239 86027485683075193996572359)
          ·
            refine ⟨129041228524612790994858539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86027485683075193996572359 129041228524612790994858539)
            ·
              refine ⟨193561842786919186492287809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129041228524612790994858539 193561842786919186492287809)
              ·
                refine ⟨145171382090189389869215857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 193561842786919186492287809 145171382090189389869215857)
                ·
                  refine ⟨108878536567642042401911893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 145171382090189389869215857 108878536567642042401911893)
                  ·
                    refine ⟨1275920350402055184397405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 108878536567642042401911893 1275920350402055184397405)
                    ·
                      rfl

theorem cell22_3727269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 2, 2, 8].length) (baseStart_3727269 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3727269 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3727269 prefixEnd_3727269 := by exact prefixLift 3727269
  have htrace : WordTrace (prefixWord ++ tailWord_3727269) baseStart_3727269 baseEnd_3727269 := by
    simpa [prefixWord, tailWord_3727269, baseEnd_3727269] using wordTrace_append hprefix tailTrace_3727269
  have hstable : (prefixWord ++ tailWord_3727269).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3727269).length < 2 ^ (prefixWord ++ tailWord_3727269).sum := by decide
  have hdescent : baseEnd_3727269 < baseStart_3727269 := by decide
  rcases family_descends (prefixWord ++ tailWord_3727269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3727299 : List Nat := [1, 1, 1, 3, 1, 1, 2, 1, 2, 9]
def baseStart_3727299 : Nat := 118140960795 + 3727299 * 2 ^ 59
def prefixEnd_3727299 : Nat := 4983230072969 + 3 ^ 40 * 3727299 * 2
def baseEnd_3727299 : Nat := 1275930620015145106147313

theorem tailTrace_3727299 : CollatzResearch.WordTrace tailWord_3727299 prefixEnd_3727299 1275930620015145106147313 := by
  unfold tailWord_3727299
  simp only [CollatzResearch.WordTrace]
  refine ⟨135945762923639769834224951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90630508615759846556149967 135945762923639769834224951)
  ·
    refine ⟨203918644385459654751337427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135945762923639769834224951 203918644385459654751337427)
    ·
      refine ⟨305877966578189482127006141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203918644385459654751337427 305877966578189482127006141)
      ·
        refine ⟨114704237466821055797627303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 305877966578189482127006141 114704237466821055797627303)
        ·
          refine ⟨172056356200231583696440955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114704237466821055797627303 172056356200231583696440955)
          ·
            refine ⟨258084534300347375544661433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 172056356200231583696440955 258084534300347375544661433)
            ·
              refine ⟨193563400725260531658496075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 258084534300347375544661433 193563400725260531658496075)
              ·
                refine ⟨290345101087890797487744113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 193563400725260531658496075 290345101087890797487744113)
                ·
                  refine ⟨217758825815918098115808085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 290345101087890797487744113 217758825815918098115808085)
                  ·
                    refine ⟨1275930620015145106147313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 217758825815918098115808085 1275930620015145106147313)
                    ·
                      rfl

theorem cell22_3727299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 1, 2, 9].length) (baseStart_3727299 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3727299 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3727299 prefixEnd_3727299 := by exact prefixLift 3727299
  have htrace : WordTrace (prefixWord ++ tailWord_3727299) baseStart_3727299 baseEnd_3727299 := by
    simpa [prefixWord, tailWord_3727299, baseEnd_3727299] using wordTrace_append hprefix tailTrace_3727299
  have hstable : (prefixWord ++ tailWord_3727299).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3727299).length < 2 ^ (prefixWord ++ tailWord_3727299).sum := by decide
  have hdescent : baseEnd_3727299 < baseStart_3727299 := by decide
  rcases family_descends (prefixWord ++ tailWord_3727299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
