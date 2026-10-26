import V185TrunkScan22Chunk379

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_3389169 : List Nat := [1, 2, 2, 2, 2, 4, 2, 2, 1, 4]
def baseStart_3389169 : Nat := 118140960795 + 3389169 * 2 ^ 59
def prefixEnd_3389169 : Nat := 4983230072969 + 3 ^ 40 * 3389169 * 2
def baseEnd_3389169 : Nat := 1160181810878637062934001

theorem tailTrace_3389169 : CollatzResearch.WordTrace tailWord_3389169 prefixEnd_3389169 1160181810878637062934001 := by
  unfold tailWord_3389169
  simp only [CollatzResearch.WordTrace]
  refine ⟨123613148658627011827778561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82408765772418007885185707 123613148658627011827778561)
  ·
    refine ⟨92709861493970258870833921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123613148658627011827778561 92709861493970258870833921)
    ·
      refine ⟨69532396120477694153125441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92709861493970258870833921 69532396120477694153125441)
      ·
        refine ⟨52149297090358270614844081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69532396120477694153125441 52149297090358270614844081)
        ·
          refine ⟨39111972817768702961133061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52149297090358270614844081 39111972817768702961133061)
          ·
            refine ⟨7333494903331631805212449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39111972817768702961133061 7333494903331631805212449)
            ·
              refine ⟨5500121177498723853909337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7333494903331631805212449 5500121177498723853909337)
              ·
                refine ⟨4125090883124042890432003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5500121177498723853909337 4125090883124042890432003)
                ·
                  refine ⟨6187636324686064335648005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4125090883124042890432003 6187636324686064335648005)
                  ·
                    refine ⟨1160181810878637062934001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6187636324686064335648005 1160181810878637062934001)
                    ·
                      rfl

theorem cell22_3389169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 2, 2, 1, 4].length) (baseStart_3389169 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3389169 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3389169 prefixEnd_3389169 := by exact prefixLift 3389169
  have htrace : WordTrace (prefixWord ++ tailWord_3389169) baseStart_3389169 baseEnd_3389169 := by
    simpa [prefixWord, tailWord_3389169, baseEnd_3389169] using wordTrace_append hprefix tailTrace_3389169
  have hstable : (prefixWord ++ tailWord_3389169).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3389169).length < 2 ^ (prefixWord ++ tailWord_3389169).sum := by decide
  have hdescent : baseEnd_3389169 < baseStart_3389169 := by decide
  rcases family_descends (prefixWord ++ tailWord_3389169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3389195 : List Nat := [1, 1, 1, 1, 5, 1, 12]
def baseStart_3389195 : Nat := 118140960795 + 3389195 * 2 ^ 59
def prefixEnd_3389195 : Nat := 4983230072969 + 3 ^ 40 * 3389195 * 2
def baseEnd_3389195 : Nat := 42970026341110431917923

theorem tailTrace_3389195 : CollatzResearch.WordTrace tailWord_3389195 prefixEnd_3389195 42970026341110431917923 := by
  unfold tailWord_3389195
  simp only [CollatzResearch.WordTrace]
  refine ⟨123614096956532818268225039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82409397971021878845483359 123614096956532818268225039)
  ·
    refine ⟨185421145434799227402337559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123614096956532818268225039 185421145434799227402337559)
    ·
      refine ⟨278131718152198841103506339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185421145434799227402337559 278131718152198841103506339)
      ·
        refine ⟨417197577228298261655259509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 278131718152198841103506339 417197577228298261655259509)
        ·
          refine ⟨39112272865152962030180579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 417197577228298261655259509 39112272865152962030180579)
          ·
            refine ⟨58668409297729443045270869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39112272865152962030180579 58668409297729443045270869)
            ·
              refine ⟨42970026341110431917923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 58668409297729443045270869 42970026341110431917923)
              ·
                rfl

theorem cell22_3389195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 12].length) (baseStart_3389195 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3389195 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3389195 prefixEnd_3389195 := by exact prefixLift 3389195
  have htrace : WordTrace (prefixWord ++ tailWord_3389195) baseStart_3389195 baseEnd_3389195 := by
    simpa [prefixWord, tailWord_3389195, baseEnd_3389195] using wordTrace_append hprefix tailTrace_3389195
  have hstable : (prefixWord ++ tailWord_3389195).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3389195).length < 2 ^ (prefixWord ++ tailWord_3389195).sum := by decide
  have hdescent : baseEnd_3389195 < baseStart_3389195 := by decide
  rcases family_descends (prefixWord ++ tailWord_3389195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3389212 : List Nat := [2, 2, 3, 1, 1, 2, 4, 7]
def baseStart_3389212 : Nat := 118140960795 + 3389212 * 2 ^ 59
def prefixEnd_3389212 : Nat := 4983230072969 + 3 ^ 40 * 3389212 * 2
def baseEnd_3389212 : Nat := 128910725628599920456541

theorem tailTrace_3389212 : CollatzResearch.WordTrace tailWord_3389212 prefixEnd_3389212 128910725628599920456541 := by
  unfold tailWord_3389212
  simp only [CollatzResearch.WordTrace]
  refine ⟨61807358498735615085796945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82409811331647486781062593 61807358498735615085796945)
  ·
    refine ⟨46355518874051711314347709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61807358498735615085796945 46355518874051711314347709)
    ·
      refine ⟨17383319577769391742880391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46355518874051711314347709 17383319577769391742880391)
      ·
        refine ⟨26074979366654087614320587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17383319577769391742880391 26074979366654087614320587)
        ·
          refine ⟨39112469049981131421480881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26074979366654087614320587 39112469049981131421480881)
          ·
            refine ⟨29334351787485848566110661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39112469049981131421480881 29334351787485848566110661)
            ·
              refine ⟨5500190960153596606145749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29334351787485848566110661 5500190960153596606145749)
              ·
                refine ⟨128910725628599920456541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5500190960153596606145749 128910725628599920456541)
                ·
                  rfl

theorem cell22_3389212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 4, 7].length) (baseStart_3389212 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3389212 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3389212 prefixEnd_3389212 := by exact prefixLift 3389212
  have htrace : WordTrace (prefixWord ++ tailWord_3389212) baseStart_3389212 baseEnd_3389212 := by
    simpa [prefixWord, tailWord_3389212, baseEnd_3389212] using wordTrace_append hprefix tailTrace_3389212
  have hstable : (prefixWord ++ tailWord_3389212).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3389212).length < 2 ^ (prefixWord ++ tailWord_3389212).sum := by decide
  have hdescent : baseEnd_3389212 < baseStart_3389212 := by decide
  rcases family_descends (prefixWord ++ tailWord_3389212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3389351 : List Nat := [1, 1, 6, 1, 2, 1, 1, 2, 4, 3]
def baseStart_3389351 : Nat := 118140960795 + 3389351 * 2 ^ 59
def prefixEnd_3389351 : Nat := 4983230072969 + 3 ^ 40 * 3389351 * 2
def baseEnd_3389351 : Nat := 1160244113198049254883443

theorem tailTrace_3389351 : CollatzResearch.WordTrace tailWord_3389351 prefixEnd_3389351 1160244113198049254883443 := by
  unfold tailWord_3389351
  simp only [CollatzResearch.WordTrace]
  refine ⟨123619786743967656910903907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82413191162645104607269271 123619786743967656910903907)
  ·
    refine ⟨185429680115951485366355861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123619786743967656910903907 185429680115951485366355861)
    ·
      refine ⟨8692016255435225876547931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 185429680115951485366355861 8692016255435225876547931)
      ·
        refine ⟨13038024383152838814821897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8692016255435225876547931 13038024383152838814821897)
        ·
          refine ⟨9778518287364629111116423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13038024383152838814821897 9778518287364629111116423)
          ·
            refine ⟨14667777431046943666674635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9778518287364629111116423 14667777431046943666674635)
            ·
              refine ⟨22001666146570415500011953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14667777431046943666674635 22001666146570415500011953)
              ·
                refine ⟨16501249609927811625008965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22001666146570415500011953 16501249609927811625008965)
                ·
                  refine ⟨3093984301861464679689181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16501249609927811625008965 3093984301861464679689181)
                  ·
                    refine ⟨1160244113198049254883443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3093984301861464679689181 1160244113198049254883443)
                    ·
                      rfl

theorem cell22_3389351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 1, 2, 4, 3].length) (baseStart_3389351 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3389351 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3389351 prefixEnd_3389351 := by exact prefixLift 3389351
  have htrace : WordTrace (prefixWord ++ tailWord_3389351) baseStart_3389351 baseEnd_3389351 := by
    simpa [prefixWord, tailWord_3389351, baseEnd_3389351] using wordTrace_append hprefix tailTrace_3389351
  have hstable : (prefixWord ++ tailWord_3389351).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3389351).length < 2 ^ (prefixWord ++ tailWord_3389351).sum := by decide
  have hdescent : baseEnd_3389351 < baseStart_3389351 := by decide
  rcases family_descends (prefixWord ++ tailWord_3389351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3389396 : List Nat := [2, 4, 1, 2, 1, 1, 2, 1, 5, 3]
def baseStart_3389396 : Nat := 118140960795 + 3389396 * 2 ^ 59
def prefixEnd_3389396 : Nat := 4983230072969 + 3 ^ 40 * 3389396 * 2
def baseEnd_3389396 : Nat := 1160259517617684137508305

theorem tailTrace_3389396 : CollatzResearch.WordTrace tailWord_3389396 prefixEnd_3389396 1160259517617684137508305 := by
  unfold tailWord_3389396
  simp only [CollatzResearch.WordTrace]
  refine ⟨61810714014402314798146021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82414285352536419730861361 61810714014402314798146021)
  ·
    refine ⟨11589508877700434024652379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 61810714014402314798146021 11589508877700434024652379)
    ·
      refine ⟨17384263316550651036978569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11589508877700434024652379 17384263316550651036978569)
      ·
        refine ⟨13038197487412988277733927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17384263316550651036978569 13038197487412988277733927)
        ·
          refine ⟨19557296231119482416600891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13038197487412988277733927 19557296231119482416600891)
          ·
            refine ⟨29335944346679223624901337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19557296231119482416600891 29335944346679223624901337)
            ·
              refine ⟨22001958260009417718676003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29335944346679223624901337 22001958260009417718676003)
              ·
                refine ⟨33002937390014126578014005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22001958260009417718676003 33002937390014126578014005)
                ·
                  refine ⟨3094025380313824366688813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 33002937390014126578014005 3094025380313824366688813)
                  ·
                    refine ⟨1160259517617684137508305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3094025380313824366688813 1160259517617684137508305)
                    ·
                      rfl

theorem cell22_3389396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 2, 1, 5, 3].length) (baseStart_3389396 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3389396 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3389396 prefixEnd_3389396 := by exact prefixLift 3389396
  have htrace : WordTrace (prefixWord ++ tailWord_3389396) baseStart_3389396 baseEnd_3389396 := by
    simpa [prefixWord, tailWord_3389396, baseEnd_3389396] using wordTrace_append hprefix tailTrace_3389396
  have hstable : (prefixWord ++ tailWord_3389396).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3389396).length < 2 ^ (prefixWord ++ tailWord_3389396).sum := by decide
  have hdescent : baseEnd_3389396 < baseStart_3389396 := by decide
  rcases family_descends (prefixWord ++ tailWord_3389396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3389473 : List Nat := [1, 2, 3, 2, 4, 1, 1, 3, 1, 4]
def baseStart_3389473 : Nat := 118140960795 + 3389473 * 2 ^ 59
def prefixEnd_3389473 : Nat := 4983230072969 + 3 ^ 40 * 3389473 * 2
def baseEnd_3389473 : Nat := 1160285876291281603333069

theorem tailTrace_3389473 : CollatzResearch.WordTrace tailWord_3389473 prefixEnd_3389473 1160285876291281603333069 := by
  unfold tailWord_3389473
  simp only [CollatzResearch.WordTrace]
  refine ⟨123624236449525671746845073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82416157633017114497896715 123624236449525671746845073)
  ·
    refine ⟨92718177337144253810133805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123624236449525671746845073 92718177337144253810133805)
    ·
      refine ⟨34769316501429095178800177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92718177337144253810133805 34769316501429095178800177)
      ·
        refine ⟨26076987376071821384100133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34769316501429095178800177 26076987376071821384100133)
        ·
          refine ⟨4889435133013466509518775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26076987376071821384100133 4889435133013466509518775)
          ·
            refine ⟨7334152699520199764278163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4889435133013466509518775 7334152699520199764278163)
            ·
              refine ⟨11001229049280299646417245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7334152699520199764278163 11001229049280299646417245)
              ·
                refine ⟨4125460893480112367406467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11001229049280299646417245 4125460893480112367406467)
                ·
                  refine ⟨6188191340220168551109701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4125460893480112367406467 6188191340220168551109701)
                  ·
                    refine ⟨1160285876291281603333069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6188191340220168551109701 1160285876291281603333069)
                    ·
                      rfl

theorem cell22_3389473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 1, 3, 1, 4].length) (baseStart_3389473 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3389473 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3389473 prefixEnd_3389473 := by exact prefixLift 3389473
  have htrace : WordTrace (prefixWord ++ tailWord_3389473) baseStart_3389473 baseEnd_3389473 := by
    simpa [prefixWord, tailWord_3389473, baseEnd_3389473] using wordTrace_append hprefix tailTrace_3389473
  have hstable : (prefixWord ++ tailWord_3389473).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3389473).length < 2 ^ (prefixWord ++ tailWord_3389473).sum := by decide
  have hdescent : baseEnd_3389473 < baseStart_3389473 := by decide
  rcases family_descends (prefixWord ++ tailWord_3389473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3389514 : List Nat := [3, 1, 2, 1, 1, 2, 1, 1, 1, 9]
def baseStart_3389514 : Nat := 118140960795 + 3389514 * 2 ^ 59
def prefixEnd_3389514 : Nat := 4983230072969 + 3 ^ 40 * 3389514 * 2
def baseEnd_3389514 : Nat := 1160299911429171163057943

theorem tailTrace_3389514 : CollatzResearch.WordTrace tailWord_3389514 prefixEnd_3389514 1160299911429171163057943 := by
  unfold tailWord_3389514
  simp only [CollatzResearch.WordTrace]
  refine ⟨30906432960594283937271899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82417154561584757166058397 30906432960594283937271899)
  ·
    refine ⟨46359649440891425905907849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30906432960594283937271899 46359649440891425905907849)
    ·
      refine ⟨34769737080668569429430887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46359649440891425905907849 34769737080668569429430887)
      ·
        refine ⟨52154605621002854144146331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34769737080668569429430887 52154605621002854144146331)
        ·
          refine ⟨78231908431504281216219497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52154605621002854144146331 78231908431504281216219497)
          ·
            refine ⟨58673931323628210912164623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78231908431504281216219497 58673931323628210912164623)
            ·
              refine ⟨88010896985442316368246935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58673931323628210912164623 88010896985442316368246935)
              ·
                refine ⟨132016345478163474552370403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88010896985442316368246935 132016345478163474552370403)
                ·
                  refine ⟨198024518217245211828555605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 132016345478163474552370403 198024518217245211828555605)
                  ·
                    refine ⟨1160299911429171163057943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 198024518217245211828555605 1160299911429171163057943)
                    ·
                      rfl

theorem cell22_3389514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 1, 1, 9].length) (baseStart_3389514 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3389514 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3389514 prefixEnd_3389514 := by exact prefixLift 3389514
  have htrace : WordTrace (prefixWord ++ tailWord_3389514) baseStart_3389514 baseEnd_3389514 := by
    simpa [prefixWord, tailWord_3389514, baseEnd_3389514] using wordTrace_append hprefix tailTrace_3389514
  have hstable : (prefixWord ++ tailWord_3389514).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3389514).length < 2 ^ (prefixWord ++ tailWord_3389514).sum := by decide
  have hdescent : baseEnd_3389514 < baseStart_3389514 := by decide
  rcases family_descends (prefixWord ++ tailWord_3389514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3389516 : List Nat := [2, 2, 1, 3, 1, 1, 6, 6]
def baseStart_3389516 : Nat := 118140960795 + 3389516 * 2 ^ 59
def prefixEnd_3389516 : Nat := 4983230072969 + 3 ^ 40 * 3389516 * 2
def baseEnd_3389516 : Nat := 128922288452227091611993

theorem tailTrace_3389516 : CollatzResearch.WordTrace tailWord_3389516 prefixEnd_3389516 128922288452227091611993 := by
  unfold tailWord_3389516
  simp only [CollatzResearch.WordTrace]
  refine ⟨61812902394184945045330201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82417203192246593393773601 61812902394184945045330201)
  ·
    refine ⟨46359676795638708783997651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61812902394184945045330201 46359676795638708783997651)
    ·
      refine ⟨69539515193458063175996477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46359676795638708783997651 69539515193458063175996477)
      ·
        refine ⟨26077318197546773690998679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69539515193458063175996477 26077318197546773690998679)
        ·
          refine ⟨39115977296320160536498019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26077318197546773690998679 39115977296320160536498019)
          ·
            refine ⟨58673965944480240804747029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39115977296320160536498019 58673965944480240804747029)
            ·
              refine ⟨2750342153647511287722517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 58673965944480240804747029 2750342153647511287722517)
              ·
                refine ⟨128922288452227091611993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2750342153647511287722517 128922288452227091611993)
                ·
                  rfl

theorem cell22_3389516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 6, 6].length) (baseStart_3389516 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3389516 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3389516 prefixEnd_3389516 := by exact prefixLift 3389516
  have htrace : WordTrace (prefixWord ++ tailWord_3389516) baseStart_3389516 baseEnd_3389516 := by
    simpa [prefixWord, tailWord_3389516, baseEnd_3389516] using wordTrace_append hprefix tailTrace_3389516
  have hstable : (prefixWord ++ tailWord_3389516).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3389516).length < 2 ^ (prefixWord ++ tailWord_3389516).sum := by decide
  have hdescent : baseEnd_3389516 < baseStart_3389516 := by decide
  rcases family_descends (prefixWord ++ tailWord_3389516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3389522 : List Nat := [3, 2, 2, 1, 5, 1, 1, 3, 4]
def baseStart_3389522 : Nat := 118140960795 + 3389522 * 2 ^ 59
def prefixEnd_3389522 : Nat := 4983230072969 + 3 ^ 40 * 3389522 * 2
def baseEnd_3389522 : Nat := 386767549997553936285973

theorem tailTrace_3389522 : CollatzResearch.WordTrace tailWord_3389522 prefixEnd_3389522 386767549997553936285973 := by
  unfold tailWord_3389522
  simp only [CollatzResearch.WordTrace]
  refine ⟨30906505906587038278844705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82417349084232102076919213 30906505906587038278844705)
  ·
    refine ⟨23179879429940278709133529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30906505906587038278844705 23179879429940278709133529)
    ·
      refine ⟨17384909572455209031850147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23179879429940278709133529 17384909572455209031850147)
      ·
        refine ⟨26077364358682813547775221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17384909572455209031850147 26077364358682813547775221)
        ·
          refine ⟨2444752908626513770103927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 26077364358682813547775221 2444752908626513770103927)
          ·
            refine ⟨3667129362939770655155891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2444752908626513770103927 3667129362939770655155891)
            ·
              refine ⟨5500694044409655982733837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3667129362939770655155891 5500694044409655982733837)
              ·
                refine ⟨2062760266653620993525189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5500694044409655982733837 2062760266653620993525189)
                ·
                  refine ⟨386767549997553936285973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2062760266653620993525189 386767549997553936285973)
                  ·
                    rfl

theorem cell22_3389522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 5, 1, 1, 3, 4].length) (baseStart_3389522 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3389522 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3389522 prefixEnd_3389522 := by exact prefixLift 3389522
  have htrace : WordTrace (prefixWord ++ tailWord_3389522) baseStart_3389522 baseEnd_3389522 := by
    simpa [prefixWord, tailWord_3389522, baseEnd_3389522] using wordTrace_append hprefix tailTrace_3389522
  have hstable : (prefixWord ++ tailWord_3389522).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3389522).length < 2 ^ (prefixWord ++ tailWord_3389522).sum := by decide
  have hdescent : baseEnd_3389522 < baseStart_3389522 := by decide
  rcases family_descends (prefixWord ++ tailWord_3389522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3389533 : List Nat := [1, 4, 4, 1, 1, 3, 8]
def baseStart_3389533 : Nat := 118140960795 + 3389533 * 2 ^ 59
def prefixEnd_3389533 : Nat := 4983230072969 + 3 ^ 40 * 3389533 * 2
def baseEnd_3389533 : Nat := 42974311685831905438255

theorem tailTrace_3389533 : CollatzResearch.WordTrace tailWord_3389533 prefixEnd_3389533 42974311685831905438255 := by
  unfold tailWord_3389533
  simp only [CollatzResearch.WordTrace]
  refine ⟨123626424829308301994029253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82417616552872201329352835 123626424829308301994029253)
  ·
    refine ⟨23179954655495306623880485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 123626424829308301994029253 23179954655495306623880485)
    ·
      refine ⟨4346241497905369991977591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23179954655495306623880485 4346241497905369991977591)
      ·
        refine ⟨6519362246858054987966387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4346241497905369991977591 6519362246858054987966387)
        ·
          refine ⟨9779043370287082481949581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6519362246858054987966387 9779043370287082481949581)
          ·
            refine ⟨3667141263857655930731093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9779043370287082481949581 3667141263857655930731093)
            ·
              refine ⟨42974311685831905438255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3667141263857655930731093 42974311685831905438255)
              ·
                rfl

theorem cell22_3389533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 3, 8].length) (baseStart_3389533 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3389533 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3389533 prefixEnd_3389533 := by exact prefixLift 3389533
  have htrace : WordTrace (prefixWord ++ tailWord_3389533) baseStart_3389533 baseEnd_3389533 := by
    simpa [prefixWord, tailWord_3389533, baseEnd_3389533] using wordTrace_append hprefix tailTrace_3389533
  have hstable : (prefixWord ++ tailWord_3389533).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3389533).length < 2 ^ (prefixWord ++ tailWord_3389533).sum := by decide
  have hdescent : baseEnd_3389533 < baseStart_3389533 := by decide
  rcases family_descends (prefixWord ++ tailWord_3389533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3389548 : List Nat := [2, 2, 1, 1, 3, 3, 3, 1, 3, 3]
def baseStart_3389548 : Nat := 118140960795 + 3389548 * 2 ^ 59
def prefixEnd_3389548 : Nat := 4983230072969 + 3 ^ 40 * 3389548 * 2
def baseEnd_3389548 : Nat := 1160311550324006407707839

theorem tailTrace_3389548 : CollatzResearch.WordTrace tailWord_3389548 prefixEnd_3389548 1160311550324006407707839 := by
  unfold tailWord_3389548
  simp only [CollatzResearch.WordTrace]
  refine ⟨61813485962126979777912649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82417981282835973037216865 61813485962126979777912649)
  ·
    refine ⟨46360114471595234833434487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61813485962126979777912649 46360114471595234833434487)
    ·
      refine ⟨69540171707392852250151731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46360114471595234833434487 69540171707392852250151731)
      ·
        refine ⟨104310257561089278375227597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69540171707392852250151731 104310257561089278375227597)
        ·
          refine ⟨39116346585408479390710349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 104310257561089278375227597 39116346585408479390710349)
          ·
            refine ⟨14668629969528179771516381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39116346585408479390710349 14668629969528179771516381)
            ·
              refine ⟨5500736238573067414318643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14668629969528179771516381 5500736238573067414318643)
              ·
                refine ⟨8251104357859601121477965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5500736238573067414318643 8251104357859601121477965)
                ·
                  refine ⟨3094164134197350420554237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8251104357859601121477965 3094164134197350420554237)
                  ·
                    refine ⟨1160311550324006407707839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3094164134197350420554237 1160311550324006407707839)
                    ·
                      rfl

theorem cell22_3389548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 3, 3].length) (baseStart_3389548 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3389548 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3389548 prefixEnd_3389548 := by exact prefixLift 3389548
  have htrace : WordTrace (prefixWord ++ tailWord_3389548) baseStart_3389548 baseEnd_3389548 := by
    simpa [prefixWord, tailWord_3389548, baseEnd_3389548] using wordTrace_append hprefix tailTrace_3389548
  have hstable : (prefixWord ++ tailWord_3389548).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3389548).length < 2 ^ (prefixWord ++ tailWord_3389548).sum := by decide
  have hdescent : baseEnd_3389548 < baseStart_3389548 := by decide
  rcases family_descends (prefixWord ++ tailWord_3389548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3389590 : List Nat := [5, 3, 2, 1, 2, 1, 2, 2, 4]
def baseStart_3389590 : Nat := 118140960795 + 3389590 * 2 ^ 59
def prefixEnd_3389590 : Nat := 4983230072969 + 3 ^ 40 * 3389590 * 2
def baseEnd_3389590 : Nat := 386775309260777432719237

theorem tailTrace_3389590 : CollatzResearch.WordTrace tailWord_3389590 prefixEnd_3389590 386775309260777432719237 := by
  unfold tailWord_3389590
  simp only [CollatzResearch.WordTrace]
  refine ⟨7726781486881362545553389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 82419002526734533819236149 7726781486881362545553389)
  ·
    refine ⟨2897543057580510954582521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7726781486881362545553389 2897543057580510954582521)
    ·
      refine ⟨2173157293185383215936891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2897543057580510954582521 2173157293185383215936891)
      ·
        refine ⟨3259735939778074823905337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2173157293185383215936891 3259735939778074823905337)
        ·
          refine ⟨2444801954833556117929003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3259735939778074823905337 2444801954833556117929003)
          ·
            refine ⟨3667202932250334176893505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2444801954833556117929003 3667202932250334176893505)
            ·
              refine ⟨2750402199187750632670129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3667202932250334176893505 2750402199187750632670129)
              ·
                refine ⟨2062801649390812974502597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2750402199187750632670129 2062801649390812974502597)
                ·
                  refine ⟨386775309260777432719237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2062801649390812974502597 386775309260777432719237)
                  ·
                    rfl

theorem cell22_3389590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 2, 1, 2, 2, 4].length) (baseStart_3389590 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3389590 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3389590 prefixEnd_3389590 := by exact prefixLift 3389590
  have htrace : WordTrace (prefixWord ++ tailWord_3389590) baseStart_3389590 baseEnd_3389590 := by
    simpa [prefixWord, tailWord_3389590, baseEnd_3389590] using wordTrace_append hprefix tailTrace_3389590
  have hstable : (prefixWord ++ tailWord_3389590).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3389590).length < 2 ^ (prefixWord ++ tailWord_3389590).sum := by decide
  have hdescent : baseEnd_3389590 < baseStart_3389590 := by decide
  rcases family_descends (prefixWord ++ tailWord_3389590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3389599 : List Nat := [1, 1, 2, 6, 1, 3, 2, 2, 1, 3]
def baseStart_3389599 : Nat := 118140960795 + 3389599 * 2 ^ 59
def prefixEnd_3389599 : Nat := 4983230072969 + 3 ^ 40 * 3389599 * 2
def baseEnd_3389599 : Nat := 1160329008666259274682683

theorem tailTrace_3389599 : CollatzResearch.WordTrace tailWord_3389599 prefixEnd_3389599 1160329008666259274682683 := by
  unfold tailWord_3389599
  simp only [CollatzResearch.WordTrace]
  refine ⟨123628832047069195265931851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82419221364712796843954567 123628832047069195265931851)
  ·
    refine ⟨185443248070603792898897777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123628832047069195265931851 185443248070603792898897777)
    ·
      refine ⟨139082436052952844674173333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 185443248070603792898897777 139082436052952844674173333)
      ·
        refine ⟨6519489189982164594101875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 139082436052952844674173333 6519489189982164594101875)
        ·
          refine ⟨9779233784973246891152813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6519489189982164594101875 9779233784973246891152813)
          ·
            refine ⟨3667212669364967584182305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9779233784973246891152813 3667212669364967584182305)
            ·
              refine ⟨2750409502023725688136729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3667212669364967584182305 2750409502023725688136729)
              ·
                refine ⟨2062807126517794266102547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2750409502023725688136729 2062807126517794266102547)
                ·
                  refine ⟨3094210689776691399153821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2062807126517794266102547 3094210689776691399153821)
                  ·
                    refine ⟨1160329008666259274682683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3094210689776691399153821 1160329008666259274682683)
                    ·
                      rfl

theorem cell22_3389599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 3, 2, 2, 1, 3].length) (baseStart_3389599 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3389599 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3389599 prefixEnd_3389599 := by exact prefixLift 3389599
  have htrace : WordTrace (prefixWord ++ tailWord_3389599) baseStart_3389599 baseEnd_3389599 := by
    simpa [prefixWord, tailWord_3389599, baseEnd_3389599] using wordTrace_append hprefix tailTrace_3389599
  have hstable : (prefixWord ++ tailWord_3389599).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3389599).length < 2 ^ (prefixWord ++ tailWord_3389599).sum := by decide
  have hdescent : baseEnd_3389599 < baseStart_3389599 := by decide
  rcases family_descends (prefixWord ++ tailWord_3389599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3389610 : List Nat := [3, 1, 5, 1, 2, 1, 1, 1, 2, 5]
def baseStart_3389610 : Nat := 118140960795 + 3389610 * 2 ^ 59
def prefixEnd_3389610 : Nat := 4983230072969 + 3 ^ 40 * 3389610 * 2
def baseEnd_3389610 : Nat := 1160332774191058912657649

theorem tailTrace_3389610 : CollatzResearch.WordTrace tailWord_3389610 prefixEnd_3389610 1160332774191058912657649 := by
  unfold tailWord_3389610
  simp only [CollatzResearch.WordTrace]
  refine ⟨30907308312507336036145571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82419488833352896096388189 30907308312507336036145571)
  ·
    refine ⟨46360962468761004054218357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30907308312507336036145571 46360962468761004054218357)
    ·
      refine ⟨4346340231446344130082971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 46360962468761004054218357 4346340231446344130082971)
      ·
        refine ⟨6519510347169516195124457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4346340231446344130082971 6519510347169516195124457)
        ·
          refine ⟨4889632760377137146343343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6519510347169516195124457 4889632760377137146343343)
          ·
            refine ⟨7334449140565705719515015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4889632760377137146343343 7334449140565705719515015)
            ·
              refine ⟨11001673710848558579272523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7334449140565705719515015 11001673710848558579272523)
              ·
                refine ⟨16502510566272837868908785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11001673710848558579272523 16502510566272837868908785)
                ·
                  refine ⟨12376882924704628401681589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16502510566272837868908785 12376882924704628401681589)
                  ·
                    refine ⟨1160332774191058912657649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12376882924704628401681589 1160332774191058912657649)
                    ·
                      rfl

theorem cell22_3389610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 1, 1, 2, 5].length) (baseStart_3389610 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3389610 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3389610 prefixEnd_3389610 := by exact prefixLift 3389610
  have htrace : WordTrace (prefixWord ++ tailWord_3389610) baseStart_3389610 baseEnd_3389610 := by
    simpa [prefixWord, tailWord_3389610, baseEnd_3389610] using wordTrace_append hprefix tailTrace_3389610
  have hstable : (prefixWord ++ tailWord_3389610).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3389610).length < 2 ^ (prefixWord ++ tailWord_3389610).sum := by decide
  have hdescent : baseEnd_3389610 < baseStart_3389610 := by decide
  rcases family_descends (prefixWord ++ tailWord_3389610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3389672 : List Nat := [2, 1, 4, 1, 2, 3, 3, 1, 2, 3]
def baseStart_3389672 : Nat := 118140960795 + 3389672 * 2 ^ 59
def prefixEnd_3389672 : Nat := 4983230072969 + 3 ^ 40 * 3389672 * 2
def baseEnd_3389672 : Nat := 1160353998058111417607459

theorem tailTrace_3389672 : CollatzResearch.WordTrace tailWord_3389672 prefixEnd_3389672 1160353998058111417607459 := by
  unfold tailWord_3389672
  simp only [CollatzResearch.WordTrace]
  refine ⟨61815747287902364366669635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82420996383869819155559513 61815747287902364366669635)
  ·
    refine ⟨92723620931853546550004453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61815747287902364366669635 92723620931853546550004453)
    ·
      refine ⟨17385678924722539978125835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 92723620931853546550004453 17385678924722539978125835)
      ·
        refine ⟨26078518387083809967188753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17385678924722539978125835 26078518387083809967188753)
        ·
          refine ⟨19558888790312857475391565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26078518387083809967188753 19558888790312857475391565)
          ·
            refine ⟨7334583296367321553271837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19558888790312857475391565 7334583296367321553271837)
            ·
              refine ⟨2750468736137745582476939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7334583296367321553271837 2750468736137745582476939)
              ·
                refine ⟨4125703104206618373715409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2750468736137745582476939 4125703104206618373715409)
                ·
                  refine ⟨3094277328154963780286557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4125703104206618373715409 3094277328154963780286557)
                  ·
                    refine ⟨1160353998058111417607459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3094277328154963780286557 1160353998058111417607459)
                    ·
                      rfl

theorem cell22_3389672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 3, 1, 2, 3].length) (baseStart_3389672 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3389672 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3389672 prefixEnd_3389672 := by exact prefixLift 3389672
  have htrace : WordTrace (prefixWord ++ tailWord_3389672) baseStart_3389672 baseEnd_3389672 := by
    simpa [prefixWord, tailWord_3389672, baseEnd_3389672] using wordTrace_append hprefix tailTrace_3389672
  have hstable : (prefixWord ++ tailWord_3389672).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3389672).length < 2 ^ (prefixWord ++ tailWord_3389672).sum := by decide
  have hdescent : baseEnd_3389672 < baseStart_3389672 := by decide
  rcases family_descends (prefixWord ++ tailWord_3389672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3389681 : List Nat := [1, 2, 2, 2, 2, 1, 2, 2, 2, 6]
def baseStart_3389681 : Nat := 118140960795 + 3389681 * 2 ^ 59
def prefixEnd_3389681 : Nat := 4983230072969 + 3 ^ 40 * 3389681 * 2
def baseEnd_3389681 : Nat := 1160357078942038394132431

theorem tailTrace_3389681 : CollatzResearch.WordTrace tailWord_3389681 prefixEnd_3389681 1160357078942038394132431 := by
  unfold tailWord_3389681
  simp only [CollatzResearch.WordTrace]
  refine ⟨123631822832772123270416897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82421215221848082180277931 123631822832772123270416897)
  ·
    refine ⟨92723867124579092452812673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123631822832772123270416897 92723867124579092452812673)
    ·
      refine ⟨69542900343434319339609505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92723867124579092452812673 69542900343434319339609505)
      ·
        refine ⟨52157175257575739504707129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69542900343434319339609505 52157175257575739504707129)
        ·
          refine ⟨39117881443181804628530347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52157175257575739504707129 39117881443181804628530347)
          ·
            refine ⟨58676822164772706942795521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39117881443181804628530347 58676822164772706942795521)
            ·
              refine ⟨44007616623579530207096641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58676822164772706942795521 44007616623579530207096641)
              ·
                refine ⟨33005712467684647655322481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44007616623579530207096641 33005712467684647655322481)
                ·
                  refine ⟨24754284350763485741491861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33005712467684647655322481 24754284350763485741491861)
                  ·
                    refine ⟨1160357078942038394132431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24754284350763485741491861 1160357078942038394132431)
                    ·
                      rfl

theorem cell22_3389681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 2, 2, 6].length) (baseStart_3389681 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3389681 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3389681 prefixEnd_3389681 := by exact prefixLift 3389681
  have htrace : WordTrace (prefixWord ++ tailWord_3389681) baseStart_3389681 baseEnd_3389681 := by
    simpa [prefixWord, tailWord_3389681, baseEnd_3389681] using wordTrace_append hprefix tailTrace_3389681
  have hstable : (prefixWord ++ tailWord_3389681).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3389681).length < 2 ^ (prefixWord ++ tailWord_3389681).sum := by decide
  have hdescent : baseEnd_3389681 < baseStart_3389681 := by decide
  rcases family_descends (prefixWord ++ tailWord_3389681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3389683 : List Nat := [1, 1, 1, 2, 2, 4, 1, 4, 3, 3]
def baseStart_3389683 : Nat := 118140960795 + 3389683 * 2 ^ 59
def prefixEnd_3389683 : Nat := 4983230072969 + 3 ^ 40 * 3389683 * 2
def baseEnd_3389683 : Nat := 1160357763582911055582425

theorem tailTrace_3389683 : CollatzResearch.WordTrace tailWord_3389683 prefixEnd_3389683 1160357763582911055582425 := by
  unfold tailWord_3389683
  simp only [CollatzResearch.WordTrace]
  refine ⟨123631895778764877611989703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82421263852509918407993135 123631895778764877611989703)
  ·
    refine ⟨185447843668147316417984555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123631895778764877611989703 185447843668147316417984555)
    ·
      refine ⟨278171765502220974626976833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185447843668147316417984555 278171765502220974626976833)
      ·
        refine ⟨208628824126665730970232625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 278171765502220974626976833 208628824126665730970232625)
        ·
          refine ⟨156471618094999298227674469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 208628824126665730970232625 156471618094999298227674469)
          ·
            refine ⟨29338428392812368417688963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 156471618094999298227674469 29338428392812368417688963)
            ·
              refine ⟨44007642589218552626533445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29338428392812368417688963 44007642589218552626533445)
              ·
                refine ⟨8251432985478478617475021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44007642589218552626533445 8251432985478478617475021)
                ·
                  refine ⟨3094287369554429481553133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8251432985478478617475021 3094287369554429481553133)
                  ·
                    refine ⟨1160357763582911055582425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3094287369554429481553133 1160357763582911055582425)
                    ·
                      rfl

theorem cell22_3389683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 4, 3, 3].length) (baseStart_3389683 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3389683 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3389683 prefixEnd_3389683 := by exact prefixLift 3389683
  have htrace : WordTrace (prefixWord ++ tailWord_3389683) baseStart_3389683 baseEnd_3389683 := by
    simpa [prefixWord, tailWord_3389683, baseEnd_3389683] using wordTrace_append hprefix tailTrace_3389683
  have hstable : (prefixWord ++ tailWord_3389683).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3389683).length < 2 ^ (prefixWord ++ tailWord_3389683).sum := by decide
  have hdescent : baseEnd_3389683 < baseStart_3389683 := by decide
  rcases family_descends (prefixWord ++ tailWord_3389683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3389696 : List Nat := [2, 1, 1, 2, 1, 1, 5, 2, 7]
def baseStart_3389696 : Nat := 118140960795 + 3389696 * 2 ^ 59
def prefixEnd_3389696 : Nat := 4983230072969 + 3 ^ 40 * 3389696 * 2
def baseEnd_3389696 : Nat := 386787404582861118335795

theorem tailTrace_3389696 : CollatzResearch.WordTrace tailWord_3389696 prefixEnd_3389696 386787404582861118335795 := by
  unfold tailWord_3389696
  simp only [CollatzResearch.WordTrace]
  refine ⟨61816184963858890416106471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82421579951811853888141961 61816184963858890416106471)
  ·
    refine ⟨92724277445788335624159707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61816184963858890416106471 92724277445788335624159707)
    ·
      refine ⟨139086416168682503436239561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92724277445788335624159707 139086416168682503436239561)
      ·
        refine ⟨104314812126511877577179671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139086416168682503436239561 104314812126511877577179671)
        ·
          refine ⟨156472218189767816365769507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104314812126511877577179671 156472218189767816365769507)
          ·
            refine ⟨234708327284651724548654261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 156472218189767816365769507 234708327284651724548654261)
            ·
              refine ⟨22003905682936099176436337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 234708327284651724548654261 22003905682936099176436337)
              ·
                refine ⟨16502929262202074382327253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22003905682936099176436337 16502929262202074382327253)
                ·
                  refine ⟨386787404582861118335795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16502929262202074382327253 386787404582861118335795)
                  ·
                    rfl

theorem cell22_3389696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 5, 2, 7].length) (baseStart_3389696 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3389696 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3389696 prefixEnd_3389696 := by exact prefixLift 3389696
  have htrace : WordTrace (prefixWord ++ tailWord_3389696) baseStart_3389696 baseEnd_3389696 := by
    simpa [prefixWord, tailWord_3389696, baseEnd_3389696] using wordTrace_append hprefix tailTrace_3389696
  have hstable : (prefixWord ++ tailWord_3389696).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3389696).length < 2 ^ (prefixWord ++ tailWord_3389696).sum := by decide
  have hdescent : baseEnd_3389696 < baseStart_3389696 := by decide
  rcases family_descends (prefixWord ++ tailWord_3389696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3389711 : List Nat := [1, 1, 2, 1, 1, 1, 3, 3, 4, 5]
def baseStart_3389711 : Nat := 118140960795 + 3389711 * 2 ^ 59
def prefixEnd_3389711 : Nat := 4983230072969 + 3 ^ 40 * 3389711 * 2
def baseEnd_3389711 : Nat := 1160367348555128315882339

theorem tailTrace_3389711 : CollatzResearch.WordTrace tailWord_3389711 prefixEnd_3389711 1160367348555128315882339 := by
  unfold tailWord_3389711
  simp only [CollatzResearch.WordTrace]
  refine ⟨123632917022663438394008987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82421944681775625596005991 123632917022663438394008987)
  ·
    refine ⟨185449375533995157591013481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123632917022663438394008987 185449375533995157591013481)
    ·
      refine ⟨139087031650496368193260111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 185449375533995157591013481 139087031650496368193260111)
      ·
        refine ⟨208630547475744552289890167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139087031650496368193260111 208630547475744552289890167)
        ·
          refine ⟨312945821213616828434835251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 208630547475744552289890167 312945821213616828434835251)
          ·
            refine ⟨469418731820425242652252877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 312945821213616828434835251 469418731820425242652252877)
            ·
              refine ⟨176032024432659465994594829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 469418731820425242652252877 176032024432659465994594829)
              ·
                refine ⟨66012009162247299747973061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 176032024432659465994594829 66012009162247299747973061)
                ·
                  refine ⟨12377251717921368702744949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 66012009162247299747973061 12377251717921368702744949)
                  ·
                    refine ⟨1160367348555128315882339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12377251717921368702744949 1160367348555128315882339)
                    ·
                      rfl

theorem cell22_3389711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 3, 4, 5].length) (baseStart_3389711 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3389711 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3389711 prefixEnd_3389711 := by exact prefixLift 3389711
  have htrace : WordTrace (prefixWord ++ tailWord_3389711) baseStart_3389711 baseEnd_3389711 := by
    simpa [prefixWord, tailWord_3389711, baseEnd_3389711] using wordTrace_append hprefix tailTrace_3389711
  have hstable : (prefixWord ++ tailWord_3389711).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3389711).length < 2 ^ (prefixWord ++ tailWord_3389711).sum := by decide
  have hdescent : baseEnd_3389711 < baseStart_3389711 := by decide
  rcases family_descends (prefixWord ++ tailWord_3389711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3389730 : List Nat := [3, 3, 1, 1, 3, 2, 1, 3, 5]
def baseStart_3389730 : Nat := 118140960795 + 3389730 * 2 ^ 59
def prefixEnd_3389730 : Nat := 4983230072969 + 3 ^ 40 * 3389730 * 2
def baseEnd_3389730 : Nat := 386791284214472866552427

theorem tailTrace_3389730 : CollatzResearch.WordTrace tailWord_3389730 prefixEnd_3389730 386791284214472866552427 := by
  unfold tailWord_3389730
  simp only [CollatzResearch.WordTrace]
  refine ⟨30908402502398651159737661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82422406673063069759300429 30908402502398651159737661)
  ·
    refine ⟨11590650938399494184901623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30908402502398651159737661 11590650938399494184901623)
    ·
      refine ⟨17385976407599241277352435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11590650938399494184901623 17385976407599241277352435)
      ·
        refine ⟨26078964611398861916028653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17385976407599241277352435 26078964611398861916028653)
        ·
          refine ⟨9779611729274573218510745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26078964611398861916028653 9779611729274573218510745)
          ·
            refine ⟨7334708796955929913883059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9779611729274573218510745 7334708796955929913883059)
            ·
              refine ⟨11002063195433894870824589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7334708796955929913883059 11002063195433894870824589)
              ·
                refine ⟨4125773698287710576559221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11002063195433894870824589 4125773698287710576559221)
                ·
                  refine ⟨386791284214472866552427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4125773698287710576559221 386791284214472866552427)
                  ·
                    rfl

theorem cell22_3389730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 1, 3, 5].length) (baseStart_3389730 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3389730 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3389730 prefixEnd_3389730 := by exact prefixLift 3389730
  have htrace : WordTrace (prefixWord ++ tailWord_3389730) baseStart_3389730 baseEnd_3389730 := by
    simpa [prefixWord, tailWord_3389730, baseEnd_3389730] using wordTrace_append hprefix tailTrace_3389730
  have hstable : (prefixWord ++ tailWord_3389730).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3389730).length < 2 ^ (prefixWord ++ tailWord_3389730).sum := by decide
  have hdescent : baseEnd_3389730 < baseStart_3389730 := by decide
  rcases family_descends (prefixWord ++ tailWord_3389730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3389835 : List Nat := [1, 1, 1, 1, 4, 4, 1, 3, 3, 3]
def baseStart_3389835 : Nat := 118140960795 + 3389835 * 2 ^ 59
def prefixEnd_3389835 : Nat := 4983230072969 + 3 ^ 40 * 3389835 * 2
def baseEnd_3389835 : Nat := 1160409796289233325781959

theorem tailTrace_3389835 : CollatzResearch.WordTrace tailWord_3389835 prefixEnd_3389835 1160409796289233325781959 := by
  unfold tailWord_3389835
  simp only [CollatzResearch.WordTrace]
  refine ⟨123637439674214207571522959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82424959782809471714348639 123637439674214207571522959)
  ·
    refine ⟨185456159511321311357284439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123637439674214207571522959 185456159511321311357284439)
    ·
      refine ⟨278184239266981967035926659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185456159511321311357284439 278184239266981967035926659)
      ·
        refine ⟨417276358900472950553889989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 278184239266981967035926659 417276358900472950553889989)
        ·
          refine ⟨78239317293838678228854373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 417276358900472950553889989 78239317293838678228854373)
          ·
            refine ⟨14669871992594752167910195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 78239317293838678228854373 14669871992594752167910195)
            ·
              refine ⟨22004807988892128251865293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14669871992594752167910195 22004807988892128251865293)
              ·
                refine ⟨8251802995834548094449485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22004807988892128251865293 8251802995834548094449485)
                ·
                  refine ⟨3094426123437955535418557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8251802995834548094449485 3094426123437955535418557)
                  ·
                    refine ⟨1160409796289233325781959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3094426123437955535418557 1160409796289233325781959)
                    ·
                      rfl

theorem cell22_3389835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 1, 3, 3, 3].length) (baseStart_3389835 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3389835 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3389835 prefixEnd_3389835 := by exact prefixLift 3389835
  have htrace : WordTrace (prefixWord ++ tailWord_3389835) baseStart_3389835 baseEnd_3389835 := by
    simpa [prefixWord, tailWord_3389835, baseEnd_3389835] using wordTrace_append hprefix tailTrace_3389835
  have hstable : (prefixWord ++ tailWord_3389835).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3389835).length < 2 ^ (prefixWord ++ tailWord_3389835).sum := by decide
  have hdescent : baseEnd_3389835 < baseStart_3389835 := by decide
  rcases family_descends (prefixWord ++ tailWord_3389835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3389854 : List Nat := [4, 3, 1, 2, 1, 3, 2, 6]
def baseStart_3389854 : Nat := 118140960795 + 3389854 * 2 ^ 59
def prefixEnd_3389854 : Nat := 4983230072969 + 3 ^ 40 * 3389854 * 2
def baseEnd_3389854 : Nat := 128935144486391512172989

theorem tailTrace_3389854 : CollatzResearch.WordTrace tailWord_3389854 prefixEnd_3389854 128935144486391512172989 := by
  unfold tailWord_3389854
  simp only [CollatzResearch.WordTrace]
  refine ⟨15454766582643171727058077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 82425421774096915877643077 15454766582643171727058077)
  ·
    refine ⟨5795537468491189397646779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15454766582643171727058077 5795537468491189397646779)
    ·
      refine ⟨8693306202736784096470169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5795537468491189397646779 8693306202736784096470169)
      ·
        refine ⟨6519979652052588072352627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8693306202736784096470169 6519979652052588072352627)
        ·
          refine ⟨9779969478078882108528941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6519979652052588072352627 9779969478078882108528941)
          ·
            refine ⟨3667488554279580790698353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9779969478078882108528941 3667488554279580790698353)
            ·
              refine ⟨2750616415709685593023765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3667488554279580790698353 2750616415709685593023765)
              ·
                refine ⟨128935144486391512172989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2750616415709685593023765 128935144486391512172989)
                ·
                  rfl

theorem cell22_3389854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 3, 2, 6].length) (baseStart_3389854 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3389854 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3389854 prefixEnd_3389854 := by exact prefixLift 3389854
  have htrace : WordTrace (prefixWord ++ tailWord_3389854) baseStart_3389854 baseEnd_3389854 := by
    simpa [prefixWord, tailWord_3389854, baseEnd_3389854] using wordTrace_append hprefix tailTrace_3389854
  have hstable : (prefixWord ++ tailWord_3389854).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3389854).length < 2 ^ (prefixWord ++ tailWord_3389854).sum := by decide
  have hdescent : baseEnd_3389854 < baseStart_3389854 := by decide
  rcases family_descends (prefixWord ++ tailWord_3389854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3389927 : List Nat := [1, 1, 5, 2, 1, 1, 2, 5, 4]
def baseStart_3389927 : Nat := 118140960795 + 3389927 * 2 ^ 59
def prefixEnd_3389927 : Nat := 4983230072969 + 3 ^ 40 * 3389927 * 2
def baseEnd_3389927 : Nat := 386813763256458584160559

theorem tailTrace_3389927 : CollatzResearch.WordTrace tailWord_3389927 prefixEnd_3389927 386813763256458584160559 := by
  unfold tailWord_3389927
  simp only [CollatzResearch.WordTrace]
  refine ⟨123640795189880907283872035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82427196793253938189248023 123640795189880907283872035)
  ·
    refine ⟨185461192784821360925808053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123640795189880907283872035 185461192784821360925808053)
    ·
      refine ⟨17386986823577002586794505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 185461192784821360925808053 17386986823577002586794505)
      ·
        refine ⟨13040240117682751940095879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17386986823577002586794505 13040240117682751940095879)
        ·
          refine ⟨19560360176524127910143819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13040240117682751940095879 19560360176524127910143819)
          ·
            refine ⟨29340540264786191865215729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19560360176524127910143819 29340540264786191865215729)
            ·
              refine ⟨22005405198589643898911797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29340540264786191865215729 22005405198589643898911797)
              ·
                refine ⟨2063006737367779115522981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22005405198589643898911797 2063006737367779115522981)
                ·
                  refine ⟨386813763256458584160559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2063006737367779115522981 386813763256458584160559)
                  ·
                    rfl

theorem cell22_3389927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 2, 5, 4].length) (baseStart_3389927 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3389927 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3389927 prefixEnd_3389927 := by exact prefixLift 3389927
  have htrace : WordTrace (prefixWord ++ tailWord_3389927) baseStart_3389927 baseEnd_3389927 := by
    simpa [prefixWord, tailWord_3389927, baseEnd_3389927] using wordTrace_append hprefix tailTrace_3389927
  have hstable : (prefixWord ++ tailWord_3389927).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3389927).length < 2 ^ (prefixWord ++ tailWord_3389927).sum := by decide
  have hdescent : baseEnd_3389927 < baseStart_3389927 := by decide
  rcases family_descends (prefixWord ++ tailWord_3389927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3390015 : List Nat := [1, 1, 2, 2, 3, 2, 1, 3, 2, 5]
def baseStart_3390015 : Nat := 118140960795 + 3390015 * 2 ^ 59
def prefixEnd_3390015 : Nat := 4983230072969 + 3 ^ 40 * 3390015 * 2
def baseEnd_3390015 : Nat := 1160471413967772856281407

theorem tailTrace_3390015 : CollatzResearch.WordTrace tailWord_3390015 prefixEnd_3390015 1160471413967772856281407 := by
  unfold tailWord_3390015
  simp only [CollatzResearch.WordTrace]
  refine ⟨123644004813562098313075499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82429336542374732208716999 123644004813562098313075499)
  ·
    refine ⟨185466007220343147469613249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123644004813562098313075499 185466007220343147469613249)
    ·
      refine ⟨139099505415257360602209937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 185466007220343147469613249 139099505415257360602209937)
      ·
        refine ⟨104324629061443020451657453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139099505415257360602209937 104324629061443020451657453)
        ·
          refine ⟨39121735898041132669371545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 104324629061443020451657453 39121735898041132669371545)
          ·
            refine ⟨29341301923530849502028659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39121735898041132669371545 29341301923530849502028659)
            ·
              refine ⟨44011952885296274253042989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29341301923530849502028659 44011952885296274253042989)
              ·
                refine ⟨16504482331986102844891121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44011952885296274253042989 16504482331986102844891121)
                ·
                  refine ⟨12378361748989577133668341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16504482331986102844891121 12378361748989577133668341)
                  ·
                    refine ⟨1160471413967772856281407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12378361748989577133668341 1160471413967772856281407)
                    ·
                      rfl

theorem cell22_3390015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 3, 2, 5].length) (baseStart_3390015 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3390015 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3390015 prefixEnd_3390015 := by exact prefixLift 3390015
  have htrace : WordTrace (prefixWord ++ tailWord_3390015) baseStart_3390015 baseEnd_3390015 := by
    simpa [prefixWord, tailWord_3390015, baseEnd_3390015] using wordTrace_append hprefix tailTrace_3390015
  have hstable : (prefixWord ++ tailWord_3390015).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3390015).length < 2 ^ (prefixWord ++ tailWord_3390015).sum := by decide
  have hdescent : baseEnd_3390015 < baseStart_3390015 := by decide
  rcases family_descends (prefixWord ++ tailWord_3390015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3390075 : List Nat := [1, 1, 1, 1, 1, 4, 2, 4, 1, 6]
def baseStart_3390075 : Nat := 118140960795 + 3390075 * 2 ^ 59
def prefixEnd_3390075 : Nat := 4983230072969 + 3 ^ 40 * 3390075 * 2
def baseEnd_3390075 : Nat := 1160491953193952699781223

theorem tailTrace_3390075 : CollatzResearch.WordTrace tailWord_3390075 prefixEnd_3390075 1160491953193952699781223 := by
  unfold tailWord_3390075
  simp only [CollatzResearch.WordTrace]
  refine ⟨123646193193344728560259679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82430795462229819040173119 123646193193344728560259679)
  ·
    refine ⟨185469289790017092840389519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123646193193344728560259679 185469289790017092840389519)
    ·
      refine ⟨278203934685025639260584279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185469289790017092840389519 278203934685025639260584279)
      ·
        refine ⟨417305902027538458890876419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 278203934685025639260584279 417305902027538458890876419)
        ·
          refine ⟨625958853041307688336314629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 417305902027538458890876419 625958853041307688336314629)
          ·
            refine ⟨117367284945245191563058993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 625958853041307688336314629 117367284945245191563058993)
            ·
              refine ⟨88025463708933893672294245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 117367284945245191563058993 88025463708933893672294245)
              ·
                refine ⟨16504774445425105063555171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 88025463708933893672294245 16504774445425105063555171)
                ·
                  refine ⟨24757161668137657595332757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16504774445425105063555171 24757161668137657595332757)
                  ·
                    refine ⟨1160491953193952699781223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24757161668137657595332757 1160491953193952699781223)
                    ·
                      rfl

theorem cell22_3390075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 4, 1, 6].length) (baseStart_3390075 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3390075 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3390075 prefixEnd_3390075 := by exact prefixLift 3390075
  have htrace : WordTrace (prefixWord ++ tailWord_3390075) baseStart_3390075 baseEnd_3390075 := by
    simpa [prefixWord, tailWord_3390075, baseEnd_3390075] using wordTrace_append hprefix tailTrace_3390075
  have hstable : (prefixWord ++ tailWord_3390075).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3390075).length < 2 ^ (prefixWord ++ tailWord_3390075).sum := by decide
  have hdescent : baseEnd_3390075 < baseStart_3390075 := by decide
  rcases family_descends (prefixWord ++ tailWord_3390075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3390113 : List Nat := [1, 2, 3, 3, 3, 2, 2, 2, 4]
def baseStart_3390113 : Nat := 118140960795 + 3390113 * 2 ^ 59
def prefixEnd_3390113 : Nat := 4983230072969 + 3 ^ 40 * 3390113 * 2
def baseEnd_3390113 : Nat := 386834987123511089110369

theorem tailTrace_3390113 : CollatzResearch.WordTrace tailWord_3390113 prefixEnd_3390113 386834987123511089110369 := by
  unfold tailWord_3390113
  simp only [CollatzResearch.WordTrace]
  refine ⟨123647579167207061050142993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82431719444804707366761995 123647579167207061050142993)
  ·
    refine ⟨92735684375405295787607245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123647579167207061050142993 92735684375405295787607245)
    ·
      refine ⟨34775881640776985920352717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92735684375405295787607245 34775881640776985920352717)
      ·
        refine ⟨13040955615291369720132269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34775881640776985920352717 13040955615291369720132269)
        ·
          refine ⟨4890358355734263645049601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13040955615291369720132269 4890358355734263645049601)
          ·
            refine ⟨3667768766800697733787201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4890358355734263645049601 3667768766800697733787201)
            ·
              refine ⟨2750826575100523300340401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3667768766800697733787201 2750826575100523300340401)
              ·
                refine ⟨2063119931325392475255301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2750826575100523300340401 2063119931325392475255301)
                ·
                  refine ⟨386834987123511089110369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2063119931325392475255301 386834987123511089110369)
                  ·
                    rfl

theorem cell22_3390113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 2, 2, 2, 4].length) (baseStart_3390113 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3390113 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3390113 prefixEnd_3390113 := by exact prefixLift 3390113
  have htrace : WordTrace (prefixWord ++ tailWord_3390113) baseStart_3390113 baseEnd_3390113 := by
    simpa [prefixWord, tailWord_3390113, baseEnd_3390113] using wordTrace_append hprefix tailTrace_3390113
  have hstable : (prefixWord ++ tailWord_3390113).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3390113).length < 2 ^ (prefixWord ++ tailWord_3390113).sum := by decide
  have hdescent : baseEnd_3390113 < baseStart_3390113 := by decide
  rcases family_descends (prefixWord ++ tailWord_3390113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3390167 : List Nat := [1, 1, 3, 2, 1, 4, 1, 2, 2, 5]
def baseStart_3390167 : Nat := 118140960795 + 3390167 * 2 ^ 59
def prefixEnd_3390167 : Nat := 4983230072969 + 3 ^ 40 * 3390167 * 2
def baseEnd_3390167 : Nat := 1160523446674095126480941

theorem tailTrace_3390167 : CollatzResearch.WordTrace tailWord_3390167 prefixEnd_3390167 1160523446674095126480941 := by
  unfold tailWord_3390167
  simp only [CollatzResearch.WordTrace]
  refine ⟨123649548709011428272608755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82433032472674285515072503 123649548709011428272608755)
  ·
    refine ⟨185474323063517142408913133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123649548709011428272608755 185474323063517142408913133)
    ·
      refine ⟨69552871148818928403342425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 185474323063517142408913133 69552871148818928403342425)
      ·
        refine ⟨52164653361614196302506819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69552871148818928403342425 52164653361614196302506819)
        ·
          refine ⟨78246980042421294453760229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52164653361614196302506819 78246980042421294453760229)
          ·
            refine ⟨14671308757953992710080043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 78246980042421294453760229 14671308757953992710080043)
            ·
              refine ⟨22006963136930989065120065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14671308757953992710080043 22006963136930989065120065)
              ·
                refine ⟨16505222352698241798840049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22006963136930989065120065 16505222352698241798840049)
                ·
                  refine ⟨12378916764523681349130037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16505222352698241798840049 12378916764523681349130037)
                  ·
                    refine ⟨1160523446674095126480941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12378916764523681349130037 1160523446674095126480941)
                    ·
                      rfl

theorem cell22_3390167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 1, 2, 2, 5].length) (baseStart_3390167 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3390167 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3390167 prefixEnd_3390167 := by exact prefixLift 3390167
  have htrace : WordTrace (prefixWord ++ tailWord_3390167) baseStart_3390167 baseEnd_3390167 := by
    simpa [prefixWord, tailWord_3390167, baseEnd_3390167] using wordTrace_append hprefix tailTrace_3390167
  have hstable : (prefixWord ++ tailWord_3390167).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3390167).length < 2 ^ (prefixWord ++ tailWord_3390167).sum := by decide
  have hdescent : baseEnd_3390167 < baseStart_3390167 := by decide
  rcases family_descends (prefixWord ++ tailWord_3390167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3390229 : List Nat := [1, 3, 2, 1, 2, 2, 1, 3, 4, 3]
def baseStart_3390229 : Nat := 118140960795 + 3390229 * 2 ^ 59
def prefixEnd_3390229 : Nat := 4983230072969 + 3 ^ 40 * 3390229 * 2
def baseEnd_3390229 : Nat := 1160544670541147631430751

theorem tailTrace_3390229 : CollatzResearch.WordTrace tailWord_3390229 prefixEnd_3390229 1160544670541147631430751 := by
  unfold tailWord_3390229
  simp only [CollatzResearch.WordTrace]
  refine ⟨123651810034786812861365741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82434540023191208574243827 123651810034786812861365741)
  ·
    refine ⟨46369428763045054823012153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123651810034786812861365741 46369428763045054823012153)
    ·
      refine ⟨34777071572283791117259115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46369428763045054823012153 34777071572283791117259115)
      ·
        refine ⟨52165607358425686675888673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34777071572283791117259115 52165607358425686675888673)
        ·
          refine ⟨39124205518819265006916505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52165607358425686675888673 39124205518819265006916505)
          ·
            refine ⟨29343154139114448755187379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39124205518819265006916505 29343154139114448755187379)
            ·
              refine ⟨44014731208671673132781069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29343154139114448755187379 44014731208671673132781069)
              ·
                refine ⟨16505524203251877424792901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44014731208671673132781069 16505524203251877424792901)
                ·
                  refine ⟨3094785788109727017148669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16505524203251877424792901 3094785788109727017148669)
                  ·
                    refine ⟨1160544670541147631430751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3094785788109727017148669 1160544670541147631430751)
                    ·
                      rfl

theorem cell22_3390229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 3, 4, 3].length) (baseStart_3390229 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3390229 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3390229 prefixEnd_3390229 := by exact prefixLift 3390229
  have htrace : WordTrace (prefixWord ++ tailWord_3390229) baseStart_3390229 baseEnd_3390229 := by
    simpa [prefixWord, tailWord_3390229, baseEnd_3390229] using wordTrace_append hprefix tailTrace_3390229
  have hstable : (prefixWord ++ tailWord_3390229).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3390229).length < 2 ^ (prefixWord ++ tailWord_3390229).sum := by decide
  have hdescent : baseEnd_3390229 < baseStart_3390229 := by decide
  rcases family_descends (prefixWord ++ tailWord_3390229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3390231 : List Nat := [1, 1, 3, 4, 3, 2, 1, 1, 6]
def baseStart_3390231 : Nat := 118140960795 + 3390231 * 2 ^ 59
def prefixEnd_3390231 : Nat := 4983230072969 + 3 ^ 40 * 3390231 * 2
def baseEnd_3390231 : Nat := 386848451727340097626915

theorem tailTrace_3390231 : CollatzResearch.WordTrace tailWord_3390231 prefixEnd_3390231 386848451727340097626915 := by
  unfold tailWord_3390231
  simp only [CollatzResearch.WordTrace]
  refine ⟨123651882980779567202938547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82434588653853044801959031 123651882980779567202938547)
  ·
    refine ⟨185477824471169350804407821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123651882980779567202938547 185477824471169350804407821)
    ·
      refine ⟨69554184176688506551652933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 185477824471169350804407821 69554184176688506551652933)
      ·
        refine ⟨13041409533129094978434925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 69554184176688506551652933 13041409533129094978434925)
        ·
          refine ⟨4890528574923410616913097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13041409533129094978434925 4890528574923410616913097)
          ·
            refine ⟨3667896431192557962684823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4890528574923410616913097 3667896431192557962684823)
            ·
              refine ⟨5501844646788836944027235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3667896431192557962684823 5501844646788836944027235)
              ·
                refine ⟨8252766970183255416040853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5501844646788836944027235 8252766970183255416040853)
                ·
                  refine ⟨386848451727340097626915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8252766970183255416040853 386848451727340097626915)
                  ·
                    rfl

theorem cell22_3390231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 2, 1, 1, 6].length) (baseStart_3390231 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3390231 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3390231 prefixEnd_3390231 := by exact prefixLift 3390231
  have htrace : WordTrace (prefixWord ++ tailWord_3390231) baseStart_3390231 baseEnd_3390231 := by
    simpa [prefixWord, tailWord_3390231, baseEnd_3390231] using wordTrace_append hprefix tailTrace_3390231
  have hstable : (prefixWord ++ tailWord_3390231).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3390231).length < 2 ^ (prefixWord ++ tailWord_3390231).sum := by decide
  have hdescent : baseEnd_3390231 < baseStart_3390231 := by decide
  rcases family_descends (prefixWord ++ tailWord_3390231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3390250 : List Nat := [3, 1, 4, 3, 1, 2, 1, 2, 1, 4]
def baseStart_3390250 : Nat := 118140960795 + 3390250 * 2 ^ 59
def prefixEnd_3390250 : Nat := 4983230072969 + 3 ^ 40 * 3390250 * 2
def baseEnd_3390250 : Nat := 1160551859270310576655687

theorem tailTrace_3390250 : CollatzResearch.WordTrace tailWord_3390250 prefixEnd_3390250 1160551859270310576655687 := by
  unfold tailWord_3390250
  simp only [CollatzResearch.WordTrace]
  refine ⟨30913143991927683361970051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82435050645140488965253469 30913143991927683361970051)
  ·
    refine ⟨46369715987891525042955077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30913143991927683361970051 46369715987891525042955077)
    ·
      refine ⟨8694321747729660945554077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46369715987891525042955077 8694321747729660945554077)
      ·
        refine ⟨3260370655398622854582779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8694321747729660945554077 3260370655398622854582779)
        ·
          refine ⟨4890555983097934281874169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3260370655398622854582779 4890555983097934281874169)
          ·
            refine ⟨3667916987323450711405627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4890555983097934281874169 3667916987323450711405627)
            ·
              refine ⟨5501875480985176067108441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3667916987323450711405627 5501875480985176067108441)
              ·
                refine ⟨4126406610738882050331331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5501875480985176067108441 4126406610738882050331331)
                ·
                  refine ⟨6189609916108323075496997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4126406610738882050331331 6189609916108323075496997)
                  ·
                    refine ⟨1160551859270310576655687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6189609916108323075496997 1160551859270310576655687)
                    ·
                      rfl

theorem cell22_3390250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 2, 1, 2, 1, 4].length) (baseStart_3390250 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3390250 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3390250 prefixEnd_3390250 := by exact prefixLift 3390250
  have htrace : WordTrace (prefixWord ++ tailWord_3390250) baseStart_3390250 baseEnd_3390250 := by
    simpa [prefixWord, tailWord_3390250, baseEnd_3390250] using wordTrace_append hprefix tailTrace_3390250
  have hstable : (prefixWord ++ tailWord_3390250).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3390250).length < 2 ^ (prefixWord ++ tailWord_3390250).sum := by decide
  have hdescent : baseEnd_3390250 < baseStart_3390250 := by decide
  rcases family_descends (prefixWord ++ tailWord_3390250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3390261 : List Nat := [1, 3, 3, 1, 3, 2, 2, 1, 2, 4]
def baseStart_3390261 : Nat := 118140960795 + 3390261 * 2 ^ 59
def prefixEnd_3390261 : Nat := 4983230072969 + 3 ^ 40 * 3390261 * 2
def baseEnd_3390261 : Nat := 1160555624795110214630653

theorem tailTrace_3390261 : CollatzResearch.WordTrace tailWord_3390261 prefixEnd_3390261 1160555624795110214630653 := by
  unfold tailWord_3390261
  simp only [CollatzResearch.WordTrace]
  refine ⟨123652977170670882326530637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82435318113780588217687091 123652977170670882326530637)
  ·
    refine ⟨46369866439001580872448989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123652977170670882326530637 46369866439001580872448989)
    ·
      refine ⟨17388699914625592827168371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46369866439001580872448989 17388699914625592827168371)
      ·
        refine ⟨26083049871938389240752557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17388699914625592827168371 26083049871938389240752557)
        ·
          refine ⟨9781143701976895965282209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26083049871938389240752557 9781143701976895965282209)
          ·
            refine ⟨7335857776482671973961657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9781143701976895965282209 7335857776482671973961657)
            ·
              refine ⟨5501893332362003980471243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7335857776482671973961657 5501893332362003980471243)
              ·
                refine ⟨8252839998543005970706865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5501893332362003980471243 8252839998543005970706865)
                ·
                  refine ⟨6189629998907254478030149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8252839998543005970706865 6189629998907254478030149)
                  ·
                    refine ⟨1160555624795110214630653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6189629998907254478030149 1160555624795110214630653)
                    ·
                      rfl

theorem cell22_3390261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 2, 1, 2, 4].length) (baseStart_3390261 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3390261 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3390261 prefixEnd_3390261 := by exact prefixLift 3390261
  have htrace : WordTrace (prefixWord ++ tailWord_3390261) baseStart_3390261 baseEnd_3390261 := by
    simpa [prefixWord, tailWord_3390261, baseEnd_3390261] using wordTrace_append hprefix tailTrace_3390261
  have hstable : (prefixWord ++ tailWord_3390261).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3390261).length < 2 ^ (prefixWord ++ tailWord_3390261).sum := by decide
  have hdescent : baseEnd_3390261 < baseStart_3390261 := by decide
  rcases family_descends (prefixWord ++ tailWord_3390261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3390272 : List Nat := [2, 1, 1, 2, 2, 1, 1, 2, 4, 6]
def baseStart_3390272 : Nat := 118140960795 + 3390272 * 2 ^ 59
def prefixEnd_3390272 : Nat := 4983230072969 + 3 ^ 40 * 3390272 * 2
def baseEnd_3390272 : Nat := 1160559390319909852605619

theorem tailTrace_3390272 : CollatzResearch.WordTrace tailWord_3390272 prefixEnd_3390272 1160559390319909852605619 := by
  unfold tailWord_3390272
  simp only [CollatzResearch.WordTrace]
  refine ⟨61826689186815515602590535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82435585582420687470120713 61826689186815515602590535)
  ·
    refine ⟨92740033780223273403885803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61826689186815515602590535 92740033780223273403885803)
    ·
      refine ⟨139110050670334910105828705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92740033780223273403885803 139110050670334910105828705)
      ·
        refine ⟨104332538002751182579371529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139110050670334910105828705 104332538002751182579371529)
        ·
          refine ⟨78249403502063386934528647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104332538002751182579371529 78249403502063386934528647)
          ·
            refine ⟨117374105253095080401792971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78249403502063386934528647 117374105253095080401792971)
            ·
              refine ⟨176061157879642620602689457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 117374105253095080401792971 176061157879642620602689457)
              ·
                refine ⟨132045868409731965452017093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 176061157879642620602689457 132045868409731965452017093)
                ·
                  refine ⟨24758600326824743522253205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 132045868409731965452017093 24758600326824743522253205)
                  ·
                    refine ⟨1160559390319909852605619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24758600326824743522253205 1160559390319909852605619)
                    ·
                      rfl

theorem cell22_3390272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 2, 4, 6].length) (baseStart_3390272 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3390272 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3390272 prefixEnd_3390272 := by exact prefixLift 3390272
  have htrace : WordTrace (prefixWord ++ tailWord_3390272) baseStart_3390272 baseEnd_3390272 := by
    simpa [prefixWord, tailWord_3390272, baseEnd_3390272] using wordTrace_append hprefix tailTrace_3390272
  have hstable : (prefixWord ++ tailWord_3390272).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3390272).length < 2 ^ (prefixWord ++ tailWord_3390272).sum := by decide
  have hdescent : baseEnd_3390272 < baseStart_3390272 := by decide
  rcases family_descends (prefixWord ++ tailWord_3390272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3390276 : List Nat := [2, 3, 4, 2, 1, 10]
def baseStart_3390276 : Nat := 118140960795 + 3390276 * 2 ^ 59
def prefixEnd_3390276 : Nat := 4983230072969 + 3 ^ 40 * 3390276 * 2
def baseEnd_3390276 : Nat := 14327910612366113277847

theorem tailTrace_3390276 : CollatzResearch.WordTrace tailWord_3390276 prefixEnd_3390276 14327910612366113277847 := by
  unfold tailWord_3390276
  simp only [CollatzResearch.WordTrace]
  refine ⟨61826762132808269944163341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82435682843744359925551121 61826762132808269944163341)
  ·
    refine ⟨23185035799803101229061253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61826762132808269944163341 23185035799803101229061253)
    ·
      refine ⟨4347194212463081480448985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23185035799803101229061253 4347194212463081480448985)
      ·
        refine ⟨3260395659347311110336739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4347194212463081480448985 3260395659347311110336739)
        ·
          refine ⟨4890593489020966665505109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3260395659347311110336739 4890593489020966665505109)
          ·
            refine ⟨14327910612366113277847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 4890593489020966665505109 14327910612366113277847)
            ·
              rfl

theorem cell22_3390276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 10].length) (baseStart_3390276 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3390276 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3390276 prefixEnd_3390276 := by exact prefixLift 3390276
  have htrace : WordTrace (prefixWord ++ tailWord_3390276) baseStart_3390276 baseEnd_3390276 := by
    simpa [prefixWord, tailWord_3390276, baseEnd_3390276] using wordTrace_append hprefix tailTrace_3390276
  have hstable : (prefixWord ++ tailWord_3390276).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3390276).length < 2 ^ (prefixWord ++ tailWord_3390276).sum := by decide
  have hdescent : baseEnd_3390276 < baseStart_3390276 := by decide
  rcases family_descends (prefixWord ++ tailWord_3390276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3390304 : List Nat := [2, 1, 1, 3, 3, 1, 1, 5, 5]
def baseStart_3390304 : Nat := 118140960795 + 3390304 * 2 ^ 59
def prefixEnd_3390304 : Nat := 4983230072969 + 3 ^ 40 * 3390304 * 2
def baseEnd_3390304 : Nat := 386856781524624145268507

theorem tailTrace_3390304 : CollatzResearch.WordTrace tailWord_3390304 prefixEnd_3390304 386856781524624145268507 := by
  unfold tailWord_3390304
  simp only [CollatzResearch.WordTrace]
  refine ⟨61827272754757550335172983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82436363673010067113563977 61827272754757550335172983)
  ·
    refine ⟨92740909132136325502759475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61827272754757550335172983 92740909132136325502759475)
    ·
      refine ⟨139111363698204488254139213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92740909132136325502759475 139111363698204488254139213)
      ·
        refine ⟨52166761386826683095302205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 139111363698204488254139213 52166761386826683095302205)
        ·
          refine ⟨19562535520060006160738327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52166761386826683095302205 19562535520060006160738327)
          ·
            refine ⟨29343803280090009241107491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19562535520060006160738327 29343803280090009241107491)
            ·
              refine ⟨44015704920135013861661237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29343803280090009241107491 44015704920135013861661237)
              ·
                refine ⟨4126472336262657549530741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 44015704920135013861661237 4126472336262657549530741)
                ·
                  refine ⟨386856781524624145268507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4126472336262657549530741 386856781524624145268507)
                  ·
                    rfl

theorem cell22_3390304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 5, 5].length) (baseStart_3390304 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3390304 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3390304 prefixEnd_3390304 := by exact prefixLift 3390304
  have htrace : WordTrace (prefixWord ++ tailWord_3390304) baseStart_3390304 baseEnd_3390304 := by
    simpa [prefixWord, tailWord_3390304, baseEnd_3390304] using wordTrace_append hprefix tailTrace_3390304
  have hstable : (prefixWord ++ tailWord_3390304).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3390304).length < 2 ^ (prefixWord ++ tailWord_3390304).sum := by decide
  have hdescent : baseEnd_3390304 < baseStart_3390304 := by decide
  rcases family_descends (prefixWord ++ tailWord_3390304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3390325 : List Nat := [1, 3, 4, 1, 1, 3, 2, 3, 1, 3]
def baseStart_3390325 : Nat := 118140960795 + 3390325 * 2 ^ 59
def prefixEnd_3390325 : Nat := 4983230072969 + 3 ^ 40 * 3390325 * 2
def baseEnd_3390325 : Nat := 1160577533303035381030457

theorem tailTrace_3390325 : CollatzResearch.WordTrace tailWord_3390325 prefixEnd_3390325 1160577533303035381030457 := by
  unfold tailWord_3390325
  simp only [CollatzResearch.WordTrace]
  refine ⟨123655311442439021256860429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82436874294959347504573619 123655311442439021256860429)
  ·
    refine ⟨46370741790914632971322661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123655311442439021256860429 46370741790914632971322661)
    ·
      refine ⟨8694514085796493682122999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46370741790914632971322661 8694514085796493682122999)
      ·
        refine ⟨13041771128694740523184499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8694514085796493682122999 13041771128694740523184499)
        ·
          refine ⟨19562656693042110784776749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13041771128694740523184499 19562656693042110784776749)
          ·
            refine ⟨7335996259890791544291281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19562656693042110784776749 7335996259890791544291281)
            ·
              refine ⟨5501997194918093658218461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7335996259890791544291281 5501997194918093658218461)
              ·
                refine ⟨2063248948094285121831923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5501997194918093658218461 2063248948094285121831923)
                ·
                  refine ⟨3094873422141427682747885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2063248948094285121831923 3094873422141427682747885)
                  ·
                    refine ⟨1160577533303035381030457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3094873422141427682747885 1160577533303035381030457)
                    ·
                      rfl

theorem cell22_3390325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 2, 3, 1, 3].length) (baseStart_3390325 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3390325 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3390325 prefixEnd_3390325 := by exact prefixLift 3390325
  have htrace : WordTrace (prefixWord ++ tailWord_3390325) baseStart_3390325 baseEnd_3390325 := by
    simpa [prefixWord, tailWord_3390325, baseEnd_3390325] using wordTrace_append hprefix tailTrace_3390325
  have hstable : (prefixWord ++ tailWord_3390325).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3390325).length < 2 ^ (prefixWord ++ tailWord_3390325).sum := by decide
  have hdescent : baseEnd_3390325 < baseStart_3390325 := by decide
  rcases family_descends (prefixWord ++ tailWord_3390325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3390398 : List Nat := [4, 2, 1, 1, 1, 2, 2, 4, 2, 3]
def baseStart_3390398 : Nat := 118140960795 + 3390398 * 2 ^ 59
def prefixEnd_3390398 : Nat := 4983230072969 + 3 ^ 40 * 3390398 * 2
def baseEnd_3390398 : Nat := 1160602522694887523955233

theorem tailTrace_3390398 : CollatzResearch.WordTrace tailWord_3390398 prefixEnd_3390398 1160602522694887523955233 := by
  unfold tailWord_3390398
  simp only [CollatzResearch.WordTrace]
  refine ⟨15457246746396819340533481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 82438649314116369816178565 15457246746396819340533481)
  ·
    refine ⟨11592935059797614505400111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15457246746396819340533481 11592935059797614505400111)
    ·
      refine ⟨17389402589696421758100167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11592935059797614505400111 17389402589696421758100167)
      ·
        refine ⟨26084103884544632637150251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17389402589696421758100167 26084103884544632637150251)
        ·
          refine ⟨39126155826816948955725377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26084103884544632637150251 39126155826816948955725377)
          ·
            refine ⟨29344616870112711716794033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39126155826816948955725377 29344616870112711716794033)
            ·
              refine ⟨22008462652584533787595525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29344616870112711716794033 22008462652584533787595525)
              ·
                refine ⟨4126586747359600085174161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22008462652584533787595525 4126586747359600085174161)
                ·
                  refine ⟨3094940060519700063880621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4126586747359600085174161 3094940060519700063880621)
                  ·
                    refine ⟨1160602522694887523955233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3094940060519700063880621 1160602522694887523955233)
                    ·
                      rfl

theorem cell22_3390398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 2, 4, 2, 3].length) (baseStart_3390398 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3390398 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3390398 prefixEnd_3390398 := by exact prefixLift 3390398
  have htrace : WordTrace (prefixWord ++ tailWord_3390398) baseStart_3390398 baseEnd_3390398 := by
    simpa [prefixWord, tailWord_3390398, baseEnd_3390398] using wordTrace_append hprefix tailTrace_3390398
  have hstable : (prefixWord ++ tailWord_3390398).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3390398).length < 2 ^ (prefixWord ++ tailWord_3390398).sum := by decide
  have hdescent : baseEnd_3390398 < baseStart_3390398 := by decide
  rcases family_descends (prefixWord ++ tailWord_3390398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3390406 : List Nat := [6, 1, 3, 1, 1, 2, 2, 1, 5]
def baseStart_3390406 : Nat := 118140960795 + 3390406 * 2 ^ 59
def prefixEnd_3390406 : Nat := 4983230072969 + 3 ^ 40 * 3390406 * 2
def baseEnd_3390406 : Nat := 386868420419459389918403

theorem tailTrace_3390406 : CollatzResearch.WordTrace tailWord_3390406 prefixEnd_3390406 386868420419459389918403 := by
  unfold tailWord_3390406
  simp only [CollatzResearch.WordTrace]
  refine ⟨3864320804848299127829971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 82438843836763714727039381 3864320804848299127829971)
  ·
    refine ⟨5796481207272448691744957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3864320804848299127829971 5796481207272448691744957)
    ·
      refine ⟨2173680452727168259404359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5796481207272448691744957 2173680452727168259404359)
      ·
        refine ⟨3260520679090752389106539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2173680452727168259404359 3260520679090752389106539)
        ·
          refine ⟨4890781018636128583659809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3260520679090752389106539 4890781018636128583659809)
          ·
            refine ⟨3668085763977096437744857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4890781018636128583659809 3668085763977096437744857)
            ·
              refine ⟨2751064322982822328308643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3668085763977096437744857 2751064322982822328308643)
              ·
                refine ⟨4126596484474233492462965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2751064322982822328308643 4126596484474233492462965)
                ·
                  refine ⟨386868420419459389918403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4126596484474233492462965 386868420419459389918403)
                  ·
                    rfl

theorem cell22_3390406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 2, 2, 1, 5].length) (baseStart_3390406 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3390406 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3390406 prefixEnd_3390406 := by exact prefixLift 3390406
  have htrace : WordTrace (prefixWord ++ tailWord_3390406) baseStart_3390406 baseEnd_3390406 := by
    simpa [prefixWord, tailWord_3390406, baseEnd_3390406] using wordTrace_append hprefix tailTrace_3390406
  have hstable : (prefixWord ++ tailWord_3390406).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3390406).length < 2 ^ (prefixWord ++ tailWord_3390406).sum := by decide
  have hdescent : baseEnd_3390406 < baseStart_3390406 := by decide
  rcases family_descends (prefixWord ++ tailWord_3390406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3390415 : List Nat := [1, 1, 2, 1, 1, 8, 2, 1, 2, 3]
def baseStart_3390415 : Nat := 118140960795 + 3390415 * 2 ^ 59
def prefixEnd_3390415 : Nat := 4983230072969 + 3 ^ 40 * 3390415 * 2
def baseEnd_3390415 : Nat := 1160608342142305146280181

theorem tailTrace_3390415 : CollatzResearch.WordTrace tailWord_3390415 prefixEnd_3390415 1160608342142305146280181 := by
  unfold tailWord_3390415
  simp only [CollatzResearch.WordTrace]
  refine ⟨123658594012112966627636699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82439062674741977751757799 123658594012112966627636699)
  ·
    refine ⟨185487891018169449941455049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123658594012112966627636699 185487891018169449941455049)
    ·
      refine ⟨139115918263627087456091287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 185487891018169449941455049 139115918263627087456091287)
      ·
        refine ⟨208673877395440631184136931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139115918263627087456091287 208673877395440631184136931)
        ·
          refine ⟨313010816093160946776205397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 208673877395440631184136931 313010816093160946776205397)
          ·
            refine ⟨3668095501091729845033657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 313010816093160946776205397 3668095501091729845033657)
            ·
              refine ⟨2751071625818797383775243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3668095501091729845033657 2751071625818797383775243)
              ·
                refine ⟨4126607438728196075662865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2751071625818797383775243 4126607438728196075662865)
                ·
                  refine ⟨3094955579046147056747149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4126607438728196075662865 3094955579046147056747149)
                  ·
                    refine ⟨1160608342142305146280181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3094955579046147056747149 1160608342142305146280181)
                    ·
                      rfl

theorem cell22_3390415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 8, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 8, 2, 1, 2, 3].length) (baseStart_3390415 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3390415 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3390415 prefixEnd_3390415 := by exact prefixLift 3390415
  have htrace : WordTrace (prefixWord ++ tailWord_3390415) baseStart_3390415 baseEnd_3390415 := by
    simpa [prefixWord, tailWord_3390415, baseEnd_3390415] using wordTrace_append hprefix tailTrace_3390415
  have hstable : (prefixWord ++ tailWord_3390415).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3390415).length < 2 ^ (prefixWord ++ tailWord_3390415).sum := by decide
  have hdescent : baseEnd_3390415 < baseStart_3390415 := by decide
  rcases family_descends (prefixWord ++ tailWord_3390415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3390460 : List Nat := [2, 2, 2, 1, 2, 4, 1, 4, 1, 3]
def baseStart_3390460 : Nat := 118140960795 + 3390460 * 2 ^ 59
def prefixEnd_3390460 : Nat := 4983230072969 + 3 ^ 40 * 3390460 * 2
def baseEnd_3390460 : Nat := 1160623746561940028905043

theorem tailTrace_3390460 : CollatzResearch.WordTrace tailWord_3390460 prefixEnd_3390460 1160623746561940028905043 := by
  unfold tailWord_3390460
  simp only [CollatzResearch.WordTrace]
  refine ⟨61830117648474969656512417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82440156864633292875349889 61830117648474969656512417)
  ·
    refine ⟨46372588236356227242384313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61830117648474969656512417 46372588236356227242384313)
    ·
      refine ⟨34779441177267170431788235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46372588236356227242384313 34779441177267170431788235)
      ·
        refine ⟨52169161765900755647682353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34779441177267170431788235 52169161765900755647682353)
        ·
          refine ⟨39126871324425566735761765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52169161765900755647682353 39126871324425566735761765)
          ·
            refine ⟨7336288373329793762955331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39126871324425566735761765 7336288373329793762955331)
            ·
              refine ⟨11004432559994690644432997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7336288373329793762955331 11004432559994690644432997)
              ·
                refine ⟨2063331104999004495831187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11004432559994690644432997 2063331104999004495831187)
                ·
                  refine ⟨3094996657498506743746781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2063331104999004495831187 3094996657498506743746781)
                  ·
                    refine ⟨1160623746561940028905043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3094996657498506743746781 1160623746561940028905043)
                    ·
                      rfl

theorem cell22_3390460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 1, 4, 1, 3].length) (baseStart_3390460 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3390460 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3390460 prefixEnd_3390460 := by exact prefixLift 3390460
  have htrace : WordTrace (prefixWord ++ tailWord_3390460) baseStart_3390460 baseEnd_3390460 := by
    simpa [prefixWord, tailWord_3390460, baseEnd_3390460] using wordTrace_append hprefix tailTrace_3390460
  have hstable : (prefixWord ++ tailWord_3390460).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3390460).length < 2 ^ (prefixWord ++ tailWord_3390460).sum := by decide
  have hdescent : baseEnd_3390460 < baseStart_3390460 := by decide
  rcases family_descends (prefixWord ++ tailWord_3390460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3390471 : List Nat := [1, 1, 4, 3, 1, 1, 3, 1, 2, 5]
def baseStart_3390471 : Nat := 118140960795 + 3390471 * 2 ^ 59
def prefixEnd_3390471 : Nat := 4983230072969 + 3 ^ 40 * 3390471 * 2
def baseEnd_3390471 : Nat := 1160627512086739666880009

theorem tailTrace_3390471 : CollatzResearch.WordTrace tailWord_3390471 prefixEnd_3390471 1160627512086739666880009 := by
  unfold tailWord_3390471
  simp only [CollatzResearch.WordTrace]
  refine ⟨123660636499910088191675267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82440424333273392127783511 123660636499910088191675267)
  ·
    refine ⟨185490954749865132287512901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123660636499910088191675267 185490954749865132287512901)
    ·
      refine ⟨34779554015599712303908669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 185490954749865132287512901 34779554015599712303908669)
      ·
        refine ⟨13042332755849892113965751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34779554015599712303908669 13042332755849892113965751)
        ·
          refine ⟨19563499133774838170948627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13042332755849892113965751 19563499133774838170948627)
          ·
            refine ⟨29345248700662257256422941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19563499133774838170948627 29345248700662257256422941)
            ·
              refine ⟨11004468262748346471158603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29345248700662257256422941 11004468262748346471158603)
              ·
                refine ⟨16506702394122519706737905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11004468262748346471158603 16506702394122519706737905)
                ·
                  refine ⟨12380026795591889780053429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16506702394122519706737905 12380026795591889780053429)
                  ·
                    refine ⟨1160627512086739666880009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12380026795591889780053429 1160627512086739666880009)
                    ·
                      rfl

theorem cell22_3390471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 3, 1, 2, 5].length) (baseStart_3390471 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3390471 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3390471 prefixEnd_3390471 := by exact prefixLift 3390471
  have htrace : WordTrace (prefixWord ++ tailWord_3390471) baseStart_3390471 baseEnd_3390471 := by
    simpa [prefixWord, tailWord_3390471, baseEnd_3390471] using wordTrace_append hprefix tailTrace_3390471
  have hstable : (prefixWord ++ tailWord_3390471).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3390471).length < 2 ^ (prefixWord ++ tailWord_3390471).sum := by decide
  have hdescent : baseEnd_3390471 < baseStart_3390471 := by decide
  rcases family_descends (prefixWord ++ tailWord_3390471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3390518 : List Nat := [5, 1, 2, 1, 1, 2, 1, 3, 6]
def baseStart_3390518 : Nat := 118140960795 + 3390518 * 2 ^ 59
def prefixEnd_3390518 : Nat := 4983230072969 + 3 ^ 40 * 3390518 * 2
def baseEnd_3390518 : Nat := 386881200382415736984955

theorem tailTrace_3390518 : CollatzResearch.WordTrace tailWord_3390518 prefixEnd_3390518 386881200382415736984955 := by
  unfold tailWord_3390518
  simp only [CollatzResearch.WordTrace]
  refine ⟨7728896920671238451164763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 82441567153826543479090805 7728896920671238451164763)
  ·
    refine ⟨11593345381006857676747145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7728896920671238451164763 11593345381006857676747145)
    ·
      refine ⟨8695009035755143257560359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11593345381006857676747145 8695009035755143257560359)
      ·
        refine ⟨13042513553632714886340539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8695009035755143257560359 13042513553632714886340539)
        ·
          refine ⟨19563770330449072329510809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13042513553632714886340539 19563770330449072329510809)
          ·
            refine ⟨14672827747836804247133107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19563770330449072329510809 14672827747836804247133107)
            ·
              refine ⟨22009241621755206370699661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14672827747836804247133107 22009241621755206370699661)
              ·
                refine ⟨8253465608158202389012373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22009241621755206370699661 8253465608158202389012373)
                ·
                  refine ⟨386881200382415736984955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8253465608158202389012373 386881200382415736984955)
                  ·
                    rfl

theorem cell22_3390518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 1, 3, 6].length) (baseStart_3390518 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3390518 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3390518 prefixEnd_3390518 := by exact prefixLift 3390518
  have htrace : WordTrace (prefixWord ++ tailWord_3390518) baseStart_3390518 baseEnd_3390518 := by
    simpa [prefixWord, tailWord_3390518, baseEnd_3390518] using wordTrace_append hprefix tailTrace_3390518
  have hstable : (prefixWord ++ tailWord_3390518).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3390518).length < 2 ^ (prefixWord ++ tailWord_3390518).sum := by decide
  have hdescent : baseEnd_3390518 < baseStart_3390518 := by decide
  rcases family_descends (prefixWord ++ tailWord_3390518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3390533 : List Nat := [1, 3, 1, 1, 1, 3, 2, 5, 2, 3]
def baseStart_3390533 : Nat := 118140960795 + 3390533 * 2 ^ 59
def prefixEnd_3390533 : Nat := 4983230072969 + 3 ^ 40 * 3390533 * 2
def baseEnd_3390533 : Nat := 1160648735953792171829819

theorem tailTrace_3390533 : CollatzResearch.WordTrace tailWord_3390533 prefixEnd_3390533 1160648735953792171829819 := by
  unfold tailWord_3390533
  simp only [CollatzResearch.WordTrace]
  refine ⟨123662897825685472780432253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82441931883790315186954835 123662897825685472780432253)
  ·
    refine ⟨46373586684632052292662095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123662897825685472780432253 46373586684632052292662095)
    ·
      refine ⟨69560380026948078438993143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46373586684632052292662095 69560380026948078438993143)
      ·
        refine ⟨104340570040422117658489715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69560380026948078438993143 104340570040422117658489715)
        ·
          refine ⟨156510855060633176487734573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104340570040422117658489715 156510855060633176487734573)
          ·
            refine ⟨58691570647737441182900465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 156510855060633176487734573 58691570647737441182900465)
            ·
              refine ⟨44018677985803080887175349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58691570647737441182900465 44018677985803080887175349)
              ·
                refine ⟨4126751061169038833172689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 44018677985803080887175349 4126751061169038833172689)
                ·
                  refine ⟨3095063295876779124879517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4126751061169038833172689 3095063295876779124879517)
                  ·
                    refine ⟨1160648735953792171829819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3095063295876779124879517 1160648735953792171829819)
                    ·
                      rfl

theorem cell22_3390533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 5, 2, 3].length) (baseStart_3390533 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3390533 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3390533 prefixEnd_3390533 := by exact prefixLift 3390533
  have htrace : WordTrace (prefixWord ++ tailWord_3390533) baseStart_3390533 baseEnd_3390533 := by
    simpa [prefixWord, tailWord_3390533, baseEnd_3390533] using wordTrace_append hprefix tailTrace_3390533
  have hstable : (prefixWord ++ tailWord_3390533).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3390533).length < 2 ^ (prefixWord ++ tailWord_3390533).sum := by decide
  have hdescent : baseEnd_3390533 < baseStart_3390533 := by decide
  rcases family_descends (prefixWord ++ tailWord_3390533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3390576 : List Nat := [2, 1, 1, 1, 5, 1, 2, 1, 2, 6]
def baseStart_3390576 : Nat := 118140960795 + 3390576 * 2 ^ 59
def prefixEnd_3390576 : Nat := 4983230072969 + 3 ^ 40 * 3390576 * 2
def baseEnd_3390576 : Nat := 1160663455732554393004687

theorem tailTrace_3390576 : CollatzResearch.WordTrace tailWord_3390576 prefixEnd_3390576 1160663455732554393004687 := by
  unfold tailWord_3390576
  simp only [CollatzResearch.WordTrace]
  refine ⟨61832233082264845562123791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82442977443019794082831721 61832233082264845562123791)
  ·
    refine ⟨92748349623397268343185687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61832233082264845562123791 92748349623397268343185687)
    ·
      refine ⟨139122524435095902514778531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92748349623397268343185687 139122524435095902514778531)
      ·
        refine ⟨208683786652643853772167797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139122524435095902514778531 208683786652643853772167797)
        ·
          refine ⟨19564104998685361291140731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 208683786652643853772167797 19564104998685361291140731)
          ·
            refine ⟨29346157498028041936711097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19564104998685361291140731 29346157498028041936711097)
            ·
              refine ⟨22009618123521031452533323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29346157498028041936711097 22009618123521031452533323)
              ·
                refine ⟨33014427185281547178799985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22009618123521031452533323 33014427185281547178799985)
                ·
                  refine ⟨24760820388961160384099989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33014427185281547178799985 24760820388961160384099989)
                  ·
                    refine ⟨1160663455732554393004687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24760820388961160384099989 1160663455732554393004687)
                    ·
                      rfl

theorem cell22_3390576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 2, 1, 2, 6].length) (baseStart_3390576 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3390576 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3390576 prefixEnd_3390576 := by exact prefixLift 3390576
  have htrace : WordTrace (prefixWord ++ tailWord_3390576) baseStart_3390576 baseEnd_3390576 := by
    simpa [prefixWord, tailWord_3390576, baseEnd_3390576] using wordTrace_append hprefix tailTrace_3390576
  have hstable : (prefixWord ++ tailWord_3390576).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3390576).length < 2 ^ (prefixWord ++ tailWord_3390576).sum := by decide
  have hdescent : baseEnd_3390576 < baseStart_3390576 := by decide
  rcases family_descends (prefixWord ++ tailWord_3390576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3390629 : List Nat := [1, 3, 1, 2, 1, 6, 2, 2, 1, 3]
def baseStart_3390629 : Nat := 118140960795 + 3390629 * 2 ^ 59
def prefixEnd_3390629 : Nat := 4983230072969 + 3 ^ 40 * 3390629 * 2
def baseEnd_3390629 : Nat := 1160681598715679921429525

theorem tailTrace_3390629 : CollatzResearch.WordTrace tailWord_3390629 prefixEnd_3390629 1160681598715679921429525 := by
  unfold tailWord_3390629
  simp only [CollatzResearch.WordTrace]
  refine ⟨123666399233337681175926941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82444266155558454117284627 123666399233337681175926941)
  ·
    refine ⟨46374899712501630440972603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123666399233337681175926941 46374899712501630440972603)
    ·
      refine ⟨69562349568752445661458905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46374899712501630440972603 69562349568752445661458905)
      ·
        refine ⟨52171762176564334246094179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69562349568752445661458905 52171762176564334246094179)
        ·
          refine ⟨78257643264846501369141269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52171762176564334246094179 78257643264846501369141269)
          ·
            refine ⟨3668327028039679751678497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 78257643264846501369141269 3668327028039679751678497)
            ·
              refine ⟨2751245271029759813758873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3668327028039679751678497 2751245271029759813758873)
              ·
                refine ⟨2063433953272319860319155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2751245271029759813758873 2063433953272319860319155)
                ·
                  refine ⟨3095150929908479790478733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2063433953272319860319155 3095150929908479790478733)
                  ·
                    refine ⟨1160681598715679921429525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3095150929908479790478733 1160681598715679921429525)
                    ·
                      rfl

theorem cell22_3390629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 6, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 6, 2, 2, 1, 3].length) (baseStart_3390629 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3390629 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3390629 prefixEnd_3390629 := by exact prefixLift 3390629
  have htrace : WordTrace (prefixWord ++ tailWord_3390629) baseStart_3390629 baseEnd_3390629 := by
    simpa [prefixWord, tailWord_3390629, baseEnd_3390629] using wordTrace_append hprefix tailTrace_3390629
  have hstable : (prefixWord ++ tailWord_3390629).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3390629).length < 2 ^ (prefixWord ++ tailWord_3390629).sum := by decide
  have hdescent : baseEnd_3390629 < baseStart_3390629 := by decide
  rcases family_descends (prefixWord ++ tailWord_3390629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3390743 : List Nat := [1, 1, 3, 4, 1, 1, 1, 3, 7]
def baseStart_3390743 : Nat := 118140960795 + 3390743 * 2 ^ 59
def prefixEnd_3390743 : Nat := 4983230072969 + 3 ^ 40 * 3390743 * 2
def baseEnd_3390743 : Nat := 386906874415140541359725

theorem tailTrace_3390743 : CollatzResearch.WordTrace tailWord_3390743 prefixEnd_3390743 386906874415140541359725 := by
  unfold tailWord_3390743
  simp only [CollatzResearch.WordTrace]
  refine ⟨123670557154924678645576883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82447038103283119097051255 123670557154924678645576883)
  ·
    refine ⟨185505835732387017968365325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123670557154924678645576883 185505835732387017968365325)
    ·
      refine ⟨69564688399645131738136997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 185505835732387017968365325 69564688399645131738136997)
      ·
        refine ⟨13043379074933462200900687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 69564688399645131738136997 13043379074933462200900687)
        ·
          refine ⟨19565068612400193301351031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13043379074933462200900687 19565068612400193301351031)
          ·
            refine ⟨29347602918600289952026547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19565068612400193301351031 29347602918600289952026547)
            ·
              refine ⟨44021404377900434928039821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29347602918600289952026547 44021404377900434928039821)
              ·
                refine ⟨16508026641712663098014933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44021404377900434928039821 16508026641712663098014933)
                ·
                  refine ⟨386906874415140541359725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16508026641712663098014933 386906874415140541359725)
                  ·
                    rfl

theorem cell22_3390743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 3, 7].length) (baseStart_3390743 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3390743 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3390743 prefixEnd_3390743 := by exact prefixLift 3390743
  have htrace : WordTrace (prefixWord ++ tailWord_3390743) baseStart_3390743 baseEnd_3390743 := by
    simpa [prefixWord, tailWord_3390743, baseEnd_3390743] using wordTrace_append hprefix tailTrace_3390743
  have hstable : (prefixWord ++ tailWord_3390743).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3390743).length < 2 ^ (prefixWord ++ tailWord_3390743).sum := by decide
  have hdescent : baseEnd_3390743 < baseStart_3390743 := by decide
  rcases family_descends (prefixWord ++ tailWord_3390743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3390803 : List Nat := [1, 1, 1, 2, 1, 1, 5, 2, 3, 5]
def baseStart_3390803 : Nat := 118140960795 + 3390803 * 2 ^ 59
def prefixEnd_3390803 : Nat := 4983230072969 + 3 ^ 40 * 3390803 * 2
def baseEnd_3390803 : Nat := 1160741162471601467578991

theorem tailTrace_3390803 : CollatzResearch.WordTrace tailWord_3390803 prefixEnd_3390803 1160741162471601467578991 := by
  unfold tailWord_3390803
  simp only [CollatzResearch.WordTrace]
  refine ⟨123672745534707308892761063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82448497023138205928507375 123672745534707308892761063)
  ·
    refine ⟨185509118302060963339141595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123672745534707308892761063 185509118302060963339141595)
    ·
      refine ⟨278263677453091445008712393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185509118302060963339141595 278263677453091445008712393)
      ·
        refine ⟨208697758089818583756534295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 278263677453091445008712393 208697758089818583756534295)
        ·
          refine ⟨313046637134727875634801443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 208697758089818583756534295 313046637134727875634801443)
          ·
            refine ⟨469569955702091813452202165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 313046637134727875634801443 469569955702091813452202165)
            ·
              refine ⟨44022183347071107511143953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 469569955702091813452202165 44022183347071107511143953)
              ·
                refine ⟨33016637510303330633357965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44022183347071107511143953 33016637510303330633357965)
                ·
                  refine ⟨12381239066363748987509237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33016637510303330633357965 12381239066363748987509237)
                  ·
                    refine ⟨1160741162471601467578991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12381239066363748987509237 1160741162471601467578991)
                    ·
                      rfl

theorem cell22_3390803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 2, 3, 5].length) (baseStart_3390803 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3390803 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3390803 prefixEnd_3390803 := by exact prefixLift 3390803
  have htrace : WordTrace (prefixWord ++ tailWord_3390803) baseStart_3390803 baseEnd_3390803 := by
    simpa [prefixWord, tailWord_3390803, baseEnd_3390803] using wordTrace_append hprefix tailTrace_3390803
  have hstable : (prefixWord ++ tailWord_3390803).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3390803).length < 2 ^ (prefixWord ++ tailWord_3390803).sum := by decide
  have hdescent : baseEnd_3390803 < baseStart_3390803 := by decide
  rcases family_descends (prefixWord ++ tailWord_3390803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3390820 : List Nat := [2, 3, 1, 1, 3, 2, 1, 3, 1, 5]
def baseStart_3390820 : Nat := 118140960795 + 3390820 * 2 ^ 59
def prefixEnd_3390820 : Nat := 4983230072969 + 3 ^ 40 * 3390820 * 2
def baseEnd_3390820 : Nat := 1160746981919019089903939

theorem tailTrace_3390820 : CollatzResearch.WordTrace tailWord_3390820 prefixEnd_3390820 1160746981919019089903939 := by
  unfold tailWord_3390820
  simp only [CollatzResearch.WordTrace]
  refine ⟨61836682787822860398064957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82448910383763813864086609 61836682787822860398064957)
  ·
    refine ⟨23188756045433572649274359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61836682787822860398064957 23188756045433572649274359)
    ·
      refine ⟨34783134068150358973911539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23188756045433572649274359 34783134068150358973911539)
      ·
        refine ⟨52174701102225538460867309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34783134068150358973911539 52174701102225538460867309)
        ·
          refine ⟨19565512913334576922825241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52174701102225538460867309 19565512913334576922825241)
          ·
            refine ⟨14674134685000932692118931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19565512913334576922825241 14674134685000932692118931)
            ·
              refine ⟨22011202027501399038178397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14674134685000932692118931 22011202027501399038178397)
              ·
                refine ⟨8254200760313024639316899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22011202027501399038178397 8254200760313024639316899)
                ·
                  refine ⟨12381301140469536958975349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8254200760313024639316899 12381301140469536958975349)
                  ·
                    refine ⟨1160746981919019089903939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12381301140469536958975349 1160746981919019089903939)
                    ·
                      rfl

theorem cell22_3390820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 1, 3, 1, 5].length) (baseStart_3390820 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3390820 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3390820 prefixEnd_3390820 := by exact prefixLift 3390820
  have htrace : WordTrace (prefixWord ++ tailWord_3390820) baseStart_3390820 baseEnd_3390820 := by
    simpa [prefixWord, tailWord_3390820, baseEnd_3390820] using wordTrace_append hprefix tailTrace_3390820
  have hstable : (prefixWord ++ tailWord_3390820).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3390820).length < 2 ^ (prefixWord ++ tailWord_3390820).sum := by decide
  have hdescent : baseEnd_3390820 < baseStart_3390820 := by decide
  rcases family_descends (prefixWord ++ tailWord_3390820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3390833 : List Nat := [1, 2, 2, 2, 1, 2, 2, 10]
def baseStart_3390833 : Nat := 118140960795 + 3390833 * 2 ^ 59
def prefixEnd_3390833 : Nat := 4983230072969 + 3 ^ 40 * 3390833 * 2
def baseEnd_3390833 : Nat := 128972381342743487703211

theorem tailTrace_3390833 : CollatzResearch.WordTrace tailWord_3390833 prefixEnd_3390833 128972381342743487703211 := by
  unfold tailWord_3390833
  simp only [CollatzResearch.WordTrace]
  refine ⟨123673839724598624016353153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82449226483065749344235435 123673839724598624016353153)
  ·
    refine ⟨92755379793448968012264865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123673839724598624016353153 92755379793448968012264865)
    ·
      refine ⟨69566534845086726009198649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92755379793448968012264865 69566534845086726009198649)
      ·
        refine ⟨52174901133815044506898987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69566534845086726009198649 52174901133815044506898987)
        ·
          refine ⟨78262351700722566760348481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52174901133815044506898987 78262351700722566760348481)
          ·
            refine ⟨58696763775541925070261361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78262351700722566760348481 58696763775541925070261361)
            ·
              refine ⟨44022572831656443802696021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58696763775541925070261361 44022572831656443802696021)
              ·
                refine ⟨128972381342743487703211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 44022572831656443802696021 128972381342743487703211)
                ·
                  rfl

theorem cell22_3390833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 10].length) (baseStart_3390833 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3390833 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3390833 prefixEnd_3390833 := by exact prefixLift 3390833
  have htrace : WordTrace (prefixWord ++ tailWord_3390833) baseStart_3390833 baseEnd_3390833 := by
    simpa [prefixWord, tailWord_3390833, baseEnd_3390833] using wordTrace_append hprefix tailTrace_3390833
  have hstable : (prefixWord ++ tailWord_3390833).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3390833).length < 2 ^ (prefixWord ++ tailWord_3390833).sum := by decide
  have hdescent : baseEnd_3390833 < baseStart_3390833 := by decide
  rcases family_descends (prefixWord ++ tailWord_3390833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3390848 : List Nat := [2, 1, 1, 2, 1, 2, 1, 2, 1, 9]
def baseStart_3390848 : Nat := 118140960795 + 3390848 * 2 ^ 59
def prefixEnd_3390848 : Nat := 4983230072969 + 3 ^ 40 * 3390848 * 2
def baseEnd_3390848 : Nat := 1160756566891236350203853

theorem tailTrace_3390848 : CollatzResearch.WordTrace tailWord_3390848 prefixEnd_3390848 1160756566891236350203853 := by
  unfold tailWord_3390848
  simp only [CollatzResearch.WordTrace]
  refine ⟨61837193409772140789074599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82449591213029521052099465 61837193409772140789074599)
  ·
    refine ⟨92755790114658211183611899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61837193409772140789074599 92755790114658211183611899)
    ·
      refine ⟨139133685171987316775417849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92755790114658211183611899 139133685171987316775417849)
      ·
        refine ⟨104350263878990487581563387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139133685171987316775417849 104350263878990487581563387)
        ·
          refine ⟨156525395818485731372345081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104350263878990487581563387 156525395818485731372345081)
          ·
            refine ⟨117394046863864298529258811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 156525395818485731372345081 117394046863864298529258811)
            ·
              refine ⟨176091070295796447793888217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 117394046863864298529258811 176091070295796447793888217)
              ·
                refine ⟨132068302721847335845416163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 176091070295796447793888217 132068302721847335845416163)
                ·
                  refine ⟨198102454082771003768124245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 132068302721847335845416163 198102454082771003768124245)
                  ·
                    refine ⟨1160756566891236350203853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 198102454082771003768124245 1160756566891236350203853)
                    ·
                      rfl

theorem cell22_3390848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 2, 1, 9].length) (baseStart_3390848 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3390848 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3390848 prefixEnd_3390848 := by exact prefixLift 3390848
  have htrace : WordTrace (prefixWord ++ tailWord_3390848) baseStart_3390848 baseEnd_3390848 := by
    simpa [prefixWord, tailWord_3390848, baseEnd_3390848] using wordTrace_append hprefix tailTrace_3390848
  have hstable : (prefixWord ++ tailWord_3390848).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3390848).length < 2 ^ (prefixWord ++ tailWord_3390848).sum := by decide
  have hdescent : baseEnd_3390848 < baseStart_3390848 := by decide
  rcases family_descends (prefixWord ++ tailWord_3390848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3390865 : List Nat := [1, 2, 2, 1, 1, 1, 2, 2, 7, 3]
def baseStart_3390865 : Nat := 118140960795 + 3390865 * 2 ^ 59
def prefixEnd_3390865 : Nat := 4983230072969 + 3 ^ 40 * 3390865 * 2
def baseEnd_3390865 : Nat := 1160762386338653972528801

theorem tailTrace_3390865 : CollatzResearch.WordTrace tailWord_3390865 prefixEnd_3390865 1160762386338653972528801 := by
  unfold tailWord_3390865
  simp only [CollatzResearch.WordTrace]
  refine ⟨123675006860482693481518049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82450004573655128987678699 123675006860482693481518049)
  ·
    refine ⟨92756255145362020111138537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123675006860482693481518049 92756255145362020111138537)
    ·
      refine ⟨69567191359021515083353903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92756255145362020111138537 69567191359021515083353903)
      ·
        refine ⟨104350787038532272625030855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69567191359021515083353903 104350787038532272625030855)
        ·
          refine ⟨156526180557798408937546283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104350787038532272625030855 156526180557798408937546283)
          ·
            refine ⟨234789270836697613406319425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 156526180557798408937546283 234789270836697613406319425)
            ·
              refine ⟨176091953127523210054739569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 234789270836697613406319425 176091953127523210054739569)
              ·
                refine ⟨132068964845642407541054677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 176091953127523210054739569 132068964845642407541054677)
                ·
                  refine ⟨3095366363569743926743469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 132068964845642407541054677 3095366363569743926743469)
                  ·
                    refine ⟨1160762386338653972528801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3095366363569743926743469 1160762386338653972528801)
                    ·
                      rfl

theorem cell22_3390865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 2, 7, 3].length) (baseStart_3390865 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3390865 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3390865 prefixEnd_3390865 := by exact prefixLift 3390865
  have htrace : WordTrace (prefixWord ++ tailWord_3390865) baseStart_3390865 baseEnd_3390865 := by
    simpa [prefixWord, tailWord_3390865, baseEnd_3390865] using wordTrace_append hprefix tailTrace_3390865
  have hstable : (prefixWord ++ tailWord_3390865).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3390865).length < 2 ^ (prefixWord ++ tailWord_3390865).sum := by decide
  have hdescent : baseEnd_3390865 < baseStart_3390865 := by decide
  rcases family_descends (prefixWord ++ tailWord_3390865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3390916 : List Nat := [2, 3, 3, 2, 1, 3, 1, 1, 3, 3]
def baseStart_3390916 : Nat := 118140960795 + 3390916 * 2 ^ 59
def prefixEnd_3390916 : Nat := 4983230072969 + 3 ^ 40 * 3390916 * 2
def baseEnd_3390916 : Nat := 1160779844680906839503645

theorem tailTrace_3390916 : CollatzResearch.WordTrace tailWord_3390916 prefixEnd_3390916 1160779844680906839503645 := by
  unfold tailWord_3390916
  simp only [CollatzResearch.WordTrace]
  refine ⟨61838433491648964595812301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82451244655531952794416401 61838433491648964595812301)
  ·
    refine ⟨23189412559368361723429613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61838433491648964595812301 23189412559368361723429613)
    ·
      refine ⟨8696029709763135646286105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23189412559368361723429613 8696029709763135646286105)
      ·
        refine ⟨6522022282322351734714579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8696029709763135646286105 6522022282322351734714579)
        ·
          refine ⟨9783033423483527602071869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6522022282322351734714579 9783033423483527602071869)
          ·
            refine ⟨3668637533806322850776951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9783033423483527602071869 3668637533806322850776951)
            ·
              refine ⟨5502956300709484276165427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3668637533806322850776951 5502956300709484276165427)
              ·
                refine ⟨8254434451064226414248141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5502956300709484276165427 8254434451064226414248141)
                ·
                  refine ⟨3095412919149084905343053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8254434451064226414248141 3095412919149084905343053)
                  ·
                    refine ⟨1160779844680906839503645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3095412919149084905343053 1160779844680906839503645)
                    ·
                      rfl

theorem cell22_3390916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 3, 1, 1, 3, 3].length) (baseStart_3390916 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3390916 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3390916 prefixEnd_3390916 := by exact prefixLift 3390916
  have htrace : WordTrace (prefixWord ++ tailWord_3390916) baseStart_3390916 baseEnd_3390916 := by
    simpa [prefixWord, tailWord_3390916, baseEnd_3390916] using wordTrace_append hprefix tailTrace_3390916
  have hstable : (prefixWord ++ tailWord_3390916).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3390916).length < 2 ^ (prefixWord ++ tailWord_3390916).sum := by decide
  have hdescent : baseEnd_3390916 < baseStart_3390916 := by decide
  rcases family_descends (prefixWord ++ tailWord_3390916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3390972 : List Nat := [2, 2, 2, 1, 2, 1, 2, 3, 4, 3]
def baseStart_3390972 : Nat := 118140960795 + 3390972 * 2 ^ 59
def prefixEnd_3390972 : Nat := 4983230072969 + 3 ^ 40 * 3390972 * 2
def baseEnd_3390972 : Nat := 1160799014625341360103473

theorem tailTrace_3390972 : CollatzResearch.WordTrace tailWord_3390972 prefixEnd_3390972 1160799014625341360103473 := by
  unfold tailWord_3390972
  simp only [CollatzResearch.WordTrace]
  refine ⟨61839454735547525377831585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82452606314063367170442113 61839454735547525377831585)
  ·
    refine ⟨46379591051660644033373689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61839454735547525377831585 46379591051660644033373689)
    ·
      refine ⟨34784693288745483025030267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46379591051660644033373689 34784693288745483025030267)
      ·
        refine ⟨52177039933118224537545401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34784693288745483025030267 52177039933118224537545401)
        ·
          refine ⟨39132779949838668403159051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52177039933118224537545401 39132779949838668403159051)
          ·
            refine ⟨58699169924758002604738577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39132779949838668403159051 58699169924758002604738577)
            ·
              refine ⟨44024377443568501953553933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58699169924758002604738577 44024377443568501953553933)
              ·
                refine ⟨16509141541338188232582725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44024377443568501953553933 16509141541338188232582725)
                ·
                  refine ⟨3095464039000910293609261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16509141541338188232582725 3095464039000910293609261)
                  ·
                    refine ⟨1160799014625341360103473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3095464039000910293609261 1160799014625341360103473)
                    ·
                      rfl

theorem cell22_3390972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 3, 4, 3].length) (baseStart_3390972 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3390972 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3390972 prefixEnd_3390972 := by exact prefixLift 3390972
  have htrace : WordTrace (prefixWord ++ tailWord_3390972) baseStart_3390972 baseEnd_3390972 := by
    simpa [prefixWord, tailWord_3390972, baseEnd_3390972] using wordTrace_append hprefix tailTrace_3390972
  have hstable : (prefixWord ++ tailWord_3390972).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3390972).length < 2 ^ (prefixWord ++ tailWord_3390972).sum := by decide
  have hdescent : baseEnd_3390972 < baseStart_3390972 := by decide
  rcases family_descends (prefixWord ++ tailWord_3390972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3391034 : List Nat := [3, 1, 1, 1, 3, 2, 4, 1, 3, 3]
def baseStart_3391034 : Nat := 118140960795 + 3391034 * 2 ^ 59
def prefixEnd_3391034 : Nat := 4983230072969 + 3 ^ 40 * 3391034 * 2
def baseEnd_3391034 : Nat := 1160820238492393865053283

theorem tailTrace_3391034 : CollatzResearch.WordTrace tailWord_3391034 prefixEnd_3391034 1160820238492393865053283 := by
  unfold tailWord_3391034
  simp only [CollatzResearch.WordTrace]
  refine ⟨30920292699217608836105039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82454113864580290229613437 30920292699217608836105039)
  ·
    refine ⟨46380439048826413254157559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30920292699217608836105039 46380439048826413254157559)
    ·
      refine ⟨69570658573239619881236339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46380439048826413254157559 69570658573239619881236339)
      ·
        refine ⟨104355987859859429821854509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69570658573239619881236339 104355987859859429821854509)
        ·
          refine ⟨39133495447447286183195441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 104355987859859429821854509 39133495447447286183195441)
          ·
            refine ⟨29350121585585464637396581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39133495447447286183195441 29350121585585464637396581)
            ·
              refine ⟨5503147797297274619511859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29350121585585464637396581 5503147797297274619511859)
              ·
                refine ⟨8254721695945911929267789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5503147797297274619511859 8254721695945911929267789)
                ·
                  refine ⟨3095520635979716973475421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8254721695945911929267789 3095520635979716973475421)
                  ·
                    refine ⟨1160820238492393865053283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3095520635979716973475421 1160820238492393865053283)
                    ·
                      rfl

theorem cell22_3391034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 4, 1, 3, 3].length) (baseStart_3391034 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3391034 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3391034 prefixEnd_3391034 := by exact prefixLift 3391034
  have htrace : WordTrace (prefixWord ++ tailWord_3391034) baseStart_3391034 baseEnd_3391034 := by
    simpa [prefixWord, tailWord_3391034, baseEnd_3391034] using wordTrace_append hprefix tailTrace_3391034
  have hstable : (prefixWord ++ tailWord_3391034).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3391034).length < 2 ^ (prefixWord ++ tailWord_3391034).sum := by decide
  have hdescent : baseEnd_3391034 < baseStart_3391034 := by decide
  rcases family_descends (prefixWord ++ tailWord_3391034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3391053 : List Nat := [1, 6, 1, 1, 4, 1, 2, 6]
def baseStart_3391053 : Nat := 118140960795 + 3391053 * 2 ^ 59
def prefixEnd_3391053 : Nat := 4983230072969 + 3 ^ 40 * 3391053 * 2
def baseEnd_3391053 : Nat := 128980749175631572092025

theorem tailTrace_3391053 : CollatzResearch.WordTrace tailWord_3391053 prefixEnd_3391053 128980749175631572092025 := by
  unfold tailWord_3391053
  simp only [CollatzResearch.WordTrace]
  refine ⟨123681863783801601589361813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82454575855867734392907875 123681863783801601589361813)
  ·
    refine ⟨5797587364865700074501335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 123681863783801601589361813 5797587364865700074501335)
    ·
      refine ⟨8696381047298550111752003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5797587364865700074501335 8696381047298550111752003)
      ·
        refine ⟨13044571570947825167628005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8696381047298550111752003 13044571570947825167628005)
        ·
          refine ⟨2445857169552717218930251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13044571570947825167628005 2445857169552717218930251)
          ·
            refine ⟨3668785754329075828395377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2445857169552717218930251 3668785754329075828395377)
            ·
              refine ⟨2751589315746806871296533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3668785754329075828395377 2751589315746806871296533)
              ·
                refine ⟨128980749175631572092025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2751589315746806871296533 128980749175631572092025)
                ·
                  rfl

theorem cell22_3391053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 4, 1, 2, 6].length) (baseStart_3391053 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3391053 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3391053 prefixEnd_3391053 := by exact prefixLift 3391053
  have htrace : WordTrace (prefixWord ++ tailWord_3391053) baseStart_3391053 baseEnd_3391053 := by
    simpa [prefixWord, tailWord_3391053, baseEnd_3391053] using wordTrace_append hprefix tailTrace_3391053
  have hstable : (prefixWord ++ tailWord_3391053).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3391053).length < 2 ^ (prefixWord ++ tailWord_3391053).sum := by decide
  have hdescent : baseEnd_3391053 < baseStart_3391053 := by decide
  rcases family_descends (prefixWord ++ tailWord_3391053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3391068 : List Nat := [2, 2, 4, 1, 2, 1, 3, 3, 1, 3]
def baseStart_3391068 : Nat := 118140960795 + 3391068 * 2 ^ 59
def prefixEnd_3391068 : Nat := 4983230072969 + 3 ^ 40 * 3391068 * 2
def baseEnd_3391068 : Nat := 1160831877387229109703179

theorem tailTrace_3391068 : CollatzResearch.WordTrace tailWord_3391068 prefixEnd_3391068 1160831877387229109703179 := by
  unfold tailWord_3391068
  simp only [CollatzResearch.WordTrace]
  refine ⟨61841205439373629575578929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82454940585831506100771905 61841205439373629575578929)
  ·
    refine ⟨46380904079530222181684197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61841205439373629575578929 46380904079530222181684197)
    ·
      refine ⟨8696419514911916659065787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46380904079530222181684197 8696419514911916659065787)
      ·
        refine ⟨13044629272367874988598681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8696419514911916659065787 13044629272367874988598681)
        ·
          refine ⟨9783471954275906241449011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13044629272367874988598681 9783471954275906241449011)
          ·
            refine ⟨14675207931413859362173517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9783471954275906241449011 14675207931413859362173517)
            ·
              refine ⟨5503202974280197260815069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14675207931413859362173517 5503202974280197260815069)
              ·
                refine ⟨2063701115355073972805651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5503202974280197260815069 2063701115355073972805651)
                ·
                  refine ⟨3095551673032610959208477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2063701115355073972805651 3095551673032610959208477)
                  ·
                    refine ⟨1160831877387229109703179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3095551673032610959208477 1160831877387229109703179)
                    ·
                      rfl

theorem cell22_3391068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 3, 3, 1, 3].length) (baseStart_3391068 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3391068 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3391068 prefixEnd_3391068 := by exact prefixLift 3391068
  have htrace : WordTrace (prefixWord ++ tailWord_3391068) baseStart_3391068 baseEnd_3391068 := by
    simpa [prefixWord, tailWord_3391068, baseEnd_3391068] using wordTrace_append hprefix tailTrace_3391068
  have hstable : (prefixWord ++ tailWord_3391068).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3391068).length < 2 ^ (prefixWord ++ tailWord_3391068).sum := by decide
  have hdescent : baseEnd_3391068 < baseStart_3391068 := by decide
  rcases family_descends (prefixWord ++ tailWord_3391068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3391085 : List Nat := [1, 5, 1, 1, 4, 1, 3, 2, 1, 3]
def baseStart_3391085 : Nat := 118140960795 + 3391085 * 2 ^ 59
def prefixEnd_3391085 : Nat := 4983230072969 + 3 ^ 40 * 3391085 * 2
def baseEnd_3391085 : Nat := 1160837696834646732028127

theorem tailTrace_3391085 : CollatzResearch.WordTrace tailWord_3391085 prefixEnd_3391085 1160837696834646732028127 := by
  unfold tailWord_3391085
  simp only [CollatzResearch.WordTrace]
  refine ⟨123683030919685671054526709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82455353946457114036351139 123683030919685671054526709)
  ·
    refine ⟨11595284148720531661361879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 123683030919685671054526709 11595284148720531661361879)
    ·
      refine ⟨17392926223080797492042819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11595284148720531661361879 17392926223080797492042819)
      ·
        refine ⟨26089389334621196238064229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17392926223080797492042819 26089389334621196238064229)
        ·
          refine ⟨4891760500241474294637043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26089389334621196238064229 4891760500241474294637043)
          ·
            refine ⟨7337640750362211441955565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4891760500241474294637043 7337640750362211441955565)
            ·
              refine ⟨2751615281385829290733337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7337640750362211441955565 2751615281385829290733337)
              ·
                refine ⟨2063711461039371968050003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2751615281385829290733337 2063711461039371968050003)
                ·
                  refine ⟨3095567191559057952075005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2063711461039371968050003 3095567191559057952075005)
                  ·
                    refine ⟨1160837696834646732028127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3095567191559057952075005 1160837696834646732028127)
                    ·
                      rfl

theorem cell22_3391085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 3, 2, 1, 3].length) (baseStart_3391085 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3391085 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3391085 prefixEnd_3391085 := by exact prefixLift 3391085
  have htrace : WordTrace (prefixWord ++ tailWord_3391085) baseStart_3391085 baseEnd_3391085 := by
    simpa [prefixWord, tailWord_3391085, baseEnd_3391085] using wordTrace_append hprefix tailTrace_3391085
  have hstable : (prefixWord ++ tailWord_3391085).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3391085).length < 2 ^ (prefixWord ++ tailWord_3391085).sum := by decide
  have hdescent : baseEnd_3391085 < baseStart_3391085 := by decide
  rcases family_descends (prefixWord ++ tailWord_3391085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3391107 : List Nat := [1, 1, 1, 3, 3, 1, 1, 5, 1, 5]
def baseStart_3391107 : Nat := 118140960795 + 3391107 * 2 ^ 59
def prefixEnd_3391107 : Nat := 4983230072969 + 3 ^ 40 * 3391107 * 2
def baseEnd_3391107 : Nat := 1160845227884246007978059

theorem tailTrace_3391107 : CollatzResearch.WordTrace tailWord_3391107 prefixEnd_3391107 1160845227884246007978059 := by
  unfold tailWord_3391107
  simp only [CollatzResearch.WordTrace]
  refine ⟨123683833325605968811827575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82455888883737312541218383 123683833325605968811827575)
  ·
    refine ⟨185525749988408953217741363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123683833325605968811827575 185525749988408953217741363)
    ·
      refine ⟨278288624982613429826612045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185525749988408953217741363 278288624982613429826612045)
      ·
        refine ⟨104358234368480036184979517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 278288624982613429826612045 104358234368480036184979517)
        ·
          refine ⟨39134337888180013569367319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 104358234368480036184979517 39134337888180013569367319)
          ·
            refine ⟨58701506832270020354050979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39134337888180013569367319 58701506832270020354050979)
            ·
              refine ⟨88052260248405030531076469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58701506832270020354050979 88052260248405030531076469)
              ·
                refine ⟨8254899398287971612288419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 88052260248405030531076469 8254899398287971612288419)
                ·
                  refine ⟨12382349097431957418432629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8254899398287971612288419 12382349097431957418432629)
                  ·
                    refine ⟨1160845227884246007978059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12382349097431957418432629 1160845227884246007978059)
                    ·
                      rfl

theorem cell22_3391107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 5, 1, 5].length) (baseStart_3391107 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3391107 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3391107 prefixEnd_3391107 := by exact prefixLift 3391107
  have htrace : WordTrace (prefixWord ++ tailWord_3391107) baseStart_3391107 baseEnd_3391107 := by
    simpa [prefixWord, tailWord_3391107, baseEnd_3391107] using wordTrace_append hprefix tailTrace_3391107
  have hstable : (prefixWord ++ tailWord_3391107).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3391107).length < 2 ^ (prefixWord ++ tailWord_3391107).sum := by decide
  have hdescent : baseEnd_3391107 < baseStart_3391107 := by decide
  rcases family_descends (prefixWord ++ tailWord_3391107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3391111 : List Nat := [1, 1, 4, 2, 1, 5, 1, 2, 1, 4]
def baseStart_3391111 : Nat := 118140960795 + 3391111 * 2 ^ 59
def prefixEnd_3391111 : Nat := 4983230072969 + 3 ^ 40 * 3391111 * 2
def baseEnd_3391111 : Nat := 1160846597165991330878047

theorem tailTrace_3391111 : CollatzResearch.WordTrace tailWord_3391111 prefixEnd_3391111 1160846597165991330878047 := by
  unfold tailWord_3391111
  simp only [CollatzResearch.WordTrace]
  refine ⟨123683979217591477494973187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82455986145060984996648791 123683979217591477494973187)
  ·
    refine ⟨185525968826387216242459781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123683979217591477494973187 185525968826387216242459781)
    ·
      refine ⟨34786119154947603045461209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 185525968826387216242459781 34786119154947603045461209)
      ·
        refine ⟨26089589366210702284095907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34786119154947603045461209 26089589366210702284095907)
        ·
          refine ⟨39134384049316053426143861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26089589366210702284095907 39134384049316053426143861)
          ·
            refine ⟨3668848504623380008700987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 39134384049316053426143861 3668848504623380008700987)
            ·
              refine ⟨5503272756935070013051481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3668848504623380008700987 5503272756935070013051481)
              ·
                refine ⟨4127454567701302509788611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5503272756935070013051481 4127454567701302509788611)
                ·
                  refine ⟨6191181851551953764682917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4127454567701302509788611 6191181851551953764682917)
                  ·
                    refine ⟨1160846597165991330878047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6191181851551953764682917 1160846597165991330878047)
                    ·
                      rfl

theorem cell22_3391111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 5, 1, 2, 1, 4].length) (baseStart_3391111 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3391111 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3391111 prefixEnd_3391111 := by exact prefixLift 3391111
  have htrace : WordTrace (prefixWord ++ tailWord_3391111) baseStart_3391111 baseEnd_3391111 := by
    simpa [prefixWord, tailWord_3391111, baseEnd_3391111] using wordTrace_append hprefix tailTrace_3391111
  have hstable : (prefixWord ++ tailWord_3391111).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3391111).length < 2 ^ (prefixWord ++ tailWord_3391111).sum := by decide
  have hdescent : baseEnd_3391111 < baseStart_3391111 := by decide
  rcases family_descends (prefixWord ++ tailWord_3391111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3391137 : List Nat := [1, 2, 3, 3, 2, 11]
def baseStart_3391137 : Nat := 118140960795 + 3391137 * 2 ^ 59
def prefixEnd_3391137 : Nat := 4983230072969 + 3 ^ 40 * 3391137 * 2
def baseEnd_3391137 : Nat := 14331549351818962095407

theorem tailTrace_3391137 : CollatzResearch.WordTrace tailWord_3391137 prefixEnd_3391137 14331549351818962095407 := by
  unfold tailWord_3391137
  simp only [CollatzResearch.WordTrace]
  refine ⟨123684927515497283935419665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82456618343664855956946443 123684927515497283935419665)
  ·
    refine ⟨92763695636622962951564749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123684927515497283935419665 92763695636622962951564749)
    ·
      refine ⟨34786385863733611106836781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92763695636622962951564749 34786385863733611106836781)
      ·
        refine ⟨13044894698900104165063793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34786385863733611106836781 13044894698900104165063793)
        ·
          refine ⟨9783671024175078123797845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13044894698900104165063793 9783671024175078123797845)
          ·
            refine ⟨14331549351818962095407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 9783671024175078123797845 14331549351818962095407)
            ·
              rfl

theorem cell22_3391137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 11].length) (baseStart_3391137 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3391137 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3391137 prefixEnd_3391137 := by exact prefixLift 3391137
  have htrace : WordTrace (prefixWord ++ tailWord_3391137) baseStart_3391137 baseEnd_3391137 := by
    simpa [prefixWord, tailWord_3391137, baseEnd_3391137] using wordTrace_append hprefix tailTrace_3391137
  have hstable : (prefixWord ++ tailWord_3391137).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3391137).length < 2 ^ (prefixWord ++ tailWord_3391137).sum := by decide
  have hdescent : baseEnd_3391137 < baseStart_3391137 := by decide
  rcases family_descends (prefixWord ++ tailWord_3391137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3391158 : List Nat := [5, 1, 3, 1, 1, 2, 2, 1, 1, 5]
def baseStart_3391158 : Nat := 118140960795 + 3391158 * 2 ^ 59
def prefixEnd_3391158 : Nat := 4983230072969 + 3 ^ 40 * 3391158 * 2
def baseEnd_3391158 : Nat := 1160862686226498874952903

theorem tailTrace_3391158 : CollatzResearch.WordTrace tailWord_3391158 prefixEnd_3391158 1160862686226498874952903 := by
  unfold tailWord_3391158
  simp only [CollatzResearch.WordTrace]
  refine ⟨7730355840526325282620883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 82457128965614136347956085 7730355840526325282620883)
  ·
    refine ⟨11595533760789487923931325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7730355840526325282620883 11595533760789487923931325)
    ·
      refine ⟨4348325160296057971474247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11595533760789487923931325 4348325160296057971474247)
      ·
        refine ⟨6522487740444086957211371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4348325160296057971474247 6522487740444086957211371)
        ·
          refine ⟨9783731610666130435817057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6522487740444086957211371 9783731610666130435817057)
          ·
            refine ⟨7337798707999597826862793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9783731610666130435817057 7337798707999597826862793)
            ·
              refine ⟨5503349030999698370147095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7337798707999597826862793 5503349030999698370147095)
              ·
                refine ⟨8255023546499547555220643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5503349030999698370147095 8255023546499547555220643)
                ·
                  refine ⟨12382535319749321332830965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8255023546499547555220643 12382535319749321332830965)
                  ·
                    refine ⟨1160862686226498874952903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12382535319749321332830965 1160862686226498874952903)
                    ·
                      rfl

theorem cell22_3391158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 2, 1, 1, 5].length) (baseStart_3391158 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3391158 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3391158 prefixEnd_3391158 := by exact prefixLift 3391158
  have htrace : WordTrace (prefixWord ++ tailWord_3391158) baseStart_3391158 baseEnd_3391158 := by
    simpa [prefixWord, tailWord_3391158, baseEnd_3391158] using wordTrace_append hprefix tailTrace_3391158
  have hstable : (prefixWord ++ tailWord_3391158).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3391158).length < 2 ^ (prefixWord ++ tailWord_3391158).sum := by decide
  have hdescent : baseEnd_3391158 < baseStart_3391158 := by decide
  rcases family_descends (prefixWord ++ tailWord_3391158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3391167 : List Nat := [1, 1, 2, 2, 2, 3, 1, 2, 2, 6]
def baseStart_3391167 : Nat := 118140960795 + 3391167 * 2 ^ 59
def prefixEnd_3391167 : Nat := 4983230072969 + 3 ^ 40 * 3391167 * 2
def baseEnd_3391167 : Nat := 1160865767110425851477875

theorem tailTrace_3391167 : CollatzResearch.WordTrace tailWord_3391167 prefixEnd_3391167 1160865767110425851477875 := by
  unfold tailWord_3391167
  simp only [CollatzResearch.WordTrace]
  refine ⟨123686021705388599059011755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82457347803592399372674503 123686021705388599059011755)
  ·
    refine ⟨185529032558082898588517633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123686021705388599059011755 185529032558082898588517633)
    ·
      refine ⟨139146774418562173941388225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 185529032558082898588517633 139146774418562173941388225)
      ·
        refine ⟨104360080813921630456041169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139146774418562173941388225 104360080813921630456041169)
        ·
          refine ⟨78270060610441222842030877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104360080813921630456041169 78270060610441222842030877)
          ·
            refine ⟨29351272728915458565761579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78270060610441222842030877 29351272728915458565761579)
            ·
              refine ⟨44026909093373187848642369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29351272728915458565761579 44026909093373187848642369)
              ·
                refine ⟨33020181820029890886481777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44026909093373187848642369 33020181820029890886481777)
                ·
                  refine ⟨24765136365022418164861333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33020181820029890886481777 24765136365022418164861333)
                  ·
                    refine ⟨1160865767110425851477875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24765136365022418164861333 1160865767110425851477875)
                    ·
                      rfl

theorem cell22_3391167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 2, 2, 6].length) (baseStart_3391167 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3391167 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3391167 prefixEnd_3391167 := by exact prefixLift 3391167
  have htrace : WordTrace (prefixWord ++ tailWord_3391167) baseStart_3391167 baseEnd_3391167 := by
    simpa [prefixWord, tailWord_3391167, baseEnd_3391167] using wordTrace_append hprefix tailTrace_3391167
  have hstable : (prefixWord ++ tailWord_3391167).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3391167).length < 2 ^ (prefixWord ++ tailWord_3391167).sum := by decide
  have hdescent : baseEnd_3391167 < baseStart_3391167 := by decide
  rcases family_descends (prefixWord ++ tailWord_3391167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3391203 : List Nat := [1, 1, 1, 7, 2, 1, 2, 1, 3, 3]
def baseStart_3391203 : Nat := 118140960795 + 3391203 * 2 ^ 59
def prefixEnd_3391203 : Nat := 4983230072969 + 3 ^ 40 * 3391203 * 2
def baseEnd_3391203 : Nat := 1160878090646133757577765

theorem tailTrace_3391203 : CollatzResearch.WordTrace tailWord_3391203 prefixEnd_3391203 1160878090646133757577765 := by
  unfold tailWord_3391203
  simp only [CollatzResearch.WordTrace]
  refine ⟨123687334733258177207322263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82458223155505451471548175 123687334733258177207322263)
  ·
    refine ⟨185531002099887265810983395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123687334733258177207322263 185531002099887265810983395)
    ·
      refine ⟨278296503149830898716475093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185531002099887265810983395 278296503149830898716475093)
      ·
        refine ⟨6522574292574161688667385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 278296503149830898716475093 6522574292574161688667385)
        ·
          refine ⟨4891930719430621266500539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6522574292574161688667385 4891930719430621266500539)
          ·
            refine ⟨7337896079145931899750809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4891930719430621266500539 7337896079145931899750809)
            ·
              refine ⟨5503422059359448924813107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7337896079145931899750809 5503422059359448924813107)
              ·
                refine ⟨8255133089039173387219661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5503422059359448924813107 8255133089039173387219661)
                ·
                  refine ⟨3095674908389690020207373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8255133089039173387219661 3095674908389690020207373)
                  ·
                    refine ⟨1160878090646133757577765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3095674908389690020207373 1160878090646133757577765)
                    ·
                      rfl

theorem cell22_3391203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 2, 1, 3, 3].length) (baseStart_3391203 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3391203 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3391203 prefixEnd_3391203 := by exact prefixLift 3391203
  have htrace : WordTrace (prefixWord ++ tailWord_3391203) baseStart_3391203 baseEnd_3391203 := by
    simpa [prefixWord, tailWord_3391203, baseEnd_3391203] using wordTrace_append hprefix tailTrace_3391203
  have hstable : (prefixWord ++ tailWord_3391203).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3391203).length < 2 ^ (prefixWord ++ tailWord_3391203).sum := by decide
  have hdescent : baseEnd_3391203 < baseStart_3391203 := by decide
  rcases family_descends (prefixWord ++ tailWord_3391203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3391214 : List Nat := [4, 1, 2, 1, 1, 2, 1, 3, 2, 5]
def baseStart_3391214 : Nat := 118140960795 + 3391214 * 2 ^ 59
def prefixEnd_3391214 : Nat := 4983230072969 + 3 ^ 40 * 3391214 * 2
def baseEnd_3391214 : Nat := 1160881856170933395552731

theorem tailTrace_3391214 : CollatzResearch.WordTrace tailWord_3391214 prefixEnd_3391214 1160881856170933395552731 := by
  unfold tailWord_3391214
  simp only [CollatzResearch.WordTrace]
  refine ⟨15460966992027290760746587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 82458490624145550723981797 15460966992027290760746587)
  ·
    refine ⟨23191450488040936141119881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15460966992027290760746587 23191450488040936141119881)
    ·
      refine ⟨17393587866030702105839911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23191450488040936141119881 17393587866030702105839911)
      ·
        refine ⟨26090381799046053158759867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17393587866030702105839911 26090381799046053158759867)
        ·
          refine ⟨39135572698569079738139801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26090381799046053158759867 39135572698569079738139801)
          ·
            refine ⟨29351679523926809803604851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39135572698569079738139801 29351679523926809803604851)
            ·
              refine ⟨44027519285890214705407277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29351679523926809803604851 44027519285890214705407277)
              ·
                refine ⟨16510319732208830514527729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44027519285890214705407277 16510319732208830514527729)
                ·
                  refine ⟨12382739799156622885895797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16510319732208830514527729 12382739799156622885895797)
                  ·
                    refine ⟨1160881856170933395552731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12382739799156622885895797 1160881856170933395552731)
                    ·
                      rfl

theorem cell22_3391214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 3, 2, 5].length) (baseStart_3391214 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3391214 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3391214 prefixEnd_3391214 := by exact prefixLift 3391214
  have htrace : WordTrace (prefixWord ++ tailWord_3391214) baseStart_3391214 baseEnd_3391214 := by
    simpa [prefixWord, tailWord_3391214, baseEnd_3391214] using wordTrace_append hprefix tailTrace_3391214
  have hstable : (prefixWord ++ tailWord_3391214).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3391214).length < 2 ^ (prefixWord ++ tailWord_3391214).sum := by decide
  have hdescent : baseEnd_3391214 < baseStart_3391214 := by decide
  rcases family_descends (prefixWord ++ tailWord_3391214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3391220 : List Nat := [2, 6, 1, 1, 1, 1, 2, 2, 3, 3]
def baseStart_3391220 : Nat := 118140960795 + 3391220 * 2 ^ 59
def prefixEnd_3391220 : Nat := 4983230072969 + 3 ^ 40 * 3391220 * 2
def baseEnd_3391220 : Nat := 1160883910093551379902713

theorem tailTrace_3391220 : CollatzResearch.WordTrace tailWord_3391220 prefixEnd_3391220 1160883910093551379902713 := by
  unfold tailWord_3391220
  simp only [CollatzResearch.WordTrace]
  refine ⟨61843977387098294555345557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82458636516131059407127409 61843977387098294555345557)
  ·
    refine ⟨2898936440020232557281823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 61843977387098294555345557 2898936440020232557281823)
    ·
      refine ⟨4348404660030348835922735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2898936440020232557281823 4348404660030348835922735)
      ·
        refine ⟨6522606990045523253884103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4348404660030348835922735 6522606990045523253884103)
        ·
          refine ⟨9783910485068284880826155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6522606990045523253884103 9783910485068284880826155)
          ·
            refine ⟨14675865727602427321239233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9783910485068284880826155 14675865727602427321239233)
            ·
              refine ⟨11006899295701820490929425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14675865727602427321239233 11006899295701820490929425)
              ·
                refine ⟨8255174471776365368197069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11006899295701820490929425 8255174471776365368197069)
                ·
                  refine ⟨3095690426916137013073901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8255174471776365368197069 3095690426916137013073901)
                  ·
                    refine ⟨1160883910093551379902713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3095690426916137013073901 1160883910093551379902713)
                    ·
                      rfl

theorem cell22_3391220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 2, 2, 3, 3].length) (baseStart_3391220 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3391220 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3391220 prefixEnd_3391220 := by exact prefixLift 3391220
  have htrace : WordTrace (prefixWord ++ tailWord_3391220) baseStart_3391220 baseEnd_3391220 := by
    simpa [prefixWord, tailWord_3391220, baseEnd_3391220] using wordTrace_append hprefix tailTrace_3391220
  have hstable : (prefixWord ++ tailWord_3391220).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3391220).length < 2 ^ (prefixWord ++ tailWord_3391220).sum := by decide
  have hdescent : baseEnd_3391220 < baseStart_3391220 := by decide
  rcases family_descends (prefixWord ++ tailWord_3391220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3391227 : List Nat := [1, 1, 1, 1, 1, 3, 1, 5, 8]
def baseStart_3391227 : Nat := 118140960795 + 3391227 * 2 ^ 59
def prefixEnd_3391227 : Nat := 4983230072969 + 3 ^ 40 * 3391227 * 2
def baseEnd_3391227 : Nat := 386962102112201898325897

theorem tailTrace_3391227 : CollatzResearch.WordTrace tailWord_3391227 prefixEnd_3391227 386962102112201898325897 := by
  unfold tailWord_3391227
  simp only [CollatzResearch.WordTrace]
  refine ⟨123688210085171229306195935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82458806723447486204130623 123688210085171229306195935)
  ·
    refine ⟨185532315127756843959293903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123688210085171229306195935 185532315127756843959293903)
    ·
      refine ⟨278298472691635265938940855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185532315127756843959293903 278298472691635265938940855)
      ·
        refine ⟨417447709037452898908411283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 278298472691635265938940855 417447709037452898908411283)
        ·
          refine ⟨626171563556179348362616925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 417447709037452898908411283 626171563556179348362616925)
          ·
            refine ⟨234814336333567255635981347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 626171563556179348362616925 234814336333567255635981347)
            ·
              refine ⟨352221504500350883453972021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 234814336333567255635981347 352221504500350883453972021)
              ·
                refine ⟨33020766046907895323809877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 352221504500350883453972021 33020766046907895323809877)
                ·
                  refine ⟨386962102112201898325897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 33020766046907895323809877 386962102112201898325897)
                  ·
                    rfl

theorem cell22_3391227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 5, 8].length) (baseStart_3391227 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3391227 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3391227 prefixEnd_3391227 := by exact prefixLift 3391227
  have htrace : WordTrace (prefixWord ++ tailWord_3391227) baseStart_3391227 baseEnd_3391227 := by
    simpa [prefixWord, tailWord_3391227, baseEnd_3391227] using wordTrace_append hprefix tailTrace_3391227
  have hstable : (prefixWord ++ tailWord_3391227).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3391227).length < 2 ^ (prefixWord ++ tailWord_3391227).sum := by decide
  have hdescent : baseEnd_3391227 < baseStart_3391227 := by decide
  rcases family_descends (prefixWord ++ tailWord_3391227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3391246 : List Nat := [4, 1, 1, 2, 1, 1, 4, 3, 1, 4]
def baseStart_3391246 : Nat := 118140960795 + 3391246 * 2 ^ 59
def prefixEnd_3391246 : Nat := 4983230072969 + 3 ^ 40 * 3391246 * 2
def baseEnd_3391246 : Nat := 1160892810424895978752633

theorem tailTrace_3391246 : CollatzResearch.WordTrace tailWord_3391246 prefixEnd_3391246 1160892810424895978752633 := by
  unfold tailWord_3391246
  simp only [CollatzResearch.WordTrace]
  refine ⟨15461112884012799443892199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 82459268714734930367425061 15461112884012799443892199)
  ·
    refine ⟨23191669326019199165838299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15461112884012799443892199 23191669326019199165838299)
    ·
      refine ⟨34787503989028798748757449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23191669326019199165838299 34787503989028798748757449)
      ·
        refine ⟨26090627991771599061568087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34787503989028798748757449 26090627991771599061568087)
        ·
          refine ⟨39135941987657398592352131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26090627991771599061568087 39135941987657398592352131)
          ·
            refine ⟨58703912981486097888528197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39135941987657398592352131 58703912981486097888528197)
            ·
              refine ⟨11006983684028643354099037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 58703912981486097888528197 11006983684028643354099037)
              ·
                refine ⟨4127618881510741257787139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11006983684028643354099037 4127618881510741257787139)
                ·
                  refine ⟨6191428322266111886680709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4127618881510741257787139 6191428322266111886680709)
                  ·
                    refine ⟨1160892810424895978752633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6191428322266111886680709 1160892810424895978752633)
                    ·
                      rfl

theorem cell22_3391246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 4, 3, 1, 4].length) (baseStart_3391246 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3391246 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3391246 prefixEnd_3391246 := by exact prefixLift 3391246
  have htrace : WordTrace (prefixWord ++ tailWord_3391246) baseStart_3391246 baseEnd_3391246 := by
    simpa [prefixWord, tailWord_3391246, baseEnd_3391246] using wordTrace_append hprefix tailTrace_3391246
  have hstable : (prefixWord ++ tailWord_3391246).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3391246).length < 2 ^ (prefixWord ++ tailWord_3391246).sum := by decide
  have hdescent : baseEnd_3391246 < baseStart_3391246 := by decide
  rcases family_descends (prefixWord ++ tailWord_3391246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3391321 : List Nat := [1, 2, 1, 2, 2, 3, 2, 3, 3, 3]
def baseStart_3391321 : Nat := 118140960795 + 3391321 * 2 ^ 59
def prefixEnd_3391321 : Nat := 4983230072969 + 3 ^ 40 * 3391321 * 2
def baseEnd_3391321 : Nat := 1160918484457620783127403

theorem tailTrace_3391321 : CollatzResearch.WordTrace tailWord_3391321 prefixEnd_3391321 1160918484457620783127403 := by
  unfold tailWord_3391321
  simp only [CollatzResearch.WordTrace]
  refine ⟨123691638546830683360117817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82461092364553788906745211 123691638546830683360117817)
  ·
    refine ⟨92768728910123012520088363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123691638546830683360117817 92768728910123012520088363)
    ·
      refine ⟨139153093365184518780132545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92768728910123012520088363 139153093365184518780132545)
      ·
        refine ⟨104364820023888389085099409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139153093365184518780132545 104364820023888389085099409)
        ·
          refine ⟨78273615017916291813824557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104364820023888389085099409 78273615017916291813824557)
          ·
            refine ⟨29352605631718609430184209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78273615017916291813824557 29352605631718609430184209)
            ·
              refine ⟨22014454223788957072638157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29352605631718609430184209 22014454223788957072638157)
              ·
                refine ⟨8255420333920858902239309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22014454223788957072638157 8255420333920858902239309)
                ·
                  refine ⟨3095782625220322088339741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8255420333920858902239309 3095782625220322088339741)
                  ·
                    refine ⟨1160918484457620783127403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3095782625220322088339741 1160918484457620783127403)
                    ·
                      rfl

theorem cell22_3391321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 2, 3, 3, 3].length) (baseStart_3391321 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3391321 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3391321 prefixEnd_3391321 := by exact prefixLift 3391321
  have htrace : WordTrace (prefixWord ++ tailWord_3391321) baseStart_3391321 baseEnd_3391321 := by
    simpa [prefixWord, tailWord_3391321, baseEnd_3391321] using wordTrace_append hprefix tailTrace_3391321
  have hstable : (prefixWord ++ tailWord_3391321).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3391321).length < 2 ^ (prefixWord ++ tailWord_3391321).sum := by decide
  have hdescent : baseEnd_3391321 < baseStart_3391321 := by decide
  rcases family_descends (prefixWord ++ tailWord_3391321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3391396 : List Nat := [2, 3, 1, 2, 1, 3, 2, 2, 6]
def baseStart_3391396 : Nat := 118140960795 + 3391396 * 2 ^ 59
def prefixEnd_3391396 : Nat := 4983230072969 + 3 ^ 40 * 3391396 * 2
def baseEnd_3391396 : Nat := 386981386163448529167391

theorem tailTrace_3391396 : CollatzResearch.WordTrace tailWord_3391396 prefixEnd_3391396 386981386163448529167391 := by
  unfold tailWord_3391396
  simp only [CollatzResearch.WordTrace]
  refine ⟨61847187010779485584549021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82462916014372647446065361 61847187010779485584549021)
  ·
    refine ⟨23192695129042307094205883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61847187010779485584549021 23192695129042307094205883)
    ·
      refine ⟨34789042693563460641308825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23192695129042307094205883 34789042693563460641308825)
      ·
        refine ⟨26091782020172595480981619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34789042693563460641308825 26091782020172595480981619)
        ·
          refine ⟨39137673030258893221472429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26091782020172595480981619 39137673030258893221472429)
          ·
            refine ⟨14676627386347084958052161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39137673030258893221472429 14676627386347084958052161)
            ·
              refine ⟨11007470539760313718539121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14676627386347084958052161 11007470539760313718539121)
              ·
                refine ⟨8255602904820235288904341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11007470539760313718539121 8255602904820235288904341)
                ·
                  refine ⟨386981386163448529167391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8255602904820235288904341 386981386163448529167391)
                  ·
                    rfl

theorem cell22_3391396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 2, 2, 6].length) (baseStart_3391396 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3391396 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3391396 prefixEnd_3391396 := by exact prefixLift 3391396
  have htrace : WordTrace (prefixWord ++ tailWord_3391396) baseStart_3391396 baseEnd_3391396 := by
    simpa [prefixWord, tailWord_3391396, baseEnd_3391396] using wordTrace_append hprefix tailTrace_3391396
  have hstable : (prefixWord ++ tailWord_3391396).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3391396).length < 2 ^ (prefixWord ++ tailWord_3391396).sum := by decide
  have hdescent : baseEnd_3391396 < baseStart_3391396 := by decide
  rcases family_descends (prefixWord ++ tailWord_3391396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3391411 : List Nat := [1, 1, 1, 2, 3, 1, 3, 1, 6, 3]
def baseStart_3391411 : Nat := 118140960795 + 3391411 * 2 ^ 59
def prefixEnd_3391411 : Nat := 4983230072969 + 3 ^ 40 * 3391411 * 2
def baseEnd_3391411 : Nat := 1160949293296890548377127

theorem tailTrace_3391411 : CollatzResearch.WordTrace tailWord_3391411 prefixEnd_3391411 1160949293296890548377127 := by
  unfold tailWord_3391411
  simp only [CollatzResearch.WordTrace]
  refine ⟨123694921116504628730894087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82463280744336419153929391 123694921116504628730894087)
  ·
    refine ⟨185542381674756943096341131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123694921116504628730894087 185542381674756943096341131)
    ·
      refine ⟨278313572512135414644511697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185542381674756943096341131 278313572512135414644511697)
      ·
        refine ⟨208735179384101560983383773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 278313572512135414644511697 208735179384101560983383773)
        ·
          refine ⟨78275692269038085368768915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 208735179384101560983383773 78275692269038085368768915)
          ·
            refine ⟨117413538403557128053153373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78275692269038085368768915 117413538403557128053153373)
            ·
              refine ⟨44030076901333923019932515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 117413538403557128053153373 44030076901333923019932515)
              ·
                refine ⟨66045115352000884529898773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44030076901333923019932515 66045115352000884529898773)
                ·
                  refine ⟨3095864782125041462339005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 66045115352000884529898773 3095864782125041462339005)
                  ·
                    refine ⟨1160949293296890548377127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3095864782125041462339005 1160949293296890548377127)
                    ·
                      rfl

theorem cell22_3391411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 1, 6, 3].length) (baseStart_3391411 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3391411 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3391411 prefixEnd_3391411 := by exact prefixLift 3391411
  have htrace : WordTrace (prefixWord ++ tailWord_3391411) baseStart_3391411 baseEnd_3391411 := by
    simpa [prefixWord, tailWord_3391411, baseEnd_3391411] using wordTrace_append hprefix tailTrace_3391411
  have hstable : (prefixWord ++ tailWord_3391411).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3391411).length < 2 ^ (prefixWord ++ tailWord_3391411).sum := by decide
  have hdescent : baseEnd_3391411 < baseStart_3391411 := by decide
  rcases family_descends (prefixWord ++ tailWord_3391411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3391445 : List Nat := [1, 3, 2, 3, 2, 2, 1, 3, 2, 3]
def baseStart_3391445 : Nat := 118140960795 + 3391445 * 2 ^ 59
def prefixEnd_3391445 : Nat := 4983230072969 + 3 ^ 40 * 3391445 * 2
def baseEnd_3391445 : Nat := 1160960932191725793027023

theorem tailTrace_3391445 : CollatzResearch.WordTrace tailWord_3391445 prefixEnd_3391445 1160960932191725793027023 := by
  unfold tailWord_3391445
  simp only [CollatzResearch.WordTrace]
  refine ⟨123696161198381452537631789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82464107465587635025087859 123696161198381452537631789)
  ·
    refine ⟨46386060449393044701611921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123696161198381452537631789 46386060449393044701611921)
    ·
      refine ⟨34789545337044783526208941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46386060449393044701611921 34789545337044783526208941)
      ·
        refine ⟨13046079501391793822328353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34789545337044783526208941 13046079501391793822328353)
        ·
          refine ⟨9784559626043845366746265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13046079501391793822328353 9784559626043845366746265)
          ·
            refine ⟨7338419719532884025059699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9784559626043845366746265 7338419719532884025059699)
            ·
              refine ⟨11007629579299326037589549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7338419719532884025059699 11007629579299326037589549)
              ·
                refine ⟨4127861092237247264096081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11007629579299326037589549 4127861092237247264096081)
                ·
                  refine ⟨3095895819177935448072061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4127861092237247264096081 3095895819177935448072061)
                  ·
                    refine ⟨1160960932191725793027023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3095895819177935448072061 1160960932191725793027023)
                    ·
                      rfl

theorem cell22_3391445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 1, 3, 2, 3].length) (baseStart_3391445 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3391445 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3391445 prefixEnd_3391445 := by exact prefixLift 3391445
  have htrace : WordTrace (prefixWord ++ tailWord_3391445) baseStart_3391445 baseEnd_3391445 := by
    simpa [prefixWord, tailWord_3391445, baseEnd_3391445] using wordTrace_append hprefix tailTrace_3391445
  have hstable : (prefixWord ++ tailWord_3391445).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3391445).length < 2 ^ (prefixWord ++ tailWord_3391445).sum := by decide
  have hdescent : baseEnd_3391445 < baseStart_3391445 := by decide
  rcases family_descends (prefixWord ++ tailWord_3391445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3391492 : List Nat := [2, 3, 2, 4, 2, 1, 1, 7]
def baseStart_3391492 : Nat := 118140960795 + 3391492 * 2 ^ 59
def prefixEnd_3391492 : Nat := 4983230072969 + 3 ^ 40 * 3391492 * 2
def baseEnd_3391492 : Nat := 128997446805803704122431

theorem tailTrace_3391492 : CollatzResearch.WordTrace tailWord_3391492 prefixEnd_3391492 128997446805803704122431 := by
  unfold tailWord_3391492
  simp only [CollatzResearch.WordTrace]
  refine ⟨61848937714605589782296365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82465250286140786376395153 61848937714605589782296365)
  ·
    refine ⟨23193351642977096168361137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61848937714605589782296365 23193351642977096168361137)
    ·
      refine ⟨17395013732232822126270853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23193351642977096168361137 17395013732232822126270853)
      ·
        refine ⟨3261565074793654148675785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17395013732232822126270853 3261565074793654148675785)
        ·
          refine ⟨2446173806095240611506839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3261565074793654148675785 2446173806095240611506839)
          ·
            refine ⟨3669260709142860917260259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2446173806095240611506839 3669260709142860917260259)
            ·
              refine ⟨5503891063714291375890389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3669260709142860917260259 5503891063714291375890389)
              ·
                refine ⟨128997446805803704122431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5503891063714291375890389 128997446805803704122431)
                ·
                  rfl

theorem cell22_3391492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 2, 1, 1, 7].length) (baseStart_3391492 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3391492 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3391492 prefixEnd_3391492 := by exact prefixLift 3391492
  have htrace : WordTrace (prefixWord ++ tailWord_3391492) baseStart_3391492 baseEnd_3391492 := by
    simpa [prefixWord, tailWord_3391492, baseEnd_3391492] using wordTrace_append hprefix tailTrace_3391492
  have hstable : (prefixWord ++ tailWord_3391492).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3391492).length < 2 ^ (prefixWord ++ tailWord_3391492).sum := by decide
  have hdescent : baseEnd_3391492 < baseStart_3391492 := by decide
  rcases family_descends (prefixWord ++ tailWord_3391492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3391524 : List Nat := [2, 3, 1, 4, 2, 1, 2, 3, 1, 3]
def baseStart_3391524 : Nat := 118140960795 + 3391524 * 2 ^ 59
def prefixEnd_3391524 : Nat := 4983230072969 + 3 ^ 40 * 3391524 * 2
def baseEnd_3391524 : Nat := 1160987975506195920301781

theorem tailTrace_3391524 : CollatzResearch.WordTrace tailWord_3391524 prefixEnd_3391524 1160987975506195920301781 := by
  unfold tailWord_3391524
  simp only [CollatzResearch.WordTrace]
  refine ⟨61849521282547624514878813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82466028376730166019838417 61849521282547624514878813)
  ·
    refine ⟨23193570480955359193079555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61849521282547624514878813 23193570480955359193079555)
    ·
      refine ⟨34790355721433038789619333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23193570480955359193079555 34790355721433038789619333)
      ·
        refine ⟨6523191697768694773053625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34790355721433038789619333 6523191697768694773053625)
        ·
          refine ⟨4892393773326521079790219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6523191697768694773053625 4892393773326521079790219)
          ·
            refine ⟨7338590659989781619685329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4892393773326521079790219 7338590659989781619685329)
            ·
              refine ⟨5503942994992336214763997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7338590659989781619685329 5503942994992336214763997)
              ·
                refine ⟨2063978623122126080536499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5503942994992336214763997 2063978623122126080536499)
                ·
                  refine ⟨3095967934683189120804749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2063978623122126080536499 3095967934683189120804749)
                  ·
                    refine ⟨1160987975506195920301781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3095967934683189120804749 1160987975506195920301781)
                    ·
                      rfl

theorem cell22_3391524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 2, 3, 1, 3].length) (baseStart_3391524 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3391524 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3391524 prefixEnd_3391524 := by exact prefixLift 3391524
  have htrace : WordTrace (prefixWord ++ tailWord_3391524) baseStart_3391524 baseEnd_3391524 := by
    simpa [prefixWord, tailWord_3391524, baseEnd_3391524] using wordTrace_append hprefix tailTrace_3391524
  have hstable : (prefixWord ++ tailWord_3391524).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3391524).length < 2 ^ (prefixWord ++ tailWord_3391524).sum := by decide
  have hdescent : baseEnd_3391524 < baseStart_3391524 := by decide
  rcases family_descends (prefixWord ++ tailWord_3391524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3391548 : List Nat := [2, 2, 2, 2, 2, 1, 4, 1, 6]
def baseStart_3391548 : Nat := 118140960795 + 3391548 * 2 ^ 59
def prefixEnd_3391548 : Nat := 4983230072969 + 3 ^ 40 * 3391548 * 2
def baseEnd_3391548 : Nat := 386998730398889285900569

theorem tailTrace_3391548 : CollatzResearch.WordTrace tailWord_3391548 prefixEnd_3391548 386998730398889285900569 := by
  unfold tailWord_3391548
  simp only [CollatzResearch.WordTrace]
  refine ⟨61849958958504150564315649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82466611944672200752420865 61849958958504150564315649)
  ·
    refine ⟨46387469218878112923236737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61849958958504150564315649 46387469218878112923236737)
    ·
      refine ⟨34790601914158584692427553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46387469218878112923236737 34790601914158584692427553)
      ·
        refine ⟨26092951435618938519320665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34790601914158584692427553 26092951435618938519320665)
        ·
          refine ⟨19569713576714203889490499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26092951435618938519320665 19569713576714203889490499)
          ·
            refine ⟨29354570365071305834235749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19569713576714203889490499 29354570365071305834235749)
            ·
              refine ⟨5503981943450869843919203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29354570365071305834235749 5503981943450869843919203)
              ·
                refine ⟨8255972915176304765878805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5503981943450869843919203 8255972915176304765878805)
                ·
                  refine ⟨386998730398889285900569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8255972915176304765878805 386998730398889285900569)
                  ·
                    rfl

theorem cell22_3391548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 4, 1, 6].length) (baseStart_3391548 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3391548 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3391548 prefixEnd_3391548 := by exact prefixLift 3391548
  have htrace : WordTrace (prefixWord ++ tailWord_3391548) baseStart_3391548 baseEnd_3391548 := by
    simpa [prefixWord, tailWord_3391548, baseEnd_3391548] using wordTrace_append hprefix tailTrace_3391548
  have hstable : (prefixWord ++ tailWord_3391548).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3391548).length < 2 ^ (prefixWord ++ tailWord_3391548).sum := by decide
  have hdescent : baseEnd_3391548 < baseStart_3391548 := by decide
  rcases family_descends (prefixWord ++ tailWord_3391548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3391561 : List Nat := [1, 2, 1, 1, 2, 2, 3, 1, 3, 6]
def baseStart_3391561 : Nat := 118140960795 + 3391561 * 2 ^ 59
def prefixEnd_3391561 : Nat := 4983230072969 + 3 ^ 40 * 3391561 * 2
def baseEnd_3391561 : Nat := 1161000641362340157126667

theorem tailTrace_3391561 : CollatzResearch.WordTrace tailWord_3391561 prefixEnd_3391561 1161000641362340157126667 := by
  unfold tailWord_3391561
  simp only [CollatzResearch.WordTrace]
  refine ⟨123700392065961204348854537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82466928043974136232569691 123700392065961204348854537)
  ·
    refine ⟨92775294049470903261640903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123700392065961204348854537 92775294049470903261640903)
    ·
      refine ⟨139162941074206354892461355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92775294049470903261640903 139162941074206354892461355)
      ·
        refine ⟨208744411611309532338692033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139162941074206354892461355 208744411611309532338692033)
        ·
          refine ⟨156558308708482149254019025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 208744411611309532338692033 156558308708482149254019025)
          ·
            refine ⟨117418731531361611940514269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 156558308708482149254019025 117418731531361611940514269)
            ·
              refine ⟨44032024324260604477692851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 117418731531361611940514269 44032024324260604477692851)
              ·
                refine ⟨66048036486390906716539277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44032024324260604477692851 66048036486390906716539277)
                ·
                  refine ⟨24768013682396590018702229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 66048036486390906716539277 24768013682396590018702229)
                  ·
                    refine ⟨1161000641362340157126667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24768013682396590018702229 1161000641362340157126667)
                    ·
                      rfl

theorem cell22_3391561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 1, 3, 6].length) (baseStart_3391561 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3391561 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3391561 prefixEnd_3391561 := by exact prefixLift 3391561
  have htrace : WordTrace (prefixWord ++ tailWord_3391561) baseStart_3391561 baseEnd_3391561 := by
    simpa [prefixWord, tailWord_3391561, baseEnd_3391561] using wordTrace_append hprefix tailTrace_3391561
  have hstable : (prefixWord ++ tailWord_3391561).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3391561).length < 2 ^ (prefixWord ++ tailWord_3391561).sum := by decide
  have hdescent : baseEnd_3391561 < baseStart_3391561 := by decide
  rcases family_descends (prefixWord ++ tailWord_3391561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3391578 : List Nat := [3, 1, 1, 2, 1, 1, 4, 3, 2, 4]
def baseStart_3391578 : Nat := 118140960795 + 3391578 * 2 ^ 59
def prefixEnd_3391578 : Nat := 4983230072969 + 3 ^ 40 * 3391578 * 2
def baseEnd_3391578 : Nat := 1161006460809757779451615

theorem tailTrace_3391578 : CollatzResearch.WordTrace tailWord_3391578 prefixEnd_3391578 1161006460809757779451615 := by
  unfold tailWord_3391578
  simp only [CollatzResearch.WordTrace]
  refine ⟨30925253026724904063055847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82467341404599744168148925 30925253026724904063055847)
  ·
    refine ⟨46387879540087356094583771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30925253026724904063055847 46387879540087356094583771)
    ·
      refine ⟨69581819310131034141875657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46387879540087356094583771 69581819310131034141875657)
      ·
        refine ⟨52186364482598275606406743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69581819310131034141875657 52186364482598275606406743)
        ·
          refine ⟨78279546723897413409610115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52186364482598275606406743 78279546723897413409610115)
          ·
            refine ⟨117419320085846120114415173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78279546723897413409610115 117419320085846120114415173)
            ·
              refine ⟨22016122516096147521452845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 117419320085846120114415173 22016122516096147521452845)
              ·
                refine ⟨8256045943536055320544817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22016122516096147521452845 8256045943536055320544817)
                ·
                  refine ⟨6192034457652041490408613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8256045943536055320544817 6192034457652041490408613)
                  ·
                    refine ⟨1161006460809757779451615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6192034457652041490408613 1161006460809757779451615)
                    ·
                      rfl

theorem cell22_3391578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 4, 3, 2, 4].length) (baseStart_3391578 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3391578 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3391578 prefixEnd_3391578 := by exact prefixLift 3391578
  have htrace : WordTrace (prefixWord ++ tailWord_3391578) baseStart_3391578 baseEnd_3391578 := by
    simpa [prefixWord, tailWord_3391578, baseEnd_3391578] using wordTrace_append hprefix tailTrace_3391578
  have hstable : (prefixWord ++ tailWord_3391578).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3391578).length < 2 ^ (prefixWord ++ tailWord_3391578).sum := by decide
  have hdescent : baseEnd_3391578 < baseStart_3391578 := by decide
  rcases family_descends (prefixWord ++ tailWord_3391578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3391580 : List Nat := [2, 2, 4, 1, 1, 2, 1, 2, 4, 3]
def baseStart_3391580 : Nat := 118140960795 + 3391580 * 2 ^ 59
def prefixEnd_3391580 : Nat := 4983230072969 + 3 ^ 40 * 3391580 * 2
def baseEnd_3391580 : Nat := 1161007145450630440901609

theorem tailTrace_3391580 : CollatzResearch.WordTrace tailWord_3391580 prefixEnd_3391580 1161007145450630440901609 := by
  unfold tailWord_3391580
  simp only [CollatzResearch.WordTrace]
  refine ⟨61850542526446185296898097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82467390035261580395864129 61850542526446185296898097)
  ·
    refine ⟨46387906894834638972673573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61850542526446185296898097 46387906894834638972673573)
    ·
      refine ⟨8697732542781494807376295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46387906894834638972673573 8697732542781494807376295)
      ·
        refine ⟨13046598814172242211064443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8697732542781494807376295 13046598814172242211064443)
        ·
          refine ⟨19569898221258363316596665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13046598814172242211064443 19569898221258363316596665)
          ·
            refine ⟨14677423665943772487447499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19569898221258363316596665 14677423665943772487447499)
            ·
              refine ⟨22016135498915658731171249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14677423665943772487447499 22016135498915658731171249)
              ·
                refine ⟨16512101624186744048378437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22016135498915658731171249 16512101624186744048378437)
                ·
                  refine ⟨3096019054535014509070957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16512101624186744048378437 3096019054535014509070957)
                  ·
                    refine ⟨1161007145450630440901609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3096019054535014509070957 1161007145450630440901609)
                    ·
                      rfl

theorem cell22_3391580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 1, 2, 4, 3].length) (baseStart_3391580 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3391580 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3391580 prefixEnd_3391580 := by exact prefixLift 3391580
  have htrace : WordTrace (prefixWord ++ tailWord_3391580) baseStart_3391580 baseEnd_3391580 := by
    simpa [prefixWord, tailWord_3391580, baseEnd_3391580] using wordTrace_append hprefix tailTrace_3391580
  have hstable : (prefixWord ++ tailWord_3391580).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3391580).length < 2 ^ (prefixWord ++ tailWord_3391580).sum := by decide
  have hdescent : baseEnd_3391580 < baseStart_3391580 := by decide
  rcases family_descends (prefixWord ++ tailWord_3391580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3391653 : List Nat := [1, 3, 1, 2, 1, 3, 2, 2, 2, 5]
def baseStart_3391653 : Nat := 118140960795 + 3391653 * 2 ^ 59
def prefixEnd_3391653 : Nat := 4983230072969 + 3 ^ 40 * 3391653 * 2
def baseEnd_3391653 : Nat := 1161032134842482583826385

theorem tailTrace_3391653 : CollatzResearch.WordTrace tailWord_3391653 prefixEnd_3391653 1161032134842482583826385 := by
  unfold tailWord_3391653
  simp only [CollatzResearch.WordTrace]
  refine ⟨123703747581627904061203613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82469165054418602707469075 123703747581627904061203613)
  ·
    refine ⟨46388905343110464022951355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123703747581627904061203613 46388905343110464022951355)
    ·
      refine ⟨69583358014665696034427033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46388905343110464022951355 69583358014665696034427033)
      ·
        refine ⟨52187518510999272025820275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69583358014665696034427033 52187518510999272025820275)
        ·
          refine ⟨78281277766498908038730413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52187518510999272025820275 78281277766498908038730413)
          ·
            refine ⟨29355479162437090514523905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78281277766498908038730413 29355479162437090514523905)
            ·
              refine ⟨22016609371827817885892929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29355479162437090514523905 22016609371827817885892929)
              ·
                refine ⟨16512457028870863414419697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22016609371827817885892929 16512457028870863414419697)
                ·
                  refine ⟨12384342771653147560814773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16512457028870863414419697 12384342771653147560814773)
                  ·
                    refine ⟨1161032134842482583826385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12384342771653147560814773 1161032134842482583826385)
                    ·
                      rfl

theorem cell22_3391653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 2, 2, 2, 5].length) (baseStart_3391653 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3391653 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3391653 prefixEnd_3391653 := by exact prefixLift 3391653
  have htrace : WordTrace (prefixWord ++ tailWord_3391653) baseStart_3391653 baseEnd_3391653 := by
    simpa [prefixWord, tailWord_3391653, baseEnd_3391653] using wordTrace_append hprefix tailTrace_3391653
  have hstable : (prefixWord ++ tailWord_3391653).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3391653).length < 2 ^ (prefixWord ++ tailWord_3391653).sum := by decide
  have hdescent : baseEnd_3391653 < baseStart_3391653 := by decide
  rcases family_descends (prefixWord ++ tailWord_3391653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3391717 : List Nat := [1, 3, 1, 4, 2, 1, 2, 4, 4]
def baseStart_3391717 : Nat := 118140960795 + 3391717 * 2 ^ 59
def prefixEnd_3391717 : Nat := 4983230072969 + 3 ^ 40 * 3391717 * 2
def baseEnd_3391717 : Nat := 387018014450135916742063

theorem tailTrace_3391717 : CollatzResearch.WordTrace tailWord_3391717 prefixEnd_3391717 387018014450135916742063 := by
  unfold tailWord_3391717
  simp only [CollatzResearch.WordTrace]
  refine ⟨123706081853396042991533405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82470721235597361994355603 123706081853396042991533405)
  ·
    refine ⟨46389780695023516121825027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123706081853396042991533405 46389780695023516121825027)
    ·
      refine ⟨69584671042535274182737541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46389780695023516121825027 69584671042535274182737541)
      ·
        refine ⟨13047125820475363909263289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 69584671042535274182737541 13047125820475363909263289)
        ·
          refine ⟨9785344365356522931947467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13047125820475363909263289 9785344365356522931947467)
          ·
            refine ⟨14678016548034784397921201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9785344365356522931947467 14678016548034784397921201)
            ·
              refine ⟨11008512411026088298440901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14678016548034784397921201 11008512411026088298440901)
              ·
                refine ⟨2064096077067391555957669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11008512411026088298440901 2064096077067391555957669)
                ·
                  refine ⟨387018014450135916742063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2064096077067391555957669 387018014450135916742063)
                  ·
                    rfl

theorem cell22_3391717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 2, 4, 4].length) (baseStart_3391717 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3391717 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3391717 prefixEnd_3391717 := by exact prefixLift 3391717
  have htrace : WordTrace (prefixWord ++ tailWord_3391717) baseStart_3391717 baseEnd_3391717 := by
    simpa [prefixWord, tailWord_3391717, baseEnd_3391717] using wordTrace_append hprefix tailTrace_3391717
  have hstable : (prefixWord ++ tailWord_3391717).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3391717).length < 2 ^ (prefixWord ++ tailWord_3391717).sum := by decide
  have hdescent : baseEnd_3391717 < baseStart_3391717 := by decide
  rcases family_descends (prefixWord ++ tailWord_3391717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3391730 : List Nat := [3, 2, 1, 3, 2, 1, 1, 2, 1, 6]
def baseStart_3391730 : Nat := 118140960795 + 3391730 * 2 ^ 59
def prefixEnd_3391730 : Nat := 4983230072969 + 3 ^ 40 * 3391730 * 2
def baseEnd_3391730 : Nat := 1161058493516080049651149

theorem tailTrace_3391730 : CollatzResearch.WordTrace tailWord_3391730 prefixEnd_3391730 1161058493516080049651149 := by
  unfold tailWord_3391730
  simp only [CollatzResearch.WordTrace]
  refine ⟨30926639000587236552939161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82471037334899297474504429 30926639000587236552939161)
  ·
    refine ⟨23194979250440427414704371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30926639000587236552939161 23194979250440427414704371)
    ·
      refine ⟨34792468875660641122056557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23194979250440427414704371 34792468875660641122056557)
      ·
        refine ⟨13047175828372740420771209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34792468875660641122056557 13047175828372740420771209)
        ·
          refine ⟨9785381871279555315578407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13047175828372740420771209 9785381871279555315578407)
          ·
            refine ⟨14678072806919332973367611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9785381871279555315578407 14678072806919332973367611)
            ·
              refine ⟨22017109210378999460051417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14678072806919332973367611 22017109210378999460051417)
              ·
                refine ⟨16512831907784249595038563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22017109210378999460051417 16512831907784249595038563)
                ·
                  refine ⟨24769247861676374392557845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16512831907784249595038563 24769247861676374392557845)
                  ·
                    refine ⟨1161058493516080049651149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24769247861676374392557845 1161058493516080049651149)
                    ·
                      rfl

theorem cell22_3391730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 1, 2, 1, 6].length) (baseStart_3391730 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3391730 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3391730 prefixEnd_3391730 := by exact prefixLift 3391730
  have htrace : WordTrace (prefixWord ++ tailWord_3391730) baseStart_3391730 baseEnd_3391730 := by
    simpa [prefixWord, tailWord_3391730, baseEnd_3391730] using wordTrace_append hprefix tailTrace_3391730
  have hstable : (prefixWord ++ tailWord_3391730).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3391730).length < 2 ^ (prefixWord ++ tailWord_3391730).sum := by decide
  have hdescent : baseEnd_3391730 < baseStart_3391730 := by decide
  rcases family_descends (prefixWord ++ tailWord_3391730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3391743 : List Nat := [1, 1, 2, 2, 1, 4, 1, 1, 2, 7]
def baseStart_3391743 : Nat := 118140960795 + 3391743 * 2 ^ 59
def prefixEnd_3391743 : Nat := 4983230072969 + 3 ^ 40 * 3391743 * 2
def baseEnd_3391743 : Nat := 1161062943681752349076109

theorem tailTrace_3391743 : CollatzResearch.WordTrace tailWord_3391743 prefixEnd_3391743 1161062943681752349076109 := by
  unfold tailWord_3391743
  simp only [CollatzResearch.WordTrace]
  refine ⟨123707030151301849431979883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82471353434201232954653255 123707030151301849431979883)
  ·
    refine ⟨185560545226952774147969825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123707030151301849431979883 185560545226952774147969825)
    ·
      refine ⟨139170408920214580610977369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 185560545226952774147969825 139170408920214580610977369)
      ·
        refine ⟨104377806690160935458233027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139170408920214580610977369 104377806690160935458233027)
        ·
          refine ⟨156566710035241403187349541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104377806690160935458233027 156566710035241403187349541)
          ·
            refine ⟨29356258131607763097628039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 156566710035241403187349541 29356258131607763097628039)
            ·
              refine ⟨44034387197411644646442059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29356258131607763097628039 44034387197411644646442059)
              ·
                refine ⟨66051580796117466969663089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44034387197411644646442059 66051580796117466969663089)
                ·
                  refine ⟨49538685597088100227247317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 66051580796117466969663089 49538685597088100227247317)
                  ·
                    refine ⟨1161062943681752349076109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 49538685597088100227247317 1161062943681752349076109)
                    ·
                      rfl

theorem cell22_3391743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 1, 2, 7].length) (baseStart_3391743 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3391743 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3391743 prefixEnd_3391743 := by exact prefixLift 3391743
  have htrace : WordTrace (prefixWord ++ tailWord_3391743) baseStart_3391743 baseEnd_3391743 := by
    simpa [prefixWord, tailWord_3391743, baseEnd_3391743] using wordTrace_append hprefix tailTrace_3391743
  have hstable : (prefixWord ++ tailWord_3391743).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3391743).length < 2 ^ (prefixWord ++ tailWord_3391743).sum := by decide
  have hdescent : baseEnd_3391743 < baseStart_3391743 := by decide
  rcases family_descends (prefixWord ++ tailWord_3391743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3391751 : List Nat := [1, 1, 4, 5, 1, 2, 1, 3, 4]
def baseStart_3391751 : Nat := 118140960795 + 3391751 * 2 ^ 59
def prefixEnd_3391751 : Nat := 4983230072969 + 3 ^ 40 * 3391751 * 2
def baseEnd_3391751 : Nat := 387021894081747664958695

theorem tailTrace_3391751 : CollatzResearch.WordTrace tailWord_3391751 prefixEnd_3391751 387021894081747664958695 := by
  unfold tailWord_3391751
  simp only [CollatzResearch.WordTrace]
  refine ⟨123707321935272866798271107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82471547956848577865514071 123707321935272866798271107)
  ·
    refine ⟨185560982902909300197406661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123707321935272866798271107 185560982902909300197406661)
    ·
      refine ⟨34792684294295493787013749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 185560982902909300197406661 34792684294295493787013749)
      ·
        refine ⟨3261814152590202542532539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 34792684294295493787013749 3261814152590202542532539)
        ·
          refine ⟨4892721228885303813798809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3261814152590202542532539 4892721228885303813798809)
          ·
            refine ⟨3669540921663977860349107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4892721228885303813798809 3669540921663977860349107)
            ·
              refine ⟨5504311382495966790523661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3669540921663977860349107 5504311382495966790523661)
              ·
                refine ⟨2064116768435987546446373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5504311382495966790523661 2064116768435987546446373)
                ·
                  refine ⟨387021894081747664958695, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2064116768435987546446373 387021894081747664958695)
                  ·
                    rfl

theorem cell22_3391751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 2, 1, 3, 4].length) (baseStart_3391751 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3391751 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3391751 prefixEnd_3391751 := by exact prefixLift 3391751
  have htrace : WordTrace (prefixWord ++ tailWord_3391751) baseStart_3391751 baseEnd_3391751 := by
    simpa [prefixWord, tailWord_3391751, baseEnd_3391751] using wordTrace_append hprefix tailTrace_3391751
  have hstable : (prefixWord ++ tailWord_3391751).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3391751).length < 2 ^ (prefixWord ++ tailWord_3391751).sum := by decide
  have hdescent : baseEnd_3391751 < baseStart_3391751 := by decide
  rcases family_descends (prefixWord ++ tailWord_3391751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3391777 : List Nat := [1, 2, 3, 2, 1, 1, 5, 1, 3, 3]
def baseStart_3391777 : Nat := 118140960795 + 3391777 * 2 ^ 59
def prefixEnd_3391777 : Nat := 4983230072969 + 3 ^ 40 * 3391777 * 2
def baseEnd_3391777 : Nat := 1161074582576587593726005

theorem tailTrace_3391777 : CollatzResearch.WordTrace tailWord_3391777 prefixEnd_3391777 1161074582576587593726005 := by
  unfold tailWord_3391777
  simp only [CollatzResearch.WordTrace]
  refine ⟨123708270233178673238717585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82472180155452448825811723 123708270233178673238717585)
  ·
    refine ⟨92781202674884004929038189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123708270233178673238717585 92781202674884004929038189)
    ·
      refine ⟨34792951003081501848389321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92781202674884004929038189 34792951003081501848389321)
      ·
        refine ⟨26094713252311126386291991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34792951003081501848389321 26094713252311126386291991)
        ·
          refine ⟨39142069878466689579437987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26094713252311126386291991 39142069878466689579437987)
          ·
            refine ⟨58713104817700034369156981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39142069878466689579437987 58713104817700034369156981)
            ·
              refine ⟨5504353576659378222108467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 58713104817700034369156981 5504353576659378222108467)
              ·
                refine ⟨8256530364989067333162701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5504353576659378222108467 8256530364989067333162701)
                ·
                  refine ⟨3096198886870900249936013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8256530364989067333162701 3096198886870900249936013)
                  ·
                    refine ⟨1161074582576587593726005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3096198886870900249936013 1161074582576587593726005)
                    ·
                      rfl

theorem cell22_3391777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 5, 1, 3, 3].length) (baseStart_3391777 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3391777 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3391777 prefixEnd_3391777 := by exact prefixLift 3391777
  have htrace : WordTrace (prefixWord ++ tailWord_3391777) baseStart_3391777 baseEnd_3391777 := by
    simpa [prefixWord, tailWord_3391777, baseEnd_3391777] using wordTrace_append hprefix tailTrace_3391777
  have hstable : (prefixWord ++ tailWord_3391777).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3391777).length < 2 ^ (prefixWord ++ tailWord_3391777).sum := by decide
  have hdescent : baseEnd_3391777 < baseStart_3391777 := by decide
  rcases family_descends (prefixWord ++ tailWord_3391777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3391783 : List Nat := [1, 1, 8, 1, 1, 1, 1, 3, 2, 3]
def baseStart_3391783 : Nat := 118140960795 + 3391783 * 2 ^ 59
def prefixEnd_3391783 : Nat := 4983230072969 + 3 ^ 40 * 3391783 * 2
def baseEnd_3391783 : Nat := 1161076636499205578075987

theorem tailTrace_3391783 : CollatzResearch.WordTrace tailWord_3391783 prefixEnd_3391783 1161076636499205578075987 := by
  unfold tailWord_3391783
  simp only [CollatzResearch.WordTrace]
  refine ⟨123708489071156936263436003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82472326047437957508957335 123708489071156936263436003)
  ·
    refine ⟨185562733606735404395154005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123708489071156936263436003 185562733606735404395154005)
    ·
      refine ⟨2174563284453930520255711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 185562733606735404395154005 2174563284453930520255711)
      ·
        refine ⟨3261844926680895780383567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2174563284453930520255711 3261844926680895780383567)
        ·
          refine ⟨4892767390021343670575351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3261844926680895780383567 4892767390021343670575351)
          ·
            refine ⟨7339151085032015505863027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4892767390021343670575351 7339151085032015505863027)
            ·
              refine ⟨11008726627548023258794541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7339151085032015505863027 11008726627548023258794541)
              ·
                refine ⟨4128272485330508722047953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11008726627548023258794541 4128272485330508722047953)
                ·
                  refine ⟨3096204363997881541535965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4128272485330508722047953 3096204363997881541535965)
                  ·
                    refine ⟨1161076636499205578075987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3096204363997881541535965 1161076636499205578075987)
                    ·
                      rfl

theorem cell22_3391783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 1, 3, 2, 3].length) (baseStart_3391783 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3391783 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3391783 prefixEnd_3391783 := by exact prefixLift 3391783
  have htrace : WordTrace (prefixWord ++ tailWord_3391783) baseStart_3391783 baseEnd_3391783 := by
    simpa [prefixWord, tailWord_3391783, baseEnd_3391783] using wordTrace_append hprefix tailTrace_3391783
  have hstable : (prefixWord ++ tailWord_3391783).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3391783).length < 2 ^ (prefixWord ++ tailWord_3391783).sum := by decide
  have hdescent : baseEnd_3391783 < baseStart_3391783 := by decide
  rcases family_descends (prefixWord ++ tailWord_3391783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3391828 : List Nat := [2, 4, 1, 1, 2, 4, 2, 2, 1, 3]
def baseStart_3391828 : Nat := 118140960795 + 3391828 * 2 ^ 59
def prefixEnd_3391828 : Nat := 4983230072969 + 3 ^ 40 * 3391828 * 2
def baseEnd_3391828 : Nat := 1161092040918840460700849

theorem tailTrace_3391828 : CollatzResearch.WordTrace tailWord_3391828 prefixEnd_3391828 1161092040918840460700849 := by
  unfold tailWord_3391828
  simp only [CollatzResearch.WordTrace]
  refine ⟨61855065177996954474412069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82473420237329272632549425 61855065177996954474412069)
  ·
    refine ⟨11597824720874428963952263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 61855065177996954474412069 11597824720874428963952263)
    ·
      refine ⟨17396737081311643445928395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11597824720874428963952263 17396737081311643445928395)
      ·
        refine ⟨26095105621967465168892593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17396737081311643445928395 26095105621967465168892593)
        ·
          refine ⟨19571329216475598876669445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26095105621967465168892593 19571329216475598876669445)
          ·
            refine ⟨3669624228089174789375521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19571329216475598876669445 3669624228089174789375521)
            ·
              refine ⟨2752218171066881092031641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3669624228089174789375521 2752218171066881092031641)
              ·
                refine ⟨2064163628300160819023731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2752218171066881092031641 2064163628300160819023731)
                ·
                  refine ⟨3096245442450241228535597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2064163628300160819023731 3096245442450241228535597)
                  ·
                    refine ⟨1161092040918840460700849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3096245442450241228535597 1161092040918840460700849)
                    ·
                      rfl

theorem cell22_3391828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 4, 2, 2, 1, 3].length) (baseStart_3391828 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3391828 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3391828 prefixEnd_3391828 := by exact prefixLift 3391828
  have htrace : WordTrace (prefixWord ++ tailWord_3391828) baseStart_3391828 baseEnd_3391828 := by
    simpa [prefixWord, tailWord_3391828, baseEnd_3391828] using wordTrace_append hprefix tailTrace_3391828
  have hstable : (prefixWord ++ tailWord_3391828).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3391828).length < 2 ^ (prefixWord ++ tailWord_3391828).sum := by decide
  have hdescent : baseEnd_3391828 < baseStart_3391828 := by decide
  rcases family_descends (prefixWord ++ tailWord_3391828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3391852 : List Nat := [2, 2, 1, 1, 6, 1, 1, 2, 6]
def baseStart_3391852 : Nat := 118140960795 + 3391852 * 2 ^ 59
def prefixEnd_3391852 : Nat := 4983230072969 + 3 ^ 40 * 3391852 * 2
def baseEnd_3391852 : Nat := 387033418869770799366925

theorem tailTrace_3391852 : CollatzResearch.WordTrace tailWord_3391852 prefixEnd_3391852 387033418869770799366925 := by
  unfold tailWord_3391852
  simp only [CollatzResearch.WordTrace]
  refine ⟨61855502853953480523848905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82474003805271307365131873 61855502853953480523848905)
  ·
    refine ⟨46391627140465110392886679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61855502853953480523848905 46391627140465110392886679)
    ·
      refine ⟨69587440710697665589330019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46391627140465110392886679 69587440710697665589330019)
      ·
        refine ⟨104381161066046498383995029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69587440710697665589330019 104381161066046498383995029)
        ·
          refine ⟨4892866924970929611749767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 104381161066046498383995029 4892866924970929611749767)
          ·
            refine ⟨7339300387456394417624651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4892866924970929611749767 7339300387456394417624651)
            ·
              refine ⟨11008950581184591626436977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7339300387456394417624651 11008950581184591626436977)
              ·
                refine ⟨8256712935888443719827733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11008950581184591626436977 8256712935888443719827733)
                ·
                  refine ⟨387033418869770799366925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8256712935888443719827733 387033418869770799366925)
                  ·
                    rfl

theorem cell22_3391852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 6].length) (baseStart_3391852 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3391852 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3391852 prefixEnd_3391852 := by exact prefixLift 3391852
  have htrace : WordTrace (prefixWord ++ tailWord_3391852) baseStart_3391852 baseEnd_3391852 := by
    simpa [prefixWord, tailWord_3391852, baseEnd_3391852] using wordTrace_append hprefix tailTrace_3391852
  have hstable : (prefixWord ++ tailWord_3391852).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3391852).length < 2 ^ (prefixWord ++ tailWord_3391852).sum := by decide
  have hdescent : baseEnd_3391852 < baseStart_3391852 := by decide
  rcases family_descends (prefixWord ++ tailWord_3391852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3391869 : List Nat := [1, 4, 1, 1, 2, 4, 2, 3, 4]
def baseStart_3391869 : Nat := 118140960795 + 3391869 * 2 ^ 59
def prefixEnd_3391869 : Nat := 4983230072969 + 3 ^ 40 * 3391869 * 2
def baseEnd_3391869 : Nat := 387035358685576673475241

theorem tailTrace_3391869 : CollatzResearch.WordTrace tailWord_3391869 prefixEnd_3391869 387035358685576673475241 := by
  unfold tailWord_3391869
  simp only [CollatzResearch.WordTrace]
  refine ⟨123711625748845372951066661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82474417165896915300711107 123711625748845372951066661)
  ·
    refine ⟨23195929827908507428324999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 123711625748845372951066661 23195929827908507428324999)
    ·
      refine ⟨34793894741862761142487499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23195929827908507428324999 34793894741862761142487499)
      ·
        refine ⟨52190842112794141713731249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34793894741862761142487499 52190842112794141713731249)
        ·
          refine ⟨39143131584595606285298437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52190842112794141713731249 39143131584595606285298437)
          ·
            refine ⟨7339337172111676178493457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39143131584595606285298437 7339337172111676178493457)
            ·
              refine ⟨5504502879083757133870093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7339337172111676178493457 5504502879083757133870093)
              ·
                refine ⟨2064188579656408925201285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5504502879083757133870093 2064188579656408925201285)
                ·
                  refine ⟨387035358685576673475241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2064188579656408925201285 387035358685576673475241)
                  ·
                    rfl

theorem cell22_3391869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 2, 3, 4].length) (baseStart_3391869 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3391869 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3391869 prefixEnd_3391869 := by exact prefixLift 3391869
  have htrace : WordTrace (prefixWord ++ tailWord_3391869) baseStart_3391869 baseEnd_3391869 := by
    simpa [prefixWord, tailWord_3391869, baseEnd_3391869] using wordTrace_append hprefix tailTrace_3391869
  have hstable : (prefixWord ++ tailWord_3391869).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3391869).length < 2 ^ (prefixWord ++ tailWord_3391869).sum := by decide
  have hdescent : baseEnd_3391869 < baseStart_3391869 := by decide
  rcases family_descends (prefixWord ++ tailWord_3391869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3391880 : List Nat := [2, 1, 3, 3, 1, 1, 11]
def baseStart_3391880 : Nat := 118140960795 + 3391880 * 2 ^ 59
def prefixEnd_3391880 : Nat := 4983230072969 + 3 ^ 40 * 3391880 * 2
def baseEnd_3391880 : Nat := 43004068206723320681507

theorem tailTrace_3391880 : CollatzResearch.WordTrace tailWord_3391880 prefixEnd_3391880 43004068206723320681507 := by
  unfold tailWord_3391880
  simp only [CollatzResearch.WordTrace]
  refine ⟨61856013475902760914858547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82474684634537014553144729 61856013475902760914858547)
  ·
    refine ⟨92784020213854141372287821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61856013475902760914858547 92784020213854141372287821)
    ·
      refine ⟨34794007580195303014607933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92784020213854141372287821 34794007580195303014607933)
      ·
        refine ⟨13047752842573238630477975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34794007580195303014607933 13047752842573238630477975)
        ·
          refine ⟨19571629263859857945716963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13047752842573238630477975 19571629263859857945716963)
          ·
            refine ⟨29357443895789786918575445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19571629263859857945716963 29357443895789786918575445)
            ·
              refine ⟨43004068206723320681507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 29357443895789786918575445 43004068206723320681507)
              ·
                rfl

theorem cell22_3391880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 11].length) (baseStart_3391880 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3391880 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3391880 prefixEnd_3391880 := by exact prefixLift 3391880
  have htrace : WordTrace (prefixWord ++ tailWord_3391880) baseStart_3391880 baseEnd_3391880 := by
    simpa [prefixWord, tailWord_3391880, baseEnd_3391880] using wordTrace_append hprefix tailTrace_3391880
  have hstable : (prefixWord ++ tailWord_3391880).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3391880).length < 2 ^ (prefixWord ++ tailWord_3391880).sum := by decide
  have hdescent : baseEnd_3391880 < baseStart_3391880 := by decide
  rcases family_descends (prefixWord ++ tailWord_3391880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3391884 : List Nat := [2, 2, 1, 2, 1, 4, 3, 2, 2, 3]
def baseStart_3391884 : Nat := 118140960795 + 3391884 * 2 ^ 59
def prefixEnd_3391884 : Nat := 4983230072969 + 3 ^ 40 * 3391884 * 2
def baseEnd_3391884 : Nat := 1161111210863274981300677

theorem tailTrace_3391884 : CollatzResearch.WordTrace tailWord_3391884 prefixEnd_3391884 1161111210863274981300677 := by
  unfold tailWord_3391884
  simp only [CollatzResearch.WordTrace]
  refine ⟨61856086421895515256431353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82474781895860687008575137 61856086421895515256431353)
  ·
    refine ⟨46392064816421636442323515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61856086421895515256431353 46392064816421636442323515)
    ·
      refine ⟨69588097224632454663485273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46392064816421636442323515 69588097224632454663485273)
      ·
        refine ⟨52191072918474340997613955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69588097224632454663485273 52191072918474340997613955)
        ·
          refine ⟨78286609377711511496420933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52191072918474340997613955 78286609377711511496420933)
          ·
            refine ⟨14678739258320908405578925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 78286609377711511496420933 14678739258320908405578925)
            ·
              refine ⟨5504527221870340652092097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14678739258320908405578925 5504527221870340652092097)
              ·
                refine ⟨4128395416402755489069073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5504527221870340652092097 4128395416402755489069073)
                ·
                  refine ⟨3096296562302066616801805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4128395416402755489069073 3096296562302066616801805)
                  ·
                    refine ⟨1161111210863274981300677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3096296562302066616801805 1161111210863274981300677)
                    ·
                      rfl

theorem cell22_3391884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 3, 2, 2, 3].length) (baseStart_3391884 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3391884 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3391884 prefixEnd_3391884 := by exact prefixLift 3391884
  have htrace : WordTrace (prefixWord ++ tailWord_3391884) baseStart_3391884 baseEnd_3391884 := by
    simpa [prefixWord, tailWord_3391884, baseEnd_3391884] using wordTrace_append hprefix tailTrace_3391884
  have hstable : (prefixWord ++ tailWord_3391884).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3391884).length < 2 ^ (prefixWord ++ tailWord_3391884).sum := by decide
  have hdescent : baseEnd_3391884 < baseStart_3391884 := by decide
  rcases family_descends (prefixWord ++ tailWord_3391884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3391901 : List Nat := [1, 4, 2, 1, 5, 1, 1, 1, 1, 5]
def baseStart_3391901 : Nat := 118140960795 + 3391901 * 2 ^ 59
def prefixEnd_3391901 : Nat := 4983230072969 + 3 ^ 40 * 3391901 * 2
def baseEnd_3391901 : Nat := 1161117030310692603625625

theorem tailTrace_3391901 : CollatzResearch.WordTrace tailWord_3391901 prefixEnd_3391901 1161117030310692603625625 := by
  unfold tailWord_3391901
  simp only [CollatzResearch.WordTrace]
  refine ⟨123712792884729442416231557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82475195256486294944154371 123712792884729442416231557)
  ·
    refine ⟨23196148665886770453043417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 123712792884729442416231557 23196148665886770453043417)
    ·
      refine ⟨17397111499415077839782563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23196148665886770453043417 17397111499415077839782563)
      ·
        refine ⟨26095667249122616759673845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17397111499415077839782563 26095667249122616759673845)
        ·
          refine ⟨2446468804605245321219423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 26095667249122616759673845 2446468804605245321219423)
          ·
            refine ⟨3669703206907867981829135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2446468804605245321219423 3669703206907867981829135)
            ·
              refine ⟨5504554810361801972743703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3669703206907867981829135 5504554810361801972743703)
              ·
                refine ⟨8256832215542702959115555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5504554810361801972743703 8256832215542702959115555)
                ·
                  refine ⟨12385248323314054438673333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8256832215542702959115555 12385248323314054438673333)
                  ·
                    refine ⟨1161117030310692603625625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12385248323314054438673333 1161117030310692603625625)
                    ·
                      rfl

theorem cell22_3391901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 5, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 5, 1, 1, 1, 1, 5].length) (baseStart_3391901 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3391901 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3391901 prefixEnd_3391901 := by exact prefixLift 3391901
  have htrace : WordTrace (prefixWord ++ tailWord_3391901) baseStart_3391901 baseEnd_3391901 := by
    simpa [prefixWord, tailWord_3391901, baseEnd_3391901] using wordTrace_append hprefix tailTrace_3391901
  have hstable : (prefixWord ++ tailWord_3391901).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3391901).length < 2 ^ (prefixWord ++ tailWord_3391901).sum := by decide
  have hdescent : baseEnd_3391901 < baseStart_3391901 := by decide
  rcases family_descends (prefixWord ++ tailWord_3391901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3392019 : List Nat := [1, 1, 1, 2, 1, 5, 1, 5, 2, 3]
def baseStart_3392019 : Nat := 118140960795 + 3392019 * 2 ^ 59
def prefixEnd_3392019 : Nat := 4983230072969 + 3 ^ 40 * 3392019 * 2
def baseEnd_3392019 : Nat := 1161157424122179629175263

theorem tailTrace_3392019 : CollatzResearch.WordTrace tailWord_3392019 prefixEnd_3392019 1161157424122179629175263 := by
  unfold tailWord_3392019
  simp only [CollatzResearch.WordTrace]
  refine ⟨123717096698301948569027111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82478064465534632379351407 123717096698301948569027111)
  ·
    refine ⟨185575645047452922853540667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123717096698301948569027111 185575645047452922853540667)
    ·
      refine ⟨278363467571179384280311001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185575645047452922853540667 278363467571179384280311001)
      ·
        refine ⟨208772600678384538210233251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 278363467571179384280311001 208772600678384538210233251)
        ·
          refine ⟨313158901017576807315349877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 208772600678384538210233251 313158901017576807315349877)
          ·
            refine ⟨29358646970397825685814051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 313158901017576807315349877 29358646970397825685814051)
            ·
              refine ⟨44037970455596738528721077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29358646970397825685814051 44037970455596738528721077)
              ·
                refine ⟨4128559730212194237067601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 44037970455596738528721077 4128559730212194237067601)
                ·
                  refine ⟨3096419797659145677800701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4128559730212194237067601 3096419797659145677800701)
                  ·
                    refine ⟨1161157424122179629175263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3096419797659145677800701 1161157424122179629175263)
                    ·
                      rfl

theorem cell22_3392019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 5, 2, 3].length) (baseStart_3392019 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3392019 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3392019 prefixEnd_3392019 := by exact prefixLift 3392019
  have htrace : WordTrace (prefixWord ++ tailWord_3392019) baseStart_3392019 baseEnd_3392019 := by
    simpa [prefixWord, tailWord_3392019, baseEnd_3392019] using wordTrace_append hprefix tailTrace_3392019
  have hstable : (prefixWord ++ tailWord_3392019).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3392019).length < 2 ^ (prefixWord ++ tailWord_3392019).sum := by decide
  have hdescent : baseEnd_3392019 < baseStart_3392019 := by decide
  rcases family_descends (prefixWord ++ tailWord_3392019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3392064 : List Nat := [2, 1, 1, 2, 2, 2, 3, 3, 3, 3]
def baseStart_3392064 : Nat := 118140960795 + 3392064 * 2 ^ 59
def prefixEnd_3392064 : Nat := 4983230072969 + 3 ^ 40 * 3392064 * 2
def baseEnd_3392064 : Nat := 1161172828541814511800125

theorem tailTrace_3392064 : CollatzResearch.WordTrace tailWord_3392064 prefixEnd_3392064 1161172828541814511800125 := by
  unfold tailWord_3392064
  simp only [CollatzResearch.WordTrace]
  refine ⟨61859368991569460627207623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82479158655425947502943497 61859368991569460627207623)
  ·
    refine ⟨92789053487354190940811435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61859368991569460627207623 92789053487354190940811435)
    ·
      refine ⟨139183580231031286411217153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92789053487354190940811435 139183580231031286411217153)
      ·
        refine ⟨104387685173273464808412865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139183580231031286411217153 104387685173273464808412865)
        ·
          refine ⟨78290763879955098606309649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104387685173273464808412865 78290763879955098606309649)
          ·
            refine ⟨58718072909966323954732237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78290763879955098606309649 58718072909966323954732237)
            ·
              refine ⟨22019277341237371483024589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58718072909966323954732237 22019277341237371483024589)
              ·
                refine ⟨8257229002964014306134221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22019277341237371483024589 8257229002964014306134221)
                ·
                  refine ⟨3096460876111505364800333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8257229002964014306134221 3096460876111505364800333)
                  ·
                    refine ⟨1161172828541814511800125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3096460876111505364800333 1161172828541814511800125)
                    ·
                      rfl

theorem cell22_3392064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 3, 3, 3, 3].length) (baseStart_3392064 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3392064 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3392064 prefixEnd_3392064 := by exact prefixLift 3392064
  have htrace : WordTrace (prefixWord ++ tailWord_3392064) baseStart_3392064 baseEnd_3392064 := by
    simpa [prefixWord, tailWord_3392064, baseEnd_3392064] using wordTrace_append hprefix tailTrace_3392064
  have hstable : (prefixWord ++ tailWord_3392064).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3392064).length < 2 ^ (prefixWord ++ tailWord_3392064).sum := by decide
  have hdescent : baseEnd_3392064 < baseStart_3392064 := by decide
  rcases family_descends (prefixWord ++ tailWord_3392064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3392173 : List Nat := [1, 5, 2, 1, 1, 3, 1, 4, 4]
def baseStart_3392173 : Nat := 118140960795 + 3392173 * 2 ^ 59
def prefixEnd_3392173 : Nat := 4983230072969 + 3 ^ 40 * 3392173 * 2
def baseEnd_3392173 : Nat := 387070047156458186941597

theorem tailTrace_3392173 : CollatzResearch.WordTrace tailWord_3392173 prefixEnd_3392173 387070047156458186941597 := by
  unfold tailWord_3392173
  simp only [CollatzResearch.WordTrace]
  refine ⟨123722713539744032870133173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82481809026496021913422115 123722713539744032870133173)
  ·
    refine ⟨11599004394351003081574985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 123722713539744032870133173 11599004394351003081574985)
    ·
      refine ⟨8699253295763252311181239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11599004394351003081574985 8699253295763252311181239)
      ·
        refine ⟨13048879943644878466771859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8699253295763252311181239 13048879943644878466771859)
        ·
          refine ⟨19573319915467317700157789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13048879943644878466771859 19573319915467317700157789)
          ·
            refine ⟨7339994968300244137559171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19573319915467317700157789 7339994968300244137559171)
            ·
              refine ⟨11009992452450366206338757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7339994968300244137559171 11009992452450366206338757)
              ·
                refine ⟨2064373584834443663688517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11009992452450366206338757 2064373584834443663688517)
                ·
                  refine ⟨387070047156458186941597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2064373584834443663688517 387070047156458186941597)
                  ·
                    rfl

theorem cell22_3392173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 1, 4, 4].length) (baseStart_3392173 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3392173 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3392173 prefixEnd_3392173 := by exact prefixLift 3392173
  have htrace : WordTrace (prefixWord ++ tailWord_3392173) baseStart_3392173 baseEnd_3392173 := by
    simpa [prefixWord, tailWord_3392173, baseEnd_3392173] using wordTrace_append hprefix tailTrace_3392173
  have hstable : (prefixWord ++ tailWord_3392173).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3392173).length < 2 ^ (prefixWord ++ tailWord_3392173).sum := by decide
  have hdescent : baseEnd_3392173 < baseStart_3392173 := by decide
  rcases family_descends (prefixWord ++ tailWord_3392173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3392233 : List Nat := [1, 2, 1, 1, 1, 2, 6, 4, 1, 3]
def baseStart_3392233 : Nat := 118140960795 + 3392233 * 2 ^ 59
def prefixEnd_3392233 : Nat := 4983230072969 + 3 ^ 40 * 3392233 * 2
def baseEnd_3392233 : Nat := 1161230680695554404324607

theorem tailTrace_3392233 : CollatzResearch.WordTrace tailWord_3392233 prefixEnd_3392233 1161230680695554404324607 := by
  unfold tailWord_3392233
  simp only [CollatzResearch.WordTrace]
  refine ⟨123724901919526663117317353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82483267946351108744878235 123724901919526663117317353)
  ·
    refine ⟨92793676439644997337988015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123724901919526663117317353 92793676439644997337988015)
    ·
      refine ⟨139190514659467496006982023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92793676439644997337988015 139190514659467496006982023)
      ·
        refine ⟨208785771989201244010473035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139190514659467496006982023 208785771989201244010473035)
        ·
          refine ⟨313178657983801866015709553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 208785771989201244010473035 313178657983801866015709553)
          ·
            refine ⟨234883993487851399511782165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 313178657983801866015709553 234883993487851399511782165)
            ·
              refine ⟨11010187194743034352114789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 234883993487851399511782165 11010187194743034352114789)
              ·
                refine ⟨2064410099014318941021523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11010187194743034352114789 2064410099014318941021523)
                ·
                  refine ⟨3096615148521478411532285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2064410099014318941021523 3096615148521478411532285)
                  ·
                    refine ⟨1161230680695554404324607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3096615148521478411532285 1161230680695554404324607)
                    ·
                      rfl

theorem cell22_3392233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 6, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 6, 4, 1, 3].length) (baseStart_3392233 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3392233 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3392233 prefixEnd_3392233 := by exact prefixLift 3392233
  have htrace : WordTrace (prefixWord ++ tailWord_3392233) baseStart_3392233 baseEnd_3392233 := by
    simpa [prefixWord, tailWord_3392233, baseEnd_3392233] using wordTrace_append hprefix tailTrace_3392233
  have hstable : (prefixWord ++ tailWord_3392233).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3392233).length < 2 ^ (prefixWord ++ tailWord_3392233).sum := by decide
  have hdescent : baseEnd_3392233 < baseStart_3392233 := by decide
  rcases family_descends (prefixWord ++ tailWord_3392233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3392304 : List Nat := [2, 1, 1, 1, 2, 2, 1, 3, 3, 6]
def baseStart_3392304 : Nat := 118140960795 + 3392304 * 2 ^ 59
def prefixEnd_3392304 : Nat := 4983230072969 + 3 ^ 40 * 3392304 * 2
def baseEnd_3392304 : Nat := 1161254985446533885799389

theorem tailTrace_3392304 : CollatzResearch.WordTrace tailWord_3392304 prefixEnd_3392304 1161254985446533885799389 := by
  unfold tailWord_3392304
  simp only [CollatzResearch.WordTrace]
  refine ⟨61863745751134721121575983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82484994334846294828767977 61863745751134721121575983)
  ·
    refine ⟨92795618626702081682363975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61863745751134721121575983 92795618626702081682363975)
    ·
      refine ⟨139193427940053122523545963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92795618626702081682363975 139193427940053122523545963)
      ·
        refine ⟨208790141910079683785318945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139193427940053122523545963 208790141910079683785318945)
        ·
          refine ⟨156592606432559762838989209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 208790141910079683785318945 156592606432559762838989209)
          ·
            refine ⟨117444454824419822129241907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 156592606432559762838989209 117444454824419822129241907)
            ·
              refine ⟨176166682236629733193862861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 117444454824419822129241907 176166682236629733193862861)
              ·
                refine ⟨66062505838736149947698573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 176166682236629733193862861 66062505838736149947698573)
                ·
                  refine ⟨24773439689526056230386965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 66062505838736149947698573 24773439689526056230386965)
                  ·
                    refine ⟨1161254985446533885799389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24773439689526056230386965 1161254985446533885799389)
                    ·
                      rfl

theorem cell22_3392304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 3, 3, 6].length) (baseStart_3392304 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3392304 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3392304 prefixEnd_3392304 := by exact prefixLift 3392304
  have htrace : WordTrace (prefixWord ++ tailWord_3392304) baseStart_3392304 baseEnd_3392304 := by
    simpa [prefixWord, tailWord_3392304, baseEnd_3392304] using wordTrace_append hprefix tailTrace_3392304
  have hstable : (prefixWord ++ tailWord_3392304).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3392304).length < 2 ^ (prefixWord ++ tailWord_3392304).sum := by decide
  have hdescent : baseEnd_3392304 < baseStart_3392304 := by decide
  rcases family_descends (prefixWord ++ tailWord_3392304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3392306 : List Nat := [3, 2, 1, 1, 3, 1, 2, 3, 1, 5]
def baseStart_3392306 : Nat := 118140960795 + 3392306 * 2 ^ 59
def prefixEnd_3392306 : Nat := 4983230072969 + 3 ^ 40 * 3392306 * 2
def baseEnd_3392306 : Nat := 1161255670087406547249383

theorem tailTrace_3392306 : CollatzResearch.WordTrace tailWord_3392306 prefixEnd_3392306 1161255670087406547249383 := by
  unfold tailWord_3392306
  simp only [CollatzResearch.WordTrace]
  refine ⟨30931891112065549146181193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82485042965508131056483181 30931891112065549146181193)
  ·
    refine ⟨23198918334049161859635895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30931891112065549146181193 23198918334049161859635895)
    ·
      refine ⟨34798377501073742789453843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23198918334049161859635895 34798377501073742789453843)
      ·
        refine ⟨52197566251610614184180765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34798377501073742789453843 52197566251610614184180765)
        ·
          refine ⟨19574087344353980319067787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52197566251610614184180765 19574087344353980319067787)
          ·
            refine ⟨29361131016530970478601681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19574087344353980319067787 29361131016530970478601681)
            ·
              refine ⟨22020848262398227858951261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29361131016530970478601681 22020848262398227858951261)
              ·
                refine ⟨8257818098399335447106723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22020848262398227858951261 8257818098399335447106723)
                ·
                  refine ⟨12386727147599003170660085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8257818098399335447106723 12386727147599003170660085)
                  ·
                    refine ⟨1161255670087406547249383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12386727147599003170660085 1161255670087406547249383)
                    ·
                      rfl

theorem cell22_3392306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 2, 3, 1, 5].length) (baseStart_3392306 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3392306 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3392306 prefixEnd_3392306 := by exact prefixLift 3392306
  have htrace : WordTrace (prefixWord ++ tailWord_3392306) baseStart_3392306 baseEnd_3392306 := by
    simpa [prefixWord, tailWord_3392306, baseEnd_3392306] using wordTrace_append hprefix tailTrace_3392306
  have hstable : (prefixWord ++ tailWord_3392306).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3392306).length < 2 ^ (prefixWord ++ tailWord_3392306).sum := by decide
  have hdescent : baseEnd_3392306 < baseStart_3392306 := by decide
  rcases family_descends (prefixWord ++ tailWord_3392306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3392310 : List Nat := [5, 1, 2, 2, 2, 1, 1, 1, 3, 4]
def baseStart_3392310 : Nat := 118140960795 + 3392310 * 2 ^ 59
def prefixEnd_3392310 : Nat := 4983230072969 + 3 ^ 40 * 3392310 * 2
def baseEnd_3392310 : Nat := 1161257039369151870149371

theorem tailTrace_3392310 : CollatzResearch.WordTrace tailWord_3392310 prefixEnd_3392310 1161257039369151870149371 := by
  unfold tailWord_3392310
  simp only [CollatzResearch.WordTrace]
  refine ⟨7732981896265481579241899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 82485140226831803511913589 7732981896265481579241899)
  ·
    refine ⟨11599472844398222368862849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7732981896265481579241899 11599472844398222368862849)
    ·
      refine ⟨8699604633298666776647137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11599472844398222368862849 8699604633298666776647137)
      ·
        refine ⟨6524703474974000082485353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8699604633298666776647137 6524703474974000082485353)
        ·
          refine ⟨4893527606230500061864015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6524703474974000082485353 4893527606230500061864015)
          ·
            refine ⟨7340291409345750092796023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4893527606230500061864015 7340291409345750092796023)
            ·
              refine ⟨11010437114018625139194035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7340291409345750092796023 11010437114018625139194035)
              ·
                refine ⟨16515655671027937708791053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11010437114018625139194035 16515655671027937708791053)
                ·
                  refine ⟨6193370876635476640796645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16515655671027937708791053 6193370876635476640796645)
                  ·
                    refine ⟨1161257039369151870149371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6193370876635476640796645 1161257039369151870149371)
                    ·
                      rfl

theorem cell22_3392310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 1, 1, 3, 4].length) (baseStart_3392310 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3392310 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3392310 prefixEnd_3392310 := by exact prefixLift 3392310
  have htrace : WordTrace (prefixWord ++ tailWord_3392310) baseStart_3392310 baseEnd_3392310 := by
    simpa [prefixWord, tailWord_3392310, baseEnd_3392310] using wordTrace_append hprefix tailTrace_3392310
  have hstable : (prefixWord ++ tailWord_3392310).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3392310).length < 2 ^ (prefixWord ++ tailWord_3392310).sum := by decide
  have hdescent : baseEnd_3392310 < baseStart_3392310 := by decide
  rcases family_descends (prefixWord ++ tailWord_3392310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3392396 : List Nat := [2, 2, 1, 2, 1, 2, 3, 2, 2, 5]
def baseStart_3392396 : Nat := 118140960795 + 3392396 * 2 ^ 59
def prefixEnd_3392396 : Nat := 4983230072969 + 3 ^ 40 * 3392396 * 2
def baseEnd_3392396 : Nat := 1161286478926676312499107

theorem tailTrace_3392396 : CollatzResearch.WordTrace tailWord_3392396 prefixEnd_3392396 1161286478926676312499107 := by
  unfold tailWord_3392396
  simp only [CollatzResearch.WordTrace]
  refine ⟨61865423508968070977750521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82487231345290761303667361 61865423508968070977750521)
  ·
    refine ⟨46399067631726053233312891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61865423508968070977750521 46399067631726053233312891)
    ·
      refine ⟨69598601447589079849969337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46399067631726053233312891 69598601447589079849969337)
      ·
        refine ⟨52198951085691809887477003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69598601447589079849969337 52198951085691809887477003)
        ·
          refine ⟨78298426628537714831215505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52198951085691809887477003 78298426628537714831215505)
          ·
            refine ⟨58723819971403286123411629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78298426628537714831215505 58723819971403286123411629)
            ·
              refine ⟨22021432489276232296279361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58723819971403286123411629 22021432489276232296279361)
              ·
                refine ⟨16516074366957174222209521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22021432489276232296279361 16516074366957174222209521)
                ·
                  refine ⟨12387055775217880666657141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16516074366957174222209521 12387055775217880666657141)
                  ·
                    refine ⟨1161286478926676312499107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12387055775217880666657141 1161286478926676312499107)
                    ·
                      rfl

theorem cell22_3392396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 3, 2, 2, 5].length) (baseStart_3392396 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3392396 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3392396 prefixEnd_3392396 := by exact prefixLift 3392396
  have htrace : WordTrace (prefixWord ++ tailWord_3392396) baseStart_3392396 baseEnd_3392396 := by
    simpa [prefixWord, tailWord_3392396, baseEnd_3392396] using wordTrace_append hprefix tailTrace_3392396
  have hstable : (prefixWord ++ tailWord_3392396).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3392396).length < 2 ^ (prefixWord ++ tailWord_3392396).sum := by decide
  have hdescent : baseEnd_3392396 < baseStart_3392396 := by decide
  rcases family_descends (prefixWord ++ tailWord_3392396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3392402 : List Nat := [3, 2, 3, 2, 2, 1, 2, 1, 3, 3]
def baseStart_3392402 : Nat := 118140960795 + 3392402 * 2 ^ 59
def prefixEnd_3392402 : Nat := 4983230072969 + 3 ^ 40 * 3392402 * 2
def baseEnd_3392402 : Nat := 1161288532849294296849089

theorem tailTrace_3392402 : CollatzResearch.WordTrace tailWord_3392402 prefixEnd_3392402 1161288532849294296849089 := by
  unfold tailWord_3392402
  simp only [CollatzResearch.WordTrace]
  refine ⟨30932766463978601245054865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82487377237276269986812973 30932766463978601245054865)
  ·
    refine ⟨23199574847983950933791149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30932766463978601245054865 23199574847983950933791149)
    ·
      refine ⟨8699840567993981600171681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23199574847983950933791149 8699840567993981600171681)
      ·
        refine ⟨6524880425995486200128761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8699840567993981600171681 6524880425995486200128761)
        ·
          refine ⟨4893660319496614650096571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6524880425995486200128761 4893660319496614650096571)
          ·
            refine ⟨7340490479244921975144857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4893660319496614650096571 7340490479244921975144857)
            ·
              refine ⟨5505367859433691481358643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7340490479244921975144857 5505367859433691481358643)
              ·
                refine ⟨8258051789150537222037965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5505367859433691481358643 8258051789150537222037965)
                ·
                  refine ⟨3096769420931451458264237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8258051789150537222037965 3096769420931451458264237)
                  ·
                    refine ⟨1161288532849294296849089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3096769420931451458264237 1161288532849294296849089)
                    ·
                      rfl

theorem cell22_3392402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 2, 1, 3, 3].length) (baseStart_3392402 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3392402 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3392402 prefixEnd_3392402 := by exact prefixLift 3392402
  have htrace : WordTrace (prefixWord ++ tailWord_3392402) baseStart_3392402 baseEnd_3392402 := by
    simpa [prefixWord, tailWord_3392402, baseEnd_3392402] using wordTrace_append hprefix tailTrace_3392402
  have hstable : (prefixWord ++ tailWord_3392402).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3392402).length < 2 ^ (prefixWord ++ tailWord_3392402).sum := by decide
  have hdescent : baseEnd_3392402 < baseStart_3392402 := by decide
  rcases family_descends (prefixWord ++ tailWord_3392402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3392415 : List Nat := [1, 1, 2, 5, 2, 2, 3, 1, 5]
def baseStart_3392415 : Nat := 118140960795 + 3392415 * 2 ^ 59
def prefixEnd_3392415 : Nat := 4983230072969 + 3 ^ 40 * 3392415 * 2
def baseEnd_3392415 : Nat := 387097661004988865424683

theorem tailTrace_3392415 : CollatzResearch.WordTrace tailWord_3392415 prefixEnd_3392415 387097661004988865424683 := by
  unfold tailWord_3392415
  simp only [CollatzResearch.WordTrace]
  refine ⟨123731540004867308200442699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82487693336578205466961799 123731540004867308200442699)
  ·
    refine ⟨185597310007300962300664049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123731540004867308200442699 185597310007300962300664049)
    ·
      refine ⟨139197982505475721725498037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 185597310007300962300664049 139197982505475721725498037)
      ·
        refine ⟨13049810859888348911765441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 139197982505475721725498037 13049810859888348911765441)
        ·
          refine ⟨9787358144916261683824081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13049810859888348911765441 9787358144916261683824081)
          ·
            refine ⟨7340518608687196262868061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9787358144916261683824081 7340518608687196262868061)
            ·
              refine ⟨2752694478257698598575523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7340518608687196262868061 2752694478257698598575523)
              ·
                refine ⟨4129041717386547897863285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2752694478257698598575523 4129041717386547897863285)
                ·
                  refine ⟨387097661004988865424683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4129041717386547897863285 387097661004988865424683)
                  ·
                    rfl

theorem cell22_3392415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 3, 1, 5].length) (baseStart_3392415 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3392415 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3392415 prefixEnd_3392415 := by exact prefixLift 3392415
  have htrace : WordTrace (prefixWord ++ tailWord_3392415) baseStart_3392415 baseEnd_3392415 := by
    simpa [prefixWord, tailWord_3392415, baseEnd_3392415] using wordTrace_append hprefix tailTrace_3392415
  have hstable : (prefixWord ++ tailWord_3392415).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3392415).length < 2 ^ (prefixWord ++ tailWord_3392415).sum := by decide
  have hdescent : baseEnd_3392415 < baseStart_3392415 := by decide
  rcases family_descends (prefixWord ++ tailWord_3392415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3392436 : List Nat := [2, 5, 2, 1, 1, 3, 1, 3, 1, 3]
def baseStart_3392436 : Nat := 118140960795 + 3392436 * 2 ^ 59
def prefixEnd_3392436 : Nat := 4983230072969 + 3 ^ 40 * 3392436 * 2
def baseEnd_3392436 : Nat := 1161300171744129541498985

theorem tailTrace_3392436 : CollatzResearch.WordTrace tailWord_3392436 prefixEnd_3392436 1161300171744129541498985 := by
  unfold tailWord_3392436
  simp only [CollatzResearch.WordTrace]
  refine ⟨61866152968895614393478581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82488203958527485857971441 61866152968895614393478581)
  ·
    refine ⟨5799951840833963849388617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 61866152968895614393478581 5799951840833963849388617)
    ·
      refine ⟨4349963880625472887041463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5799951840833963849388617 4349963880625472887041463)
      ·
        refine ⟨6524945820938209330562195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4349963880625472887041463 6524945820938209330562195)
        ·
          refine ⟨9787418731407313995843293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6524945820938209330562195 9787418731407313995843293)
          ·
            refine ⟨3670282024277742748441235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9787418731407313995843293 3670282024277742748441235)
            ·
              refine ⟨5505423036416614122661853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3670282024277742748441235 5505423036416614122661853)
              ·
                refine ⟨2064533638656230295998195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5505423036416614122661853 2064533638656230295998195)
                ·
                  refine ⟨3096800457984345443997293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2064533638656230295998195 3096800457984345443997293)
                  ·
                    refine ⟨1161300171744129541498985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3096800457984345443997293 1161300171744129541498985)
                    ·
                      rfl

theorem cell22_3392436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 3, 1, 3, 1, 3].length) (baseStart_3392436 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3392436 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3392436 prefixEnd_3392436 := by exact prefixLift 3392436
  have htrace : WordTrace (prefixWord ++ tailWord_3392436) baseStart_3392436 baseEnd_3392436 := by
    simpa [prefixWord, tailWord_3392436, baseEnd_3392436] using wordTrace_append hprefix tailTrace_3392436
  have hstable : (prefixWord ++ tailWord_3392436).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3392436).length < 2 ^ (prefixWord ++ tailWord_3392436).sum := by decide
  have hdescent : baseEnd_3392436 < baseStart_3392436 := by decide
  rcases family_descends (prefixWord ++ tailWord_3392436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3392490 : List Nat := [3, 1, 3, 1, 2, 3, 2, 1, 2, 4]
def baseStart_3392490 : Nat := 118140960795 + 3392490 * 2 ^ 59
def prefixEnd_3392490 : Nat := 4983230072969 + 3 ^ 40 * 3392490 * 2
def baseEnd_3392490 : Nat := 1161318657047691400648819

theorem tailTrace_3392490 : CollatzResearch.WordTrace tailWord_3392490 prefixEnd_3392490 1161318657047691400648819 := by
  unfold tailWord_3392490
  simp only [CollatzResearch.WordTrace]
  refine ⟨30933568869898899002355731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82489516986397064006281949 30933568869898899002355731)
  ·
    refine ⟨46400353304848348503533597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30933568869898899002355731 46400353304848348503533597)
    ·
      refine ⟨17400132489318130688825099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46400353304848348503533597 17400132489318130688825099)
      ·
        refine ⟨26100198733977196033237649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17400132489318130688825099 26100198733977196033237649)
        ·
          refine ⟨19575149050482897024928237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26100198733977196033237649 19575149050482897024928237)
          ·
            refine ⟨7340680893931086384348089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19575149050482897024928237 7340680893931086384348089)
            ·
              refine ⟨5505510670448314788261067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7340680893931086384348089 5505510670448314788261067)
              ·
                refine ⟨8258266005672472182391601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5505510670448314788261067 8258266005672472182391601)
                ·
                  refine ⟨6193699504254354136793701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8258266005672472182391601 6193699504254354136793701)
                  ·
                    refine ⟨1161318657047691400648819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6193699504254354136793701 1161318657047691400648819)
                    ·
                      rfl

theorem cell22_3392490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 2, 1, 2, 4].length) (baseStart_3392490 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3392490 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3392490 prefixEnd_3392490 := by exact prefixLift 3392490
  have htrace : WordTrace (prefixWord ++ tailWord_3392490) baseStart_3392490 baseEnd_3392490 := by
    simpa [prefixWord, tailWord_3392490, baseEnd_3392490] using wordTrace_append hprefix tailTrace_3392490
  have hstable : (prefixWord ++ tailWord_3392490).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3392490).length < 2 ^ (prefixWord ++ tailWord_3392490).sum := by decide
  have hdescent : baseEnd_3392490 < baseStart_3392490 := by decide
  rcases family_descends (prefixWord ++ tailWord_3392490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3392582 : List Nat := [6, 1, 1, 1, 1, 2, 2, 1, 2, 5]
def baseStart_3392582 : Nat := 118140960795 + 3392582 * 2 ^ 59
def prefixEnd_3392582 : Nat := 4983230072969 + 3 ^ 40 * 3392582 * 2
def baseEnd_3392582 : Nat := 1161350150527833827348537

theorem tailTrace_3392582 : CollatzResearch.WordTrace tailWord_3392582 prefixEnd_3392582 1161350150527833827348537 := by
  unfold tailWord_3392582
  simp only [CollatzResearch.WordTrace]
  refine ⟨3866800968601946741305375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 82491753996841530481181333 3866800968601946741305375)
  ·
    refine ⟨5800201452902920111958063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3866800968601946741305375 5800201452902920111958063)
    ·
      refine ⟨8700302179354380167937095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5800201452902920111958063 8700302179354380167937095)
      ·
        refine ⟨13050453269031570251905643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8700302179354380167937095 13050453269031570251905643)
        ·
          refine ⟨19575679903547355377858465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13050453269031570251905643 19575679903547355377858465)
          ·
            refine ⟨14681759927660516533393849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19575679903547355377858465 14681759927660516533393849)
            ·
              refine ⟨11011319945745387400045387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14681759927660516533393849 11011319945745387400045387)
              ·
                refine ⟨16516979918618081100068081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11011319945745387400045387 16516979918618081100068081)
                ·
                  refine ⟨12387734938963560825051061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16516979918618081100068081 12387734938963560825051061)
                  ·
                    refine ⟨1161350150527833827348537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12387734938963560825051061 1161350150527833827348537)
                    ·
                      rfl

theorem cell22_3392582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 2, 1, 2, 5].length) (baseStart_3392582 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3392582 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3392582 prefixEnd_3392582 := by exact prefixLift 3392582
  have htrace : WordTrace (prefixWord ++ tailWord_3392582) baseStart_3392582 baseEnd_3392582 := by
    simpa [prefixWord, tailWord_3392582, baseEnd_3392582] using wordTrace_append hprefix tailTrace_3392582
  have hstable : (prefixWord ++ tailWord_3392582).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3392582).length < 2 ^ (prefixWord ++ tailWord_3392582).sum := by decide
  have hdescent : baseEnd_3392582 < baseStart_3392582 := by decide
  rcases family_descends (prefixWord ++ tailWord_3392582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3392608 : List Nat := [2, 1, 1, 3, 2, 2, 1, 3, 1, 6]
def baseStart_3392608 : Nat := 118140960795 + 3392608 * 2 ^ 59
def prefixEnd_3392608 : Nat := 4983230072969 + 3 ^ 40 * 3392608 * 2
def baseEnd_3392608 : Nat := 1161359050859178426198457

theorem tailTrace_3392608 : CollatzResearch.WordTrace tailWord_3392608 prefixEnd_3392608 1161359050859178426198457 := by
  unfold tailWord_3392608
  simp only [CollatzResearch.WordTrace]
  refine ⟨61869289646584051081109239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82492386195445401441478985 61869289646584051081109239)
  ·
    refine ⟨92803934469876076621663859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61869289646584051081109239 92803934469876076621663859)
    ·
      refine ⟨139205901704814114932495789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92803934469876076621663859 139205901704814114932495789)
      ·
        refine ⟨52202213139305293099685921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 139205901704814114932495789 52202213139305293099685921)
        ·
          refine ⟨39151659854478969824764441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52202213139305293099685921 39151659854478969824764441)
          ·
            refine ⟨29363744890859227368573331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39151659854478969824764441 29363744890859227368573331)
            ·
              refine ⟨44045617336288841052859997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29363744890859227368573331 44045617336288841052859997)
              ·
                refine ⟨16517106501108315394822499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44045617336288841052859997 16517106501108315394822499)
                ·
                  refine ⟨24775659751662473092233749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16517106501108315394822499 24775659751662473092233749)
                  ·
                    refine ⟨1161359050859178426198457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24775659751662473092233749 1161359050859178426198457)
                    ·
                      rfl

theorem cell22_3392608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 3, 1, 6].length) (baseStart_3392608 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3392608 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3392608 prefixEnd_3392608 := by exact prefixLift 3392608
  have htrace : WordTrace (prefixWord ++ tailWord_3392608) baseStart_3392608 baseEnd_3392608 := by
    simpa [prefixWord, tailWord_3392608, baseEnd_3392608] using wordTrace_append hprefix tailTrace_3392608
  have hstable : (prefixWord ++ tailWord_3392608).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3392608).length < 2 ^ (prefixWord ++ tailWord_3392608).sum := by decide
  have hdescent : baseEnd_3392608 < baseStart_3392608 := by decide
  rcases family_descends (prefixWord ++ tailWord_3392608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3392629 : List Nat := [1, 3, 4, 3, 1, 2, 1, 1, 6]
def baseStart_3392629 : Nat := 118140960795 + 3392629 * 2 ^ 59
def prefixEnd_3392629 : Nat := 4983230072969 + 3 ^ 40 * 3392629 * 2
def baseEnd_3392629 : Nat := 387122079862780457141131

theorem tailTrace_3392629 : CollatzResearch.WordTrace tailWord_3392629 prefixEnd_3392629 387122079862780457141131 := by
  unfold tailWord_3392629
  simp only [CollatzResearch.WordTrace]
  refine ⟨123739345226092022748732941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82492896817394681832488627 123739345226092022748732941)
  ·
    refine ⟨46402254459784508530774853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123739345226092022748732941 46402254459784508530774853)
    ·
      refine ⟨8700422711209595349520285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46402254459784508530774853 8700422711209595349520285)
      ·
        refine ⟨3262658516703598256070107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8700422711209595349520285 3262658516703598256070107)
        ·
          refine ⟨4893987775055397384105161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3262658516703598256070107 4893987775055397384105161)
          ·
            refine ⟨3670490831291548038078871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4893987775055397384105161 3670490831291548038078871)
            ·
              refine ⟨5505736246937322057118307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3670490831291548038078871 5505736246937322057118307)
              ·
                refine ⟨8258604370405983085677461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5505736246937322057118307 8258604370405983085677461)
                ·
                  refine ⟨387122079862780457141131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8258604370405983085677461 387122079862780457141131)
                  ·
                    rfl

theorem cell22_3392629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 2, 1, 1, 6].length) (baseStart_3392629 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3392629 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3392629 prefixEnd_3392629 := by exact prefixLift 3392629
  have htrace : WordTrace (prefixWord ++ tailWord_3392629) baseStart_3392629 baseEnd_3392629 := by
    simpa [prefixWord, tailWord_3392629, baseEnd_3392629] using wordTrace_append hprefix tailTrace_3392629
  have hstable : (prefixWord ++ tailWord_3392629).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3392629).length < 2 ^ (prefixWord ++ tailWord_3392629).sum := by decide
  have hdescent : baseEnd_3392629 < baseStart_3392629 := by decide
  rcases family_descends (prefixWord ++ tailWord_3392629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3392644 : List Nat := [2, 3, 2, 1, 2, 2, 4, 1, 2, 3]
def baseStart_3392644 : Nat := 118140960795 + 3392644 * 2 ^ 59
def prefixEnd_3392644 : Nat := 4983230072969 + 3 ^ 40 * 3392644 * 2
def baseEnd_3392644 : Nat := 1161371374394886332298347

theorem tailTrace_3392644 : CollatzResearch.WordTrace tailWord_3392644 prefixEnd_3392644 1161371374394886332298347 := by
  unfold tailWord_3392644
  simp only [CollatzResearch.WordTrace]
  refine ⟨61869946160518840155264493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82493261547358453540352657 61869946160518840155264493)
  ·
    refine ⟨23201229810194565058224185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61869946160518840155264493 23201229810194565058224185)
    ·
      refine ⟨17400922357645923793668139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23201229810194565058224185 17400922357645923793668139)
      ·
        refine ⟨26101383536468885690502209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17400922357645923793668139 26101383536468885690502209)
        ·
          refine ⟨19576037652351664267876657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26101383536468885690502209 19576037652351664267876657)
          ·
            refine ⟨14682028239263748200907493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19576037652351664267876657 14682028239263748200907493)
            ·
              refine ⟨2752880294861952787670155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14682028239263748200907493 2752880294861952787670155)
              ·
                refine ⟨4129320442292929181505233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2752880294861952787670155 4129320442292929181505233)
                ·
                  refine ⟨3096990331719696886128925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4129320442292929181505233 3096990331719696886128925)
                  ·
                    refine ⟨1161371374394886332298347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3096990331719696886128925 1161371374394886332298347)
                    ·
                      rfl

theorem cell22_3392644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 4, 1, 2, 3].length) (baseStart_3392644 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3392644 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3392644 prefixEnd_3392644 := by exact prefixLift 3392644
  have htrace : WordTrace (prefixWord ++ tailWord_3392644) baseStart_3392644 baseEnd_3392644 := by
    simpa [prefixWord, tailWord_3392644, baseEnd_3392644] using wordTrace_append hprefix tailTrace_3392644
  have hstable : (prefixWord ++ tailWord_3392644).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3392644).length < 2 ^ (prefixWord ++ tailWord_3392644).sum := by decide
  have hdescent : baseEnd_3392644 < baseStart_3392644 := by decide
  rcases family_descends (prefixWord ++ tailWord_3392644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3392700 : List Nat := [2, 2, 2, 3, 2, 1, 1, 1, 1, 7]
def baseStart_3392700 : Nat := 118140960795 + 3392700 * 2 ^ 59
def prefixEnd_3392700 : Nat := 4983230072969 + 3 ^ 40 * 3392700 * 2
def baseEnd_3392700 : Nat := 1161390544339320852898175

theorem tailTrace_3392700 : CollatzResearch.WordTrace tailWord_3392700 prefixEnd_3392700 1161390544339320852898175 := by
  unfold tailWord_3392700
  simp only [CollatzResearch.WordTrace]
  refine ⟨61870967404417400937283777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82494623205889867916378369 61870967404417400937283777)
  ·
    refine ⟨46403225553313050702962833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61870967404417400937283777 46403225553313050702962833)
    ·
      refine ⟨34802419164984788027222125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46403225553313050702962833 34802419164984788027222125)
      ·
        refine ⟨13050907186869295510208297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34802419164984788027222125 13050907186869295510208297)
        ·
          refine ⟨9788180390151971632656223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13050907186869295510208297 9788180390151971632656223)
          ·
            refine ⟨14682270585227957448984335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9788180390151971632656223 14682270585227957448984335)
            ·
              refine ⟨22023405877841936173476503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14682270585227957448984335 22023405877841936173476503)
              ·
                refine ⟨33035108816762904260214755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22023405877841936173476503 33035108816762904260214755)
                ·
                  refine ⟨49552663225144356390322133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33035108816762904260214755 49552663225144356390322133)
                  ·
                    refine ⟨1161390544339320852898175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 49552663225144356390322133 1161390544339320852898175)
                    ·
                      rfl

theorem cell22_3392700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 1, 1, 1, 7].length) (baseStart_3392700 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3392700 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3392700 prefixEnd_3392700 := by exact prefixLift 3392700
  have htrace : WordTrace (prefixWord ++ tailWord_3392700) baseStart_3392700 baseEnd_3392700 := by
    simpa [prefixWord, tailWord_3392700, baseEnd_3392700] using wordTrace_append hprefix tailTrace_3392700
  have hstable : (prefixWord ++ tailWord_3392700).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3392700).length < 2 ^ (prefixWord ++ tailWord_3392700).sum := by decide
  have hdescent : baseEnd_3392700 < baseStart_3392700 := by decide
  rcases family_descends (prefixWord ++ tailWord_3392700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3392702 : List Nat := [4, 2, 1, 1, 3, 1, 2, 3, 5]
def baseStart_3392702 : Nat := 118140960795 + 3392702 * 2 ^ 59
def prefixEnd_3392702 : Nat := 4983230072969 + 3 ^ 40 * 3392702 * 2
def baseEnd_3392702 : Nat := 387130409660064504782723

theorem tailTrace_3392702 : CollatzResearch.WordTrace tailWord_3392702 prefixEnd_3392702 387130409660064504782723 := by
  unfold tailWord_3392702
  simp only [CollatzResearch.WordTrace]
  refine ⟨15467750969353444527017545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 82494671836551704144093573 15467750969353444527017545)
  ·
    refine ⟨11600813227015083395263159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15467750969353444527017545 11600813227015083395263159)
    ·
      refine ⟨17401219840522625092894739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11600813227015083395263159 17401219840522625092894739)
      ·
        refine ⟨26101829760783937639342109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17401219840522625092894739 26101829760783937639342109)
        ·
          refine ⟨9788186160293976614753291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26101829760783937639342109 9788186160293976614753291)
          ·
            refine ⟨14682279240440964922129937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9788186160293976614753291 14682279240440964922129937)
            ·
              refine ⟨11011709430330723691597453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14682279240440964922129937 11011709430330723691597453)
              ·
                refine ⟨4129391036374021384349045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11011709430330723691597453 4129391036374021384349045)
                ·
                  refine ⟨387130409660064504782723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4129391036374021384349045 387130409660064504782723)
                  ·
                    rfl

theorem cell22_3392702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 2, 3, 5].length) (baseStart_3392702 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3392702 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3392702 prefixEnd_3392702 := by exact prefixLift 3392702
  have htrace : WordTrace (prefixWord ++ tailWord_3392702) baseStart_3392702 baseEnd_3392702 := by
    simpa [prefixWord, tailWord_3392702, baseEnd_3392702] using wordTrace_append hprefix tailTrace_3392702
  have hstable : (prefixWord ++ tailWord_3392702).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3392702).length < 2 ^ (prefixWord ++ tailWord_3392702).sum := by decide
  have hdescent : baseEnd_3392702 < baseStart_3392702 := by decide
  rcases family_descends (prefixWord ++ tailWord_3392702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3392710 : List Nat := [6, 1, 2, 2, 2, 1, 1, 1, 2, 4]
def baseStart_3392710 : Nat := 118140960795 + 3392710 * 2 ^ 59
def prefixEnd_3392710 : Nat := 4983230072969 + 3 ^ 40 * 3392710 * 2
def baseEnd_3392710 : Nat := 1161393967543684160148145

theorem tailTrace_3392710 : CollatzResearch.WordTrace tailWord_3392710 prefixEnd_3392710 1161393967543684160148145 := by
  unfold tailWord_3392710
  simp only [CollatzResearch.WordTrace]
  refine ⟨3866946860587455424450987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 82494866359199049054954389 3866946860587455424450987)
  ·
    refine ⟨5800420290881183136676481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3866946860587455424450987 5800420290881183136676481)
    ·
      refine ⟨4350315218160887352507361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5800420290881183136676481 4350315218160887352507361)
      ·
        refine ⟨3262736413620665514380521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4350315218160887352507361 3262736413620665514380521)
        ·
          refine ⟨2447052310215499135785391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3262736413620665514380521 2447052310215499135785391)
          ·
            refine ⟨3670578465323248703678087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2447052310215499135785391 3670578465323248703678087)
            ·
              refine ⟨5505867697984873055517131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3670578465323248703678087 5505867697984873055517131)
              ·
                refine ⟨8258801546977309583275697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5505867697984873055517131 8258801546977309583275697)
                ·
                  refine ⟨6194101160232982187456773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8258801546977309583275697 6194101160232982187456773)
                  ·
                    refine ⟨1161393967543684160148145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6194101160232982187456773 1161393967543684160148145)
                    ·
                      rfl

theorem cell22_3392710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 2, 1, 1, 1, 2, 4].length) (baseStart_3392710 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3392710 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3392710 prefixEnd_3392710 := by exact prefixLift 3392710
  have htrace : WordTrace (prefixWord ++ tailWord_3392710) baseStart_3392710 baseEnd_3392710 := by
    simpa [prefixWord, tailWord_3392710, baseEnd_3392710] using wordTrace_append hprefix tailTrace_3392710
  have hstable : (prefixWord ++ tailWord_3392710).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3392710).length < 2 ^ (prefixWord ++ tailWord_3392710).sum := by decide
  have hdescent : baseEnd_3392710 < baseStart_3392710 := by decide
  rcases family_descends (prefixWord ++ tailWord_3392710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3392747 : List Nat := [1, 1, 1, 1, 2, 6, 2, 4, 4]
def baseStart_3392747 : Nat := 118140960795 + 3392747 * 2 ^ 59
def prefixEnd_3392747 : Nat := 4983230072969 + 3 ^ 40 * 3392747 * 2
def baseEnd_3392747 : Nat := 387135544466609465657677

theorem tailTrace_3392747 : CollatzResearch.WordTrace tailWord_3392747 prefixEnd_3392747 387135544466609465657677 := by
  unfold tailWord_3392747
  simp only [CollatzResearch.WordTrace]
  refine ⟨123743649039664528901528495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82495766026443019267685663 123743649039664528901528495)
  ·
    refine ⟨185615473559496793352292743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123743649039664528901528495 185615473559496793352292743)
    ·
      refine ⟨278423210339245190028439115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185615473559496793352292743 278423210339245190028439115)
      ·
        refine ⟨417634815508867785042658673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 278423210339245190028439115 417634815508867785042658673)
        ·
          refine ⟨313226111631650838781994005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 417634815508867785042658673 313226111631650838781994005)
          ·
            refine ⟨14682473982733633067905969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 313226111631650838781994005 14682473982733633067905969)
            ·
              refine ⟨11011855487050224800929477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14682473982733633067905969 11011855487050224800929477)
              ·
                refine ⟨2064722903821917150174277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11011855487050224800929477 2064722903821917150174277)
                ·
                  refine ⟨387135544466609465657677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2064722903821917150174277 387135544466609465657677)
                  ·
                    rfl

theorem cell22_3392747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 2, 4, 4].length) (baseStart_3392747 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3392747 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3392747 prefixEnd_3392747 := by exact prefixLift 3392747
  have htrace : WordTrace (prefixWord ++ tailWord_3392747) baseStart_3392747 baseEnd_3392747 := by
    simpa [prefixWord, tailWord_3392747, baseEnd_3392747] using wordTrace_append hprefix tailTrace_3392747
  have hstable : (prefixWord ++ tailWord_3392747).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3392747).length < 2 ^ (prefixWord ++ tailWord_3392747).sum := by decide
  have hdescent : baseEnd_3392747 < baseStart_3392747 := by decide
  rcases family_descends (prefixWord ++ tailWord_3392747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3392798 : List Nat := [4, 3, 2, 1, 3, 1, 1, 1, 6]
def baseStart_3392798 : Nat := 118140960795 + 3392798 * 2 ^ 59
def prefixEnd_3392798 : Nat := 4983230072969 + 3 ^ 40 * 3392798 * 2
def baseEnd_3392798 : Nat := 387141363914027087982625

theorem tailTrace_3392798 : CollatzResearch.WordTrace tailWord_3392798 prefixEnd_3392798 387141363914027087982625 := by
  unfold tailWord_3392798
  simp only [CollatzResearch.WordTrace]
  refine ⟨15468188645309970576454381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 82497006108319843074423365 15468188645309970576454381)
  ·
    refine ⟨5800570741991238966170393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15468188645309970576454381 5800570741991238966170393)
    ·
      refine ⟨4350428056493429224627795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5800570741991238966170393 4350428056493429224627795)
      ·
        refine ⟨6525642084740143836941693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4350428056493429224627795 6525642084740143836941693)
        ·
          refine ⟨2447115781777553938853135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6525642084740143836941693 2447115781777553938853135)
          ·
            refine ⟨3670673672666330908279703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2447115781777553938853135 3670673672666330908279703)
            ·
              refine ⟨5506010508999496362419555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3670673672666330908279703 5506010508999496362419555)
              ·
                refine ⟨8259015763499244543629333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5506010508999496362419555 8259015763499244543629333)
                ·
                  refine ⟨387141363914027087982625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8259015763499244543629333 387141363914027087982625)
                  ·
                    rfl

theorem cell22_3392798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 3, 1, 1, 1, 6].length) (baseStart_3392798 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3392798 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3392798 prefixEnd_3392798 := by exact prefixLift 3392798
  have htrace : WordTrace (prefixWord ++ tailWord_3392798) baseStart_3392798 baseEnd_3392798 := by
    simpa [prefixWord, tailWord_3392798, baseEnd_3392798] using wordTrace_append hprefix tailTrace_3392798
  have hstable : (prefixWord ++ tailWord_3392798).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3392798).length < 2 ^ (prefixWord ++ tailWord_3392798).sum := by decide
  have hdescent : baseEnd_3392798 < baseStart_3392798 := by decide
  rcases family_descends (prefixWord ++ tailWord_3392798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3392813 : List Nat := [1, 5, 3, 1, 1, 1, 4, 1, 2, 3]
def baseStart_3392813 : Nat := 118140960795 + 3392813 * 2 ^ 59
def prefixEnd_3392813 : Nat := 4983230072969 + 3 ^ 40 * 3392813 * 2
def baseEnd_3392813 : Nat := 1161429226548626224822829

theorem tailTrace_3392813 : CollatzResearch.WordTrace tailWord_3392813 prefixEnd_3392813 1161429226548626224822829 := by
  unfold tailWord_3392813
  simp only [CollatzResearch.WordTrace]
  refine ⟨123746056257425422173431093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82497370838283614782287395 123746056257425422173431093)
  ·
    refine ⟨11601192774133633328759165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 123746056257425422173431093 11601192774133633328759165)
    ·
      refine ⟨4350447290300112498284687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11601192774133633328759165 4350447290300112498284687)
      ·
        refine ⟨6525670935450168747427031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4350447290300112498284687 6525670935450168747427031)
        ·
          refine ⟨9788506403175253121140547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6525670935450168747427031 9788506403175253121140547)
          ·
            refine ⟨14682759604762879681710821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9788506403175253121140547 14682759604762879681710821)
            ·
              refine ⟨2753017425893039940320779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14682759604762879681710821 2753017425893039940320779)
              ·
                refine ⟨4129526138839559910481169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2753017425893039940320779 4129526138839559910481169)
                ·
                  refine ⟨3097144604129669932860877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4129526138839559910481169 3097144604129669932860877)
                  ·
                    refine ⟨1161429226548626224822829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3097144604129669932860877 1161429226548626224822829)
                    ·
                      rfl

theorem cell22_3392813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 4, 1, 2, 3].length) (baseStart_3392813 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3392813 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3392813 prefixEnd_3392813 := by exact prefixLift 3392813
  have htrace : WordTrace (prefixWord ++ tailWord_3392813) baseStart_3392813 baseEnd_3392813 := by
    simpa [prefixWord, tailWord_3392813, baseEnd_3392813] using wordTrace_append hprefix tailTrace_3392813
  have hstable : (prefixWord ++ tailWord_3392813).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3392813).length < 2 ^ (prefixWord ++ tailWord_3392813).sum := by decide
  have hdescent : baseEnd_3392813 < baseStart_3392813 := by decide
  rcases family_descends (prefixWord ++ tailWord_3392813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3392835 : List Nat := [1, 1, 1, 3, 1, 3, 1, 2, 4, 5]
def baseStart_3392835 : Nat := 118140960795 + 3392835 * 2 ^ 59
def prefixEnd_3392835 : Nat := 4983230072969 + 3 ^ 40 * 3392835 * 2
def baseEnd_3392835 : Nat := 1161436757598225500772761

theorem tailTrace_3392835 : CollatzResearch.WordTrace tailWord_3392835 prefixEnd_3392835 1161436757598225500772761 := by
  unfold tailWord_3392835
  simp only [CollatzResearch.WordTrace]
  refine ⟨123746858663345719930731959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82497905775563813287154639 123746858663345719930731959)
  ·
    refine ⟨185620287995018579896097939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123746858663345719930731959 185620287995018579896097939)
    ·
      refine ⟨278430431992527869844146909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185620287995018579896097939 278430431992527869844146909)
      ·
        refine ⟨104411411997197951191555091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 278430431992527869844146909 104411411997197951191555091)
        ·
          refine ⟨156617117995796926787332637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104411411997197951191555091 156617117995796926787332637)
          ·
            refine ⟨58731419248423847545249739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 156617117995796926787332637 58731419248423847545249739)
            ·
              refine ⟨88097128872635771317874609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58731419248423847545249739 88097128872635771317874609)
              ·
                refine ⟨66072846654476828488405957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 88097128872635771317874609 66072846654476828488405957)
                ·
                  refine ⟨12388658747714405341576117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 66072846654476828488405957 12388658747714405341576117)
                  ·
                    refine ⟨1161436757598225500772761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12388658747714405341576117 1161436757598225500772761)
                    ·
                      rfl

theorem cell22_3392835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 2, 4, 5].length) (baseStart_3392835 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3392835 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3392835 prefixEnd_3392835 := by exact prefixLift 3392835
  have htrace : WordTrace (prefixWord ++ tailWord_3392835) baseStart_3392835 baseEnd_3392835 := by
    simpa [prefixWord, tailWord_3392835, baseEnd_3392835] using wordTrace_append hprefix tailTrace_3392835
  have hstable : (prefixWord ++ tailWord_3392835).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3392835).length < 2 ^ (prefixWord ++ tailWord_3392835).sum := by decide
  have hdescent : baseEnd_3392835 < baseStart_3392835 := by decide
  rcases family_descends (prefixWord ++ tailWord_3392835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3392852 : List Nat := [2, 4, 1, 1, 2, 1, 2, 2, 2, 5]
def baseStart_3392852 : Nat := 118140960795 + 3392852 * 2 ^ 59
def prefixEnd_3392852 : Nat := 4983230072969 + 3 ^ 40 * 3392852 * 2
def baseEnd_3392852 : Nat := 1161442577045643123097709

theorem tailTrace_3392852 : CollatzResearch.WordTrace tailWord_3392852 prefixEnd_3392852 1161442577045643123097709 := by
  unfold tailWord_3392852
  simp only [CollatzResearch.WordTrace]
  refine ⟨61873739352142065917050405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82498319136189421222733873 61873739352142065917050405)
  ·
    refine ⟨11601326128526637359446951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 61873739352142065917050405 11601326128526637359446951)
    ·
      refine ⟨17401989192789956039170427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11601326128526637359446951 17401989192789956039170427)
      ·
        refine ⟨26102983789184934058755641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17401989192789956039170427 26102983789184934058755641)
        ·
          refine ⟨19577237841888700544066731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26102983789184934058755641 19577237841888700544066731)
          ·
            refine ⟨29365856762833050816100097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19577237841888700544066731 29365856762833050816100097)
            ·
              refine ⟨22024392572124788112075073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29365856762833050816100097 22024392572124788112075073)
              ·
                refine ⟨16518294429093591084056305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22024392572124788112075073 16518294429093591084056305)
                ·
                  refine ⟨12388720821820193313042229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16518294429093591084056305 12388720821820193313042229)
                  ·
                    refine ⟨1161442577045643123097709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12388720821820193313042229 1161442577045643123097709)
                    ·
                      rfl

theorem cell22_3392852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 2, 2, 2, 5].length) (baseStart_3392852 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3392852 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3392852 prefixEnd_3392852 := by exact prefixLift 3392852
  have htrace : WordTrace (prefixWord ++ tailWord_3392852) baseStart_3392852 baseEnd_3392852 := by
    simpa [prefixWord, tailWord_3392852, baseEnd_3392852] using wordTrace_append hprefix tailTrace_3392852
  have hstable : (prefixWord ++ tailWord_3392852).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3392852).length < 2 ^ (prefixWord ++ tailWord_3392852).sum := by decide
  have hdescent : baseEnd_3392852 < baseStart_3392852 := by decide
  rcases family_descends (prefixWord ++ tailWord_3392852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3392865 : List Nat := [1, 2, 3, 1, 1, 1, 1, 2, 10]
def baseStart_3392865 : Nat := 118140960795 + 3392865 * 2 ^ 59
def prefixEnd_3392865 : Nat := 4983230072969 + 3 ^ 40 * 3392865 * 2
def baseEnd_3392865 : Nat := 387149009070438474174223

theorem tailTrace_3392865 : CollatzResearch.WordTrace tailWord_3392865 prefixEnd_3392865 387149009070438474174223 := by
  unfold tailWord_3392865
  simp only [CollatzResearch.WordTrace]
  refine ⟨123747952853237035054324049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82498635235491356702882699 123747952853237035054324049)
  ·
    refine ⟨92810964639927776290743037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123747952853237035054324049 92810964639927776290743037)
    ·
      refine ⟨34804111739972916109028639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92810964639927776290743037 34804111739972916109028639)
      ·
        refine ⟨52206167609959374163542959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34804111739972916109028639 52206167609959374163542959)
        ·
          refine ⟨78309251414939061245314439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52206167609959374163542959 78309251414939061245314439)
          ·
            refine ⟨117463877122408591867971659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78309251414939061245314439 117463877122408591867971659)
            ·
              refine ⟨176195815683612887801957489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 117463877122408591867971659 176195815683612887801957489)
              ·
                refine ⟨132146861762709665851468117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 176195815683612887801957489 132146861762709665851468117)
                ·
                  refine ⟨387149009070438474174223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 132146861762709665851468117 387149009070438474174223)
                  ·
                    rfl

theorem cell22_3392865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 2, 10].length) (baseStart_3392865 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3392865 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3392865 prefixEnd_3392865 := by exact prefixLift 3392865
  have htrace : WordTrace (prefixWord ++ tailWord_3392865) baseStart_3392865 baseEnd_3392865 := by
    simpa [prefixWord, tailWord_3392865, baseEnd_3392865] using wordTrace_append hprefix tailTrace_3392865
  have hstable : (prefixWord ++ tailWord_3392865).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3392865).length < 2 ^ (prefixWord ++ tailWord_3392865).sum := by decide
  have hdescent : baseEnd_3392865 < baseStart_3392865 := by decide
  rcases family_descends (prefixWord ++ tailWord_3392865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3392867 : List Nat := [1, 1, 1, 5, 2, 2, 1, 2, 3, 4]
def baseStart_3392867 : Nat := 118140960795 + 3392867 * 2 ^ 59
def prefixEnd_3392867 : Nat := 4983230072969 + 3 ^ 40 * 3392867 * 2
def baseEnd_3392867 : Nat := 1161447711852188083972663

theorem tailTrace_3392867 : CollatzResearch.WordTrace tailWord_3392867 prefixEnd_3392867 1161447711852188083972663 := by
  unfold tailWord_3392867
  simp only [CollatzResearch.WordTrace]
  refine ⟨123748025799229789395896855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82498683866153192930597903 123748025799229789395896855)
  ·
    refine ⟨185622038698844684093845283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123748025799229789395896855 185622038698844684093845283)
    ·
      refine ⟨278433058048267026140767925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185622038698844684093845283 278433058048267026140767925)
      ·
        refine ⟨26103099192025033700696993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 278433058048267026140767925 26103099192025033700696993)
        ·
          refine ⟨19577324394018775275522745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26103099192025033700696993 19577324394018775275522745)
          ·
            refine ⟨14682993295514081456642059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19577324394018775275522745 14682993295514081456642059)
            ·
              refine ⟨22024489943271122184963089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14682993295514081456642059 22024489943271122184963089)
              ·
                refine ⟨16518367457453341638722317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22024489943271122184963089 16518367457453341638722317)
                ·
                  refine ⟨6194387796545003114520869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16518367457453341638722317 6194387796545003114520869)
                  ·
                    refine ⟨1161447711852188083972663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6194387796545003114520869 1161447711852188083972663)
                    ·
                      rfl

theorem cell22_3392867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 1, 2, 3, 4].length) (baseStart_3392867 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3392867 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3392867 prefixEnd_3392867 := by exact prefixLift 3392867
  have htrace : WordTrace (prefixWord ++ tailWord_3392867) baseStart_3392867 baseEnd_3392867 := by
    simpa [prefixWord, tailWord_3392867, baseEnd_3392867] using wordTrace_append hprefix tailTrace_3392867
  have hstable : (prefixWord ++ tailWord_3392867).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3392867).length < 2 ^ (prefixWord ++ tailWord_3392867).sum := by decide
  have hdescent : baseEnd_3392867 < baseStart_3392867 := by decide
  rcases family_descends (prefixWord ++ tailWord_3392867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3392882 : List Nat := [3, 2, 1, 2, 1, 2, 3, 2, 6]
def baseStart_3392882 : Nat := 118140960795 + 3392882 * 2 ^ 59
def prefixEnd_3392882 : Nat := 4983230072969 + 3 ^ 40 * 3392882 * 2
def baseEnd_3392882 : Nat := 387150948886244348282539

theorem tailTrace_3392882 : CollatzResearch.WordTrace tailWord_3392882 prefixEnd_3392882 387150948886244348282539 := by
  unfold tailWord_3392882
  simp only [CollatzResearch.WordTrace]
  refine ⟨30937143223543861739423225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82499048596116964638461933 30937143223543861739423225)
  ·
    refine ⟨23202857417657896304567419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30937143223543861739423225 23202857417657896304567419)
    ·
      refine ⟨34804286126486844456851129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23202857417657896304567419 34804286126486844456851129)
      ·
        refine ⟨26103214594865133342638347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34804286126486844456851129 26103214594865133342638347)
        ·
          refine ⟨39154821892297700013957521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26103214594865133342638347 39154821892297700013957521)
          ·
            refine ⟨29366116419223275010468141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39154821892297700013957521 29366116419223275010468141)
            ·
              refine ⟨11012293657208728128925553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29366116419223275010468141 11012293657208728128925553)
              ·
                refine ⟨8259220242906546096694165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11012293657208728128925553 8259220242906546096694165)
                ·
                  refine ⟨387150948886244348282539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8259220242906546096694165 387150948886244348282539)
                  ·
                    rfl

theorem cell22_3392882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 3, 2, 6].length) (baseStart_3392882 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3392882 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3392882 prefixEnd_3392882 := by exact prefixLift 3392882
  have htrace : WordTrace (prefixWord ++ tailWord_3392882) baseStart_3392882 baseEnd_3392882 := by
    simpa [prefixWord, tailWord_3392882, baseEnd_3392882] using wordTrace_append hprefix tailTrace_3392882
  have hstable : (prefixWord ++ tailWord_3392882).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3392882).length < 2 ^ (prefixWord ++ tailWord_3392882).sum := by decide
  have hdescent : baseEnd_3392882 < baseStart_3392882 := by decide
  rcases family_descends (prefixWord ++ tailWord_3392882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3392899 : List Nat := [1, 1, 1, 3, 5, 1, 1, 5, 4]
def baseStart_3392899 : Nat := 118140960795 + 3392899 * 2 ^ 59
def prefixEnd_3392899 : Nat := 4983230072969 + 3 ^ 40 * 3392899 * 2
def baseEnd_3392899 : Nat := 387152888702050222390855

theorem tailTrace_3392899 : CollatzResearch.WordTrace tailWord_3392899 prefixEnd_3392899 387152888702050222390855 := by
  unfold tailWord_3392899
  simp only [CollatzResearch.WordTrace]
  refine ⟨123749192935113858861061751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82499461956742572574041167 123749192935113858861061751)
  ·
    refine ⟨185623789402670788291592627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123749192935113858861061751 185623789402670788291592627)
    ·
      refine ⟨278435684104006182437388941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185623789402670788291592627 278435684104006182437388941)
      ·
        refine ⟨104413381539002318414020853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 278435684104006182437388941 104413381539002318414020853)
        ·
          refine ⟨9788754519281467351314455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 104413381539002318414020853 9788754519281467351314455)
          ·
            refine ⟨14683131778922201026971683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9788754519281467351314455 14683131778922201026971683)
            ·
              refine ⟨22024697668383301540457525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14683131778922201026971683 22024697668383301540457525)
              ·
                refine ⟨2064815406410934519417893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22024697668383301540457525 2064815406410934519417893)
                ·
                  refine ⟨387152888702050222390855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2064815406410934519417893 387152888702050222390855)
                  ·
                    rfl

theorem cell22_3392899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 1, 5, 4].length) (baseStart_3392899 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3392899 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3392899 prefixEnd_3392899 := by exact prefixLift 3392899
  have htrace : WordTrace (prefixWord ++ tailWord_3392899) baseStart_3392899 baseEnd_3392899 := by
    simpa [prefixWord, tailWord_3392899, baseEnd_3392899] using wordTrace_append hprefix tailTrace_3392899
  have hstable : (prefixWord ++ tailWord_3392899).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3392899).length < 2 ^ (prefixWord ++ tailWord_3392899).sum := by decide
  have hdescent : baseEnd_3392899 < baseStart_3392899 := by decide
  rcases family_descends (prefixWord ++ tailWord_3392899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3392916 : List Nat := [2, 4, 2, 1, 2, 1, 2, 4, 4]
def baseStart_3392916 : Nat := 118140960795 + 3392916 * 2 ^ 59
def prefixEnd_3392916 : Nat := 4983230072969 + 3 ^ 40 * 3392916 * 2
def baseEnd_3392916 : Nat := 387154828517856096499171

theorem tailTrace_3392916 : CollatzResearch.WordTrace tailWord_3392916 prefixEnd_3392916 387154828517856096499171 := by
  unfold tailWord_3392916
  simp only [CollatzResearch.WordTrace]
  refine ⟨61874906488026135382215301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82499875317368180509620401 61874906488026135382215301)
  ·
    refine ⟨11601544966504900384165369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 61874906488026135382215301 11601544966504900384165369)
    ·
      refine ⟨8701158724878675288124027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11601544966504900384165369 8701158724878675288124027)
      ·
        refine ⟨13051738087318012932186041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8701158724878675288124027 13051738087318012932186041)
        ·
          refine ⟨9788803565488509699139531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13051738087318012932186041 9788803565488509699139531)
          ·
            refine ⟨14683205348232764548709297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9788803565488509699139531 14683205348232764548709297)
            ·
              refine ⟨11012404011174573411531973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14683205348232764548709297 11012404011174573411531973)
              ·
                refine ⟨2064825752095232514662245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11012404011174573411531973 2064825752095232514662245)
                ·
                  refine ⟨387154828517856096499171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2064825752095232514662245 387154828517856096499171)
                  ·
                    rfl

theorem cell22_3392916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 2, 4, 4].length) (baseStart_3392916 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3392916 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3392916 prefixEnd_3392916 := by exact prefixLift 3392916
  have htrace : WordTrace (prefixWord ++ tailWord_3392916) baseStart_3392916 baseEnd_3392916 := by
    simpa [prefixWord, tailWord_3392916, baseEnd_3392916] using wordTrace_append hprefix tailTrace_3392916
  have hstable : (prefixWord ++ tailWord_3392916).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3392916).length < 2 ^ (prefixWord ++ tailWord_3392916).sum := by decide
  have hdescent : baseEnd_3392916 < baseStart_3392916 := by decide
  rcases family_descends (prefixWord ++ tailWord_3392916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3392931 : List Nat := [1, 1, 1, 4, 1, 3, 5, 1, 2, 3]
def baseStart_3392931 : Nat := 118140960795 + 3392931 * 2 ^ 59
def prefixEnd_3392931 : Nat := 4983230072969 + 3 ^ 40 * 3392931 * 2
def baseEnd_3392931 : Nat := 1161469620360113250372467

theorem tailTrace_3392931 : CollatzResearch.WordTrace tailWord_3392931 prefixEnd_3392931 1161469620360113250372467 := by
  unfold tailWord_3392931
  simp only [CollatzResearch.WordTrace]
  refine ⟨123750360070997928326226647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82500240047331952217484431 123750360070997928326226647)
  ·
    refine ⟨185625540106496892489339971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123750360070997928326226647 185625540106496892489339971)
    ·
      refine ⟨278438310159745338734009957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185625540106496892489339971 278438310159745338734009957)
      ·
        refine ⟨52207183154952251012626867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 278438310159745338734009957 52207183154952251012626867)
        ·
          refine ⟨78310774732428376518940301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52207183154952251012626867 78310774732428376518940301)
          ·
            refine ⟨29366540524660641194602613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78310774732428376518940301 29366540524660641194602613)
            ·
              refine ⟨2753113174186935111993995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 29366540524660641194602613 2753113174186935111993995)
              ·
                refine ⟨4129669761280402667990993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2753113174186935111993995 4129669761280402667990993)
                ·
                  refine ⟨3097252320960302000993245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4129669761280402667990993 3097252320960302000993245)
                  ·
                    refine ⟨1161469620360113250372467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3097252320960302000993245 1161469620360113250372467)
                    ·
                      rfl

theorem cell22_3392931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 5, 1, 2, 3].length) (baseStart_3392931 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3392931 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3392931 prefixEnd_3392931 := by exact prefixLift 3392931
  have htrace : WordTrace (prefixWord ++ tailWord_3392931) baseStart_3392931 baseEnd_3392931 := by
    simpa [prefixWord, tailWord_3392931, baseEnd_3392931] using wordTrace_append hprefix tailTrace_3392931
  have hstable : (prefixWord ++ tailWord_3392931).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3392931).length < 2 ^ (prefixWord ++ tailWord_3392931).sum := by decide
  have hdescent : baseEnd_3392931 < baseStart_3392931 := by decide
  rcases family_descends (prefixWord ++ tailWord_3392931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3393066 : List Nat := [3, 1, 4, 1, 1, 1, 2, 2, 4, 3]
def baseStart_3393066 : Nat := 118140960795 + 3393066 * 2 ^ 59
def prefixEnd_3393066 : Nat := 4983230072969 + 3 ^ 40 * 3393066 * 2
def baseEnd_3393066 : Nat := 1161515833619017898247053

theorem tailTrace_3393066 : CollatzResearch.WordTrace tailWord_3393066 prefixEnd_3393066 1161515833619017898247053 := by
  unfold tailWord_3393066
  simp only [CollatzResearch.WordTrace]
  refine ⟨30938820981377211595597763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82503522617005897588260701 30938820981377211595597763)
  ·
    refine ⟨46408231472065817393396645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30938820981377211595597763 46408231472065817393396645)
    ·
      refine ⟨8701543401012340761261871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46408231472065817393396645 8701543401012340761261871)
      ·
        refine ⟨13052315101518511141892807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8701543401012340761261871 13052315101518511141892807)
        ·
          refine ⟨19578472652277766712839211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13052315101518511141892807 19578472652277766712839211)
          ·
            refine ⟨29367708978416650069258817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19578472652277766712839211 29367708978416650069258817)
            ·
              refine ⟨22025781733812487551944113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29367708978416650069258817 22025781733812487551944113)
              ·
                refine ⟨16519336300359365663958085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22025781733812487551944113 16519336300359365663958085)
                ·
                  refine ⟨3097375556317381061992141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16519336300359365663958085 3097375556317381061992141)
                  ·
                    refine ⟨1161515833619017898247053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3097375556317381061992141 1161515833619017898247053)
                    ·
                      rfl

theorem cell22_3393066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 2, 2, 4, 3].length) (baseStart_3393066 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3393066 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3393066 prefixEnd_3393066 := by exact prefixLift 3393066
  have htrace : WordTrace (prefixWord ++ tailWord_3393066) baseStart_3393066 baseEnd_3393066 := by
    simpa [prefixWord, tailWord_3393066, baseEnd_3393066] using wordTrace_append hprefix tailTrace_3393066
  have hstable : (prefixWord ++ tailWord_3393066).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3393066).length < 2 ^ (prefixWord ++ tailWord_3393066).sum := by decide
  have hdescent : baseEnd_3393066 < baseStart_3393066 := by decide
  rcases family_descends (prefixWord ++ tailWord_3393066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3393070 : List Nat := [4, 1, 3, 1, 2, 3, 2, 1, 1, 4]
def baseStart_3393070 : Nat := 118140960795 + 3393070 * 2 ^ 59
def prefixEnd_3393070 : Nat := 4983230072969 + 3 ^ 40 * 3393070 * 2
def baseEnd_3393070 : Nat := 1161517202900763221147041

theorem tailTrace_3393070 : CollatzResearch.WordTrace tailWord_3393070 prefixEnd_3393070 1161517202900763221147041 := by
  unfold tailWord_3393070
  simp only [CollatzResearch.WordTrace]
  refine ⟨15469428727186794383192083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 82503619878329570043691109 15469428727186794383192083)
  ·
    refine ⟨23204143090780191574788125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15469428727186794383192083 23204143090780191574788125)
    ·
      refine ⟨8701553659042571840545547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23204143090780191574788125 8701553659042571840545547)
      ·
        refine ⟨13052330488563857760818321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8701553659042571840545547 13052330488563857760818321)
        ·
          refine ⟨9789247866422893320613741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13052330488563857760818321 9789247866422893320613741)
          ·
            refine ⟨3670967949908584995230153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9789247866422893320613741 3670967949908584995230153)
            ·
              refine ⟨2753225962431438746422615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3670967949908584995230153 2753225962431438746422615)
              ·
                refine ⟨4129838943647158119633923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2753225962431438746422615 4129838943647158119633923)
                ·
                  refine ⟨6194758415470737179450885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4129838943647158119633923 6194758415470737179450885)
                  ·
                    refine ⟨1161517202900763221147041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6194758415470737179450885 1161517202900763221147041)
                    ·
                      rfl

theorem cell22_3393070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 3, 2, 1, 1, 4].length) (baseStart_3393070 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3393070 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3393070 prefixEnd_3393070 := by exact prefixLift 3393070
  have htrace : WordTrace (prefixWord ++ tailWord_3393070) baseStart_3393070 baseEnd_3393070 := by
    simpa [prefixWord, tailWord_3393070, baseEnd_3393070] using wordTrace_append hprefix tailTrace_3393070
  have hstable : (prefixWord ++ tailWord_3393070).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3393070).length < 2 ^ (prefixWord ++ tailWord_3393070).sum := by decide
  have hdescent : baseEnd_3393070 < baseStart_3393070 := by decide
  rcases family_descends (prefixWord ++ tailWord_3393070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3393111 : List Nat := [1, 1, 3, 2, 2, 3, 2, 2, 3, 3]
def baseStart_3393111 : Nat := 118140960795 + 3393111 * 2 ^ 59
def prefixEnd_3393111 : Nat := 4983230072969 + 3 ^ 40 * 3393111 * 2
def baseEnd_3393111 : Nat := 1161531238038652780871915

theorem tailTrace_3393111 : CollatzResearch.WordTrace tailWord_3393111 prefixEnd_3393111 1161531238038652780871915 := by
  unfold tailWord_3393111
  simp only [CollatzResearch.WordTrace]
  refine ⟨123756925210345819067779187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82504616806897212711852791 123756925210345819067779187)
  ·
    refine ⟨185635387815518728601668781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123756925210345819067779187 185635387815518728601668781)
    ·
      refine ⟨69613270430819523225625793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 185635387815518728601668781 69613270430819523225625793)
      ·
        refine ⟨52209952823114642419219345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69613270430819523225625793 52209952823114642419219345)
        ·
          refine ⟨39157464617335981814414509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52209952823114642419219345 39157464617335981814414509)
          ·
            refine ⟨14684049231500993180405441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39157464617335981814414509 14684049231500993180405441)
            ·
              refine ⟨11013036923625744885304081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14684049231500993180405441 11013036923625744885304081)
              ·
                refine ⟨8259777692719308663978061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11013036923625744885304081 8259777692719308663978061)
                ·
                  refine ⟨3097416634769740748991773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8259777692719308663978061 3097416634769740748991773)
                  ·
                    refine ⟨1161531238038652780871915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3097416634769740748991773 1161531238038652780871915)
                    ·
                      rfl

theorem cell22_3393111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 2, 2, 3, 3].length) (baseStart_3393111 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3393111 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3393111 prefixEnd_3393111 := by exact prefixLift 3393111
  have htrace : WordTrace (prefixWord ++ tailWord_3393111) baseStart_3393111 baseEnd_3393111 := by
    simpa [prefixWord, tailWord_3393111, baseEnd_3393111] using wordTrace_append hprefix tailTrace_3393111
  have hstable : (prefixWord ++ tailWord_3393111).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3393111).length < 2 ^ (prefixWord ++ tailWord_3393111).sum := by decide
  have hdescent : baseEnd_3393111 < baseStart_3393111 := by decide
  rcases family_descends (prefixWord ++ tailWord_3393111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3393124 : List Nat := [2, 3, 1, 1, 2, 3, 1, 2, 7]
def baseStart_3393124 : Nat := 118140960795 + 3393124 * 2 ^ 59
def prefixEnd_3393124 : Nat := 4983230072969 + 3 ^ 40 * 3393124 * 2
def baseEnd_3393124 : Nat := 387178562734775026765625

theorem tailTrace_3393124 : CollatzResearch.WordTrace tailWord_3393124 prefixEnd_3393124 387178562734775026765625 := by
  unfold tailWord_3393124
  simp only [CollatzResearch.WordTrace]
  refine ⟨61878699679649361144001213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82504932906199148192001617 61878699679649361144001213)
  ·
    refine ⟨23204512379868510429000455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61878699679649361144001213 23204512379868510429000455)
    ·
      refine ⟨34806768569802765643500683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23204512379868510429000455 34806768569802765643500683)
      ·
        refine ⟨52210152854704148465251025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34806768569802765643500683 52210152854704148465251025)
        ·
          refine ⟨39157614641028111348938269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52210152854704148465251025 39157614641028111348938269)
          ·
            refine ⟨14684105490385541755851851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39157614641028111348938269 14684105490385541755851851)
            ·
              refine ⟨22026158235578312633777777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14684105490385541755851851 22026158235578312633777777)
              ·
                refine ⟨16519618676683734475333333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22026158235578312633777777 16519618676683734475333333)
                ·
                  refine ⟨387178562734775026765625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16519618676683734475333333 387178562734775026765625)
                  ·
                    rfl

theorem cell22_3393124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 1, 2, 7].length) (baseStart_3393124 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3393124 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3393124 prefixEnd_3393124 := by exact prefixLift 3393124
  have htrace : WordTrace (prefixWord ++ tailWord_3393124) baseStart_3393124 baseEnd_3393124 := by
    simpa [prefixWord, tailWord_3393124, baseEnd_3393124] using wordTrace_append hprefix tailTrace_3393124
  have hstable : (prefixWord ++ tailWord_3393124).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3393124).length < 2 ^ (prefixWord ++ tailWord_3393124).sum := by decide
  have hdescent : baseEnd_3393124 < baseStart_3393124 := by decide
  rcases family_descends (prefixWord ++ tailWord_3393124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3393141 : List Nat := [1, 3, 4, 2, 1, 1, 2, 1, 7]
def baseStart_3393141 : Nat := 118140960795 + 3393141 * 2 ^ 59
def prefixEnd_3393141 : Nat := 4983230072969 + 3 ^ 40 * 3393141 * 2
def baseEnd_3393141 : Nat := 387180502550580900873941

theorem tailTrace_3393141 : CollatzResearch.WordTrace tailWord_3393141 prefixEnd_3393141 387180502550580900873941 := by
  unfold tailWord_3393141
  simp only [CollatzResearch.WordTrace]
  refine ⟨123758019400237134191371277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82505346266824756127580851 123758019400237134191371277)
  ·
    refine ⟨46409257275088925321764229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123758019400237134191371277 46409257275088925321764229)
    ·
      refine ⟨8701735739079173497830793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46409257275088925321764229 8701735739079173497830793)
      ·
        refine ⟨6526301804309380123373095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8701735739079173497830793 6526301804309380123373095)
        ·
          refine ⟨9789452706464070185059643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6526301804309380123373095 9789452706464070185059643)
          ·
            refine ⟨14684179059696105277589465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9789452706464070185059643 14684179059696105277589465)
            ·
              refine ⟨11013134294772078958192099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14684179059696105277589465 11013134294772078958192099)
              ·
                refine ⟨16519701442158118437288149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11013134294772078958192099 16519701442158118437288149)
                ·
                  refine ⟨387180502550580900873941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16519701442158118437288149 387180502550580900873941)
                  ·
                    rfl

theorem cell22_3393141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 2, 1, 7].length) (baseStart_3393141 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3393141 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3393141 prefixEnd_3393141 := by exact prefixLift 3393141
  have htrace : WordTrace (prefixWord ++ tailWord_3393141) baseStart_3393141 baseEnd_3393141 := by
    simpa [prefixWord, tailWord_3393141, baseEnd_3393141] using wordTrace_append hprefix tailTrace_3393141
  have hstable : (prefixWord ++ tailWord_3393141).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3393141).length < 2 ^ (prefixWord ++ tailWord_3393141).sum := by decide
  have hdescent : baseEnd_3393141 < baseStart_3393141 := by decide
  rcases family_descends (prefixWord ++ tailWord_3393141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3393145 : List Nat := [1, 2, 1, 3, 3, 1, 5, 2, 1, 3]
def baseStart_3393145 : Nat := 118140960795 + 3393145 * 2 ^ 59
def prefixEnd_3393145 : Nat := 4983230072969 + 3 ^ 40 * 3393145 * 2
def baseEnd_3393145 : Nat := 1161542876933488025521811

theorem tailTrace_3393145 : CollatzResearch.WordTrace tailWord_3393145 prefixEnd_3393145 1161542876933488025521811 := by
  unfold tailWord_3393145
  simp only [CollatzResearch.WordTrace]
  refine ⟨123758165292222642874516889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82505443528148428583011259 123758165292222642874516889)
  ·
    refine ⟨92818623969166982155887667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123758165292222642874516889 92818623969166982155887667)
    ·
      refine ⟨139227935953750473233831501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92818623969166982155887667 139227935953750473233831501)
      ·
        refine ⟨52210475982656427462686813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 139227935953750473233831501 52210475982656427462686813)
        ·
          refine ⟨19578928493496160298507555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52210475982656427462686813 19578928493496160298507555)
          ·
            refine ⟨29368392740244240447761333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19578928493496160298507555 29368392740244240447761333)
            ·
              refine ⟨2753286819397897541977625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 29368392740244240447761333 2753286819397897541977625)
              ·
                refine ⟨2064965114548423156483219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2753286819397897541977625 2064965114548423156483219)
                ·
                  refine ⟨3097447671822634734724829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2064965114548423156483219 3097447671822634734724829)
                  ·
                    refine ⟨1161542876933488025521811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3097447671822634734724829 1161542876933488025521811)
                    ·
                      rfl

theorem cell22_3393145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 5, 2, 1, 3].length) (baseStart_3393145 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3393145 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3393145 prefixEnd_3393145 := by exact prefixLift 3393145
  have htrace : WordTrace (prefixWord ++ tailWord_3393145) baseStart_3393145 baseEnd_3393145 := by
    simpa [prefixWord, tailWord_3393145, baseEnd_3393145] using wordTrace_append hprefix tailTrace_3393145
  have hstable : (prefixWord ++ tailWord_3393145).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3393145).length < 2 ^ (prefixWord ++ tailWord_3393145).sum := by decide
  have hdescent : baseEnd_3393145 < baseStart_3393145 := by decide
  rcases family_descends (prefixWord ++ tailWord_3393145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3393192 : List Nat := [2, 1, 7, 1, 1, 1, 2, 2, 5]
def baseStart_3393192 : Nat := 118140960795 + 3393192 * 2 ^ 59
def prefixEnd_3393192 : Nat := 4983230072969 + 3 ^ 40 * 3393192 * 2
def baseEnd_3393192 : Nat := 387186321997998523198889

theorem tailTrace_3393192 : CollatzResearch.WordTrace tailWord_3393192 prefixEnd_3393192 387186321997998523198889 := by
  unfold tailWord_3393192
  simp only [CollatzResearch.WordTrace]
  refine ⟨61879939761526184950738915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82506586348701579934318553 61879939761526184950738915)
  ·
    refine ⟨92819909642289277426108373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61879939761526184950738915 92819909642289277426108373)
    ·
      refine ⟨2175466632241154939674415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 92819909642289277426108373 2175466632241154939674415)
      ·
        refine ⟨3263199948361732409511623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2175466632241154939674415 3263199948361732409511623)
        ·
          refine ⟨4894799922542598614267435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3263199948361732409511623 4894799922542598614267435)
          ·
            refine ⟨7342199883813897921401153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4894799922542598614267435 7342199883813897921401153)
            ·
              refine ⟨5506649912860423441050865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7342199883813897921401153 5506649912860423441050865)
              ·
                refine ⟨4129987434645317580788149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5506649912860423441050865 4129987434645317580788149)
                ·
                  refine ⟨387186321997998523198889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4129987434645317580788149 387186321997998523198889)
                  ·
                    rfl

theorem cell22_3393192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 2, 2, 5].length) (baseStart_3393192 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3393192 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3393192 prefixEnd_3393192 := by exact prefixLift 3393192
  have htrace : WordTrace (prefixWord ++ tailWord_3393192) baseStart_3393192 baseEnd_3393192 := by
    simpa [prefixWord, tailWord_3393192, baseEnd_3393192] using wordTrace_append hprefix tailTrace_3393192
  have hstable : (prefixWord ++ tailWord_3393192).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3393192).length < 2 ^ (prefixWord ++ tailWord_3393192).sum := by decide
  have hdescent : baseEnd_3393192 < baseStart_3393192 := by decide
  rcases family_descends (prefixWord ++ tailWord_3393192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3393233 : List Nat := [1, 2, 2, 1, 2, 6, 1, 1, 2, 4]
def baseStart_3393233 : Nat := 118140960795 + 3393233 * 2 ^ 59
def prefixEnd_3393233 : Nat := 4983230072969 + 3 ^ 40 * 3393233 * 2
def baseEnd_3393233 : Nat := 1161573001131885129321541

theorem tailTrace_3393233 : CollatzResearch.WordTrace tailWord_3393233 prefixEnd_3393233 1161573001131885129321541 := by
  unfold tailWord_3393233
  simp only [CollatzResearch.WordTrace]
  refine ⟨123761374915903833903720353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82507583277269222602480235 123761374915903833903720353)
  ·
    refine ⟨92821031186927875427790265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123761374915903833903720353 92821031186927875427790265)
    ·
      refine ⟨69615773390195906570842699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92821031186927875427790265 69615773390195906570842699)
      ·
        refine ⟨104423660085293859856264049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69615773390195906570842699 104423660085293859856264049)
        ·
          refine ⟨78317745063970394892198037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104423660085293859856264049 78317745063970394892198037)
          ·
            refine ⟨3671144299873612260571783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 78317745063970394892198037 3671144299873612260571783)
            ·
              refine ⟨5506716449810418390857675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3671144299873612260571783 5506716449810418390857675)
              ·
                refine ⟨8260074674715627586286513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5506716449810418390857675 8260074674715627586286513)
                ·
                  refine ⟨6195056006036720689714885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8260074674715627586286513 6195056006036720689714885)
                  ·
                    refine ⟨1161573001131885129321541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6195056006036720689714885 1161573001131885129321541)
                    ·
                      rfl

theorem cell22_3393233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 6, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 6, 1, 1, 2, 4].length) (baseStart_3393233 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3393233 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3393233 prefixEnd_3393233 := by exact prefixLift 3393233
  have htrace : WordTrace (prefixWord ++ tailWord_3393233) baseStart_3393233 baseEnd_3393233 := by
    simpa [prefixWord, tailWord_3393233, baseEnd_3393233] using wordTrace_append hprefix tailTrace_3393233
  have hstable : (prefixWord ++ tailWord_3393233).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3393233).length < 2 ^ (prefixWord ++ tailWord_3393233).sum := by decide
  have hdescent : baseEnd_3393233 < baseStart_3393233 := by decide
  rcases family_descends (prefixWord ++ tailWord_3393233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3393263 : List Nat := [1, 1, 2, 1, 5, 1, 4, 1, 3, 3]
def baseStart_3393263 : Nat := 118140960795 + 3393263 * 2 ^ 59
def prefixEnd_3393263 : Nat := 4983230072969 + 3 ^ 40 * 3393263 * 2
def baseEnd_3393263 : Nat := 1161583270744975051071449

theorem tailTrace_3393263 : CollatzResearch.WordTrace tailWord_3393263 prefixEnd_3393263 1161583270744975051071449 := by
  unfold tailWord_3393263
  simp only [CollatzResearch.WordTrace]
  refine ⟨123762469105795149027312443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82508312737196766018208295 123762469105795149027312443)
  ·
    refine ⟨185643703658692723540968665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123762469105795149027312443 185643703658692723540968665)
    ·
      refine ⟨139232777744019542655726499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 185643703658692723540968665 139232777744019542655726499)
      ·
        refine ⟨208849166616029313983589749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139232777744019542655726499 208849166616029313983589749)
        ·
          refine ⟨19579609370252748185961539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 208849166616029313983589749 19579609370252748185961539)
          ·
            refine ⟨29369414055379122278942309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19579609370252748185961539 29369414055379122278942309)
            ·
              refine ⟨5506765135383585427301683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29369414055379122278942309 5506765135383585427301683)
              ·
                refine ⟨8260147703075378140952525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5506765135383585427301683 8260147703075378140952525)
                ·
                  refine ⟨3097555388653266802857197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8260147703075378140952525 3097555388653266802857197)
                  ·
                    refine ⟨1161583270744975051071449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3097555388653266802857197 1161583270744975051071449)
                    ·
                      rfl

theorem cell22_3393263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 4, 1, 3, 3].length) (baseStart_3393263 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3393263 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3393263 prefixEnd_3393263 := by exact prefixLift 3393263
  have htrace : WordTrace (prefixWord ++ tailWord_3393263) baseStart_3393263 baseEnd_3393263 := by
    simpa [prefixWord, tailWord_3393263, baseEnd_3393263] using wordTrace_append hprefix tailTrace_3393263
  have hstable : (prefixWord ++ tailWord_3393263).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3393263).length < 2 ^ (prefixWord ++ tailWord_3393263).sum := by decide
  have hdescent : baseEnd_3393263 < baseStart_3393263 := by decide
  rcases family_descends (prefixWord ++ tailWord_3393263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3393351 : List Nat := [1, 1, 4, 1, 2, 1, 2, 3, 1, 6]
def baseStart_3393351 : Nat := 118140960795 + 3393351 * 2 ^ 59
def prefixEnd_3393351 : Nat := 4983230072969 + 3 ^ 40 * 3393351 * 2
def baseEnd_3393351 : Nat := 1161613394943372154871179

theorem tailTrace_3393351 : CollatzResearch.WordTrace tailWord_3393351 prefixEnd_3393351 1161613394943372154871179 := by
  unfold tailWord_3393351
  simp only [CollatzResearch.WordTrace]
  refine ⟨123765678729476340056515907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82510452486317560037677271 123765678729476340056515907)
  ·
    refine ⟨185648518094214510084773861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123765678729476340056515907 185648518094214510084773861)
    ·
      refine ⟨34809097142665220640895099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 185648518094214510084773861 34809097142665220640895099)
      ·
        refine ⟨52213645713997830961342649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34809097142665220640895099 52213645713997830961342649)
        ·
          refine ⟨39160234285498373221006987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52213645713997830961342649 39160234285498373221006987)
          ·
            refine ⟨58740351428247559831510481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39160234285498373221006987 58740351428247559831510481)
            ·
              refine ⟨44055263571185669873632861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58740351428247559831510481 44055263571185669873632861)
              ·
                refine ⟨16520723839194626202612323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44055263571185669873632861 16520723839194626202612323)
                ·
                  refine ⟨24781085758791939303918485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16520723839194626202612323 24781085758791939303918485)
                  ·
                    refine ⟨1161613394943372154871179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24781085758791939303918485 1161613394943372154871179)
                    ·
                      rfl

theorem cell22_3393351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 3, 1, 6].length) (baseStart_3393351 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3393351 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3393351 prefixEnd_3393351 := by exact prefixLift 3393351
  have htrace : WordTrace (prefixWord ++ tailWord_3393351) baseStart_3393351 baseEnd_3393351 := by
    simpa [prefixWord, tailWord_3393351, baseEnd_3393351] using wordTrace_append hprefix tailTrace_3393351
  have hstable : (prefixWord ++ tailWord_3393351).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3393351).length < 2 ^ (prefixWord ++ tailWord_3393351).sum := by decide
  have hdescent : baseEnd_3393351 < baseStart_3393351 := by decide
  rcases family_descends (prefixWord ++ tailWord_3393351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3393370 : List Nat := [3, 1, 1, 2, 1, 3, 4, 2, 2, 3]
def baseStart_3393370 : Nat := 118140960795 + 3393370 * 2 ^ 59
def prefixEnd_3393370 : Nat := 4983230072969 + 3 ^ 40 * 3393370 * 2
def baseEnd_3393370 : Nat := 1161619899031662438646121

theorem tailTrace_3393370 : CollatzResearch.WordTrace tailWord_3393370 prefixEnd_3393370 1161619899031662438646121 := by
  unfold tailWord_3393370
  simp only [CollatzResearch.WordTrace]
  refine ⟨30941592929101876575364391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82510914477605004200971709 30941592929101876575364391)
  ·
    refine ⟨46412389393652814863046587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30941592929101876575364391 46412389393652814863046587)
    ·
      refine ⟨69618584090479222294569881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46412389393652814863046587 69618584090479222294569881)
      ·
        refine ⟨52213938067859416720927411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69618584090479222294569881 52213938067859416720927411)
        ·
          refine ⟨78320907101789125081391117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52213938067859416720927411 78320907101789125081391117)
          ·
            refine ⟨29370340163170921905521669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78320907101789125081391117 29370340163170921905521669)
            ·
              refine ⟨5506938780594547857285313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29370340163170921905521669 5506938780594547857285313)
              ·
                refine ⟨4130204085445910892963985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5506938780594547857285313 4130204085445910892963985)
                ·
                  refine ⟨3097653064084433169722989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4130204085445910892963985 3097653064084433169722989)
                  ·
                    refine ⟨1161619899031662438646121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3097653064084433169722989 1161619899031662438646121)
                    ·
                      rfl

theorem cell22_3393370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 4, 2, 2, 3].length) (baseStart_3393370 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3393370 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3393370 prefixEnd_3393370 := by exact prefixLift 3393370
  have htrace : WordTrace (prefixWord ++ tailWord_3393370) baseStart_3393370 baseEnd_3393370 := by
    simpa [prefixWord, tailWord_3393370, baseEnd_3393370] using wordTrace_append hprefix tailTrace_3393370
  have hstable : (prefixWord ++ tailWord_3393370).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3393370).length < 2 ^ (prefixWord ++ tailWord_3393370).sum := by decide
  have hdescent : baseEnd_3393370 < baseStart_3393370 := by decide
  rcases family_descends (prefixWord ++ tailWord_3393370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3393372 : List Nat := [2, 2, 4, 2, 2, 1, 1, 4, 4]
def baseStart_3393372 : Nat := 118140960795 + 3393372 * 2 ^ 59
def prefixEnd_3393372 : Nat := 4983230072969 + 3 ^ 40 * 3393372 * 2
def baseEnd_3393372 : Nat := 387206861224178366698705

theorem tailTrace_3393372 : CollatzResearch.WordTrace tailWord_3393372 prefixEnd_3393372 387206861224178366698705 := by
  unfold tailWord_3393372
  simp only [CollatzResearch.WordTrace]
  refine ⟨61883222331200130321515185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82510963108266840428686913 61883222331200130321515185)
  ·
    refine ⟨46412416748400097741136389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61883222331200130321515185 46412416748400097741136389)
    ·
      refine ⟨8702328140325018326463073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46412416748400097741136389 8702328140325018326463073)
      ·
        refine ⟨6526746105243763744847305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8702328140325018326463073 6526746105243763744847305)
        ·
          refine ⟨4895059578932822808635479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6526746105243763744847305 4895059578932822808635479)
          ·
            refine ⟨7342589368399234212953219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4895059578932822808635479 7342589368399234212953219)
            ·
              refine ⟨11013884052598851319429829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7342589368399234212953219 11013884052598851319429829)
              ·
                refine ⟨2065103259862284622393093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11013884052598851319429829 2065103259862284622393093)
                ·
                  refine ⟨387206861224178366698705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2065103259862284622393093 387206861224178366698705)
                  ·
                    rfl

theorem cell22_3393372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 1, 4, 4].length) (baseStart_3393372 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3393372 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3393372 prefixEnd_3393372 := by exact prefixLift 3393372
  have htrace : WordTrace (prefixWord ++ tailWord_3393372) baseStart_3393372 baseEnd_3393372 := by
    simpa [prefixWord, tailWord_3393372, baseEnd_3393372] using wordTrace_append hprefix tailTrace_3393372
  have hstable : (prefixWord ++ tailWord_3393372).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3393372).length < 2 ^ (prefixWord ++ tailWord_3393372).sum := by decide
  have hdescent : baseEnd_3393372 < baseStart_3393372 := by decide
  rcases family_descends (prefixWord ++ tailWord_3393372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3393381 : List Nat := [1, 3, 1, 3, 1, 1, 1, 2, 2, 7]
def baseStart_3393381 : Nat := 118140960795 + 3393381 * 2 ^ 59
def prefixEnd_3393381 : Nat := 4983230072969 + 3 ^ 40 * 3393381 * 2
def baseEnd_3393381 : Nat := 1161623664556462076621087

theorem tailTrace_3393381 : CollatzResearch.WordTrace tailWord_3393381 prefixEnd_3393381 1161623664556462076621087 := by
  unfold tailWord_3393381
  simp only [CollatzResearch.WordTrace]
  refine ⟨123766772919367655180107997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82511181946245103453405331 123766772919367655180107997)
  ·
    refine ⟨46412539844762870692540499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123766772919367655180107997 46412539844762870692540499)
    ·
      refine ⟨69618809767144306038810749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46412539844762870692540499 69618809767144306038810749)
      ·
        refine ⟨26107053662679114764554031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69618809767144306038810749 26107053662679114764554031)
        ·
          refine ⟨39160580494018672146831047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26107053662679114764554031 39160580494018672146831047)
          ·
            refine ⟨58740870741028008220246571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39160580494018672146831047 58740870741028008220246571)
            ·
              refine ⟨88111306111542012330369857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58740870741028008220246571 88111306111542012330369857)
              ·
                refine ⟨66083479583656509247777393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 88111306111542012330369857 66083479583656509247777393)
                ·
                  refine ⟨49562609687742381935833045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 66083479583656509247777393 49562609687742381935833045)
                  ·
                    refine ⟨1161623664556462076621087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 49562609687742381935833045 1161623664556462076621087)
                    ·
                      rfl

theorem cell22_3393381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 2, 2, 7].length) (baseStart_3393381 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3393381 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3393381 prefixEnd_3393381 := by exact prefixLift 3393381
  have htrace : WordTrace (prefixWord ++ tailWord_3393381) baseStart_3393381 baseEnd_3393381 := by
    simpa [prefixWord, tailWord_3393381, baseEnd_3393381] using wordTrace_append hprefix tailTrace_3393381
  have hstable : (prefixWord ++ tailWord_3393381).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3393381).length < 2 ^ (prefixWord ++ tailWord_3393381).sum := by decide
  have hdescent : baseEnd_3393381 < baseStart_3393381 := by decide
  rcases family_descends (prefixWord ++ tailWord_3393381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3393458 : List Nat := [3, 2, 1, 1, 1, 1, 1, 5, 3, 4]
def baseStart_3393458 : Nat := 118140960795 + 3393458 * 2 ^ 59
def prefixEnd_3393458 : Nat := 4983230072969 + 3 ^ 40 * 3393458 * 2
def baseEnd_3393458 : Nat := 1161650023230059542445851

theorem tailTrace_3393458 : CollatzResearch.WordTrace tailWord_3393458 prefixEnd_3393458 1161650023230059542445851 := by
  unfold tailWord_3393458
  simp only [CollatzResearch.WordTrace]
  refine ⟨30942395335022174332665257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82513054226725798220440685 30942395335022174332665257)
  ·
    refine ⟨23206796501266630749498943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30942395335022174332665257 23206796501266630749498943)
    ·
      refine ⟨34810194751899946124248415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23206796501266630749498943 34810194751899946124248415)
      ·
        refine ⟨52215292127849919186372623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34810194751899946124248415 52215292127849919186372623)
        ·
          refine ⟨78322938191774878779558935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52215292127849919186372623 78322938191774878779558935)
          ·
            refine ⟨117484407287662318169338403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78322938191774878779558935 117484407287662318169338403)
            ·
              refine ⟨176226610931493477254007605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 117484407287662318169338403 176226610931493477254007605)
              ·
                refine ⟨16521244774827513492563213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 176226610931493477254007605 16521244774827513492563213)
                ·
                  refine ⟨6195466790560317559711205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16521244774827513492563213 6195466790560317559711205)
                  ·
                    refine ⟨1161650023230059542445851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6195466790560317559711205 1161650023230059542445851)
                    ·
                      rfl

theorem cell22_3393458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 5, 3, 4].length) (baseStart_3393458 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3393458 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3393458 prefixEnd_3393458 := by exact prefixLift 3393458
  have htrace : WordTrace (prefixWord ++ tailWord_3393458) baseStart_3393458 baseEnd_3393458 := by
    simpa [prefixWord, tailWord_3393458, baseEnd_3393458] using wordTrace_append hprefix tailTrace_3393458
  have hstable : (prefixWord ++ tailWord_3393458).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3393458).length < 2 ^ (prefixWord ++ tailWord_3393458).sum := by decide
  have hdescent : baseEnd_3393458 < baseStart_3393458 := by decide
  rcases family_descends (prefixWord ++ tailWord_3393458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3393548 : List Nat := [2, 2, 1, 2, 3, 1, 1, 1, 1, 8]
def baseStart_3393548 : Nat := 118140960795 + 3393548 * 2 ^ 59
def prefixEnd_3393548 : Nat := 4983230072969 + 3 ^ 40 * 3393548 * 2
def baseEnd_3393548 : Nat := 1161680832069329307695575

theorem tailTrace_3393548 : CollatzResearch.WordTrace tailWord_3393548 prefixEnd_3393548 1161680832069329307695575 := by
  unfold tailWord_3393548
  simp only [CollatzResearch.WordTrace]
  refine ⟨61886431954881321350718649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82515242606508428467624865 61886431954881321350718649)
  ·
    refine ⟨46414823966160991013038987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61886431954881321350718649 46414823966160991013038987)
    ·
      refine ⟨69622235949241486519558481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46414823966160991013038987 69622235949241486519558481)
      ·
        refine ⟨52216676961931114889668861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69622235949241486519558481 52216676961931114889668861)
        ·
          refine ⟨19581253860724168083625823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52216676961931114889668861 19581253860724168083625823)
          ·
            refine ⟨29371880791086252125438735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19581253860724168083625823 29371880791086252125438735)
            ·
              refine ⟨44057821186629378188158103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29371880791086252125438735 44057821186629378188158103)
              ·
                refine ⟨66086731779944067282237155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44057821186629378188158103 66086731779944067282237155)
                ·
                  refine ⟨99130097669916100923355733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 66086731779944067282237155 99130097669916100923355733)
                  ·
                    refine ⟨1161680832069329307695575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 99130097669916100923355733 1161680832069329307695575)
                    ·
                      rfl

theorem cell22_3393548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 1, 1, 8].length) (baseStart_3393548 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3393548 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3393548 prefixEnd_3393548 := by exact prefixLift 3393548
  have htrace : WordTrace (prefixWord ++ tailWord_3393548) baseStart_3393548 baseEnd_3393548 := by
    simpa [prefixWord, tailWord_3393548, baseEnd_3393548] using wordTrace_append hprefix tailTrace_3393548
  have hstable : (prefixWord ++ tailWord_3393548).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3393548).length < 2 ^ (prefixWord ++ tailWord_3393548).sum := by decide
  have hdescent : baseEnd_3393548 < baseStart_3393548 := by decide
  rcases family_descends (prefixWord ++ tailWord_3393548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3393584 : List Nat := [2, 1, 1, 1, 2, 6, 2, 3, 1, 3]
def baseStart_3393584 : Nat := 118140960795 + 3393584 * 2 ^ 59
def prefixEnd_3393584 : Nat := 4983230072969 + 3 ^ 40 * 3393584 * 2
def baseEnd_3393584 : Nat := 1161693155605037213795465

theorem tailTrace_3393584 : CollatzResearch.WordTrace tailWord_3393584 prefixEnd_3393584 1161693155605037213795465 := by
  unfold tailWord_3393584
  simp only [CollatzResearch.WordTrace]
  refine ⟨61887088468816110424873903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82516117958421480566498537 61887088468816110424873903)
  ·
    refine ⟨92830632703224165637310855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61887088468816110424873903 92830632703224165637310855)
    ·
      refine ⟨139245949054836248455966283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92830632703224165637310855 139245949054836248455966283)
      ·
        refine ⟨208868923582254372683949425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139245949054836248455966283 208868923582254372683949425)
        ·
          refine ⟨156651692686690779512962069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 208868923582254372683949425 156651692686690779512962069)
          ·
            refine ⟨7343048094688630289670097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 156651692686690779512962069 7343048094688630289670097)
            ·
              refine ⟨5507286071016472717252573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7343048094688630289670097 5507286071016472717252573)
              ·
                refine ⟨2065232276631177268969715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5507286071016472717252573 2065232276631177268969715)
                ·
                  refine ⟨3097848414946765903454573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2065232276631177268969715 3097848414946765903454573)
                  ·
                    refine ⟨1161693155605037213795465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3097848414946765903454573 1161693155605037213795465)
                    ·
                      rfl

theorem cell22_3393584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 2, 3, 1, 3].length) (baseStart_3393584 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3393584 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3393584 prefixEnd_3393584 := by exact prefixLift 3393584
  have htrace : WordTrace (prefixWord ++ tailWord_3393584) baseStart_3393584 baseEnd_3393584 := by
    simpa [prefixWord, tailWord_3393584, baseEnd_3393584] using wordTrace_append hprefix tailTrace_3393584
  have hstable : (prefixWord ++ tailWord_3393584).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3393584).length < 2 ^ (prefixWord ++ tailWord_3393584).sum := by decide
  have hdescent : baseEnd_3393584 < baseStart_3393584 := by decide
  rcases family_descends (prefixWord ++ tailWord_3393584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3393655 : List Nat := [1, 1, 3, 1, 1, 5, 1, 1, 4, 4]
def baseStart_3393655 : Nat := 118140960795 + 3393655 * 2 ^ 59
def prefixEnd_3393655 : Nat := 4983230072969 + 3 ^ 40 * 3393655 * 2
def baseEnd_3393655 : Nat := 1161717460356016695270247

theorem tailTrace_3393655 : CollatzResearch.WordTrace tailWord_3393655 prefixEnd_3393655 1161717460356016695270247 := by
  unfold tailWord_3393655
  simp only [CollatzResearch.WordTrace]
  refine ⟨123776766520374999975582419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82517844346916666650388279 123776766520374999975582419)
  ·
    refine ⟨185665149780562499963373629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123776766520374999975582419 185665149780562499963373629)
    ·
      refine ⟨69624431167710937486265111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 185665149780562499963373629 69624431167710937486265111)
      ·
        refine ⟨104436646751566406229397667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69624431167710937486265111 104436646751566406229397667)
        ·
          refine ⟨156654970127349609344096501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104436646751566406229397667 156654970127349609344096501)
          ·
            refine ⟨14686403449439025876009047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 156654970127349609344096501 14686403449439025876009047)
            ·
              refine ⟨22029605174158538814013571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14686403449439025876009047 22029605174158538814013571)
              ·
                refine ⟨33044407761237808221020357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22029605174158538814013571 33044407761237808221020357)
                ·
                  refine ⟨6195826455232089041441317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33044407761237808221020357 6195826455232089041441317)
                  ·
                    refine ⟨1161717460356016695270247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6195826455232089041441317 1161717460356016695270247)
                    ·
                      rfl

theorem cell22_3393655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 1, 1, 4, 4].length) (baseStart_3393655 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3393655 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3393655 prefixEnd_3393655 := by exact prefixLift 3393655
  have htrace : WordTrace (prefixWord ++ tailWord_3393655) baseStart_3393655 baseEnd_3393655 := by
    simpa [prefixWord, tailWord_3393655, baseEnd_3393655] using wordTrace_append hprefix tailTrace_3393655
  have hstable : (prefixWord ++ tailWord_3393655).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3393655).length < 2 ^ (prefixWord ++ tailWord_3393655).sum := by decide
  have hdescent : baseEnd_3393655 < baseStart_3393655 := by decide
  rcases family_descends (prefixWord ++ tailWord_3393655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3393657 : List Nat := [1, 2, 1, 3, 4, 1, 2, 1, 4, 3]
def baseStart_3393657 : Nat := 118140960795 + 3393657 * 2 ^ 59
def prefixEnd_3393657 : Nat := 4983230072969 + 3 ^ 40 * 3393657 * 2
def baseEnd_3393657 : Nat := 1161718144996889356720241

theorem tailTrace_3393657 : CollatzResearch.WordTrace tailWord_3393657 prefixEnd_3393657 1161718144996889356720241 := by
  unfold tailWord_3393657
  simp only [CollatzResearch.WordTrace]
  refine ⟨123776839466367754317155225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82517892977578502878103483 123776839466367754317155225)
  ·
    refine ⟨92832629599775815737866419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123776839466367754317155225 92832629599775815737866419)
    ·
      refine ⟨139248944399663723606799629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92832629599775815737866419 139248944399663723606799629)
      ·
        refine ⟨52218354149873896352549861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 139248944399663723606799629 52218354149873896352549861)
        ·
          refine ⟨9790941403101355566103099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52218354149873896352549861 9790941403101355566103099)
          ·
            refine ⟨14686412104652033349154649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9790941403101355566103099 14686412104652033349154649)
            ·
              refine ⟨11014809078489025011865987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14686412104652033349154649 11014809078489025011865987)
              ·
                refine ⟨16522213617733537517798981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11014809078489025011865987 16522213617733537517798981)
                ·
                  refine ⟨3097915053325038284587309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16522213617733537517798981 3097915053325038284587309)
                  ·
                    refine ⟨1161718144996889356720241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3097915053325038284587309 1161718144996889356720241)
                    ·
                      rfl

theorem cell22_3393657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 2, 1, 4, 3].length) (baseStart_3393657 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3393657 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3393657 prefixEnd_3393657 := by exact prefixLift 3393657
  have htrace : WordTrace (prefixWord ++ tailWord_3393657) baseStart_3393657 baseEnd_3393657 := by
    simpa [prefixWord, tailWord_3393657, baseEnd_3393657] using wordTrace_append hprefix tailTrace_3393657
  have hstable : (prefixWord ++ tailWord_3393657).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3393657).length < 2 ^ (prefixWord ++ tailWord_3393657).sum := by decide
  have hdescent : baseEnd_3393657 < baseStart_3393657 := by decide
  rcases family_descends (prefixWord ++ tailWord_3393657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3393674 : List Nat := [3, 1, 2, 3, 1, 3, 1, 3, 2, 3]
def baseStart_3393674 : Nat := 118140960795 + 3393674 * 2 ^ 59
def prefixEnd_3393674 : Nat := 4983230072969 + 3 ^ 40 * 3393674 * 2
def baseEnd_3393674 : Nat := 1161723964444306979045189

theorem tailTrace_3393674 : CollatzResearch.WordTrace tailWord_3393674 prefixEnd_3393674 1161723964444306979045189 := by
  unfold tailWord_3393674
  simp only [CollatzResearch.WordTrace]
  refine ⟨30944364876826541555131019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82518306338204110813682717 30944364876826541555131019)
  ·
    refine ⟨46416547315239812332696529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30944364876826541555131019 46416547315239812332696529)
    ·
      refine ⟨34812410486429859249522397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46416547315239812332696529 34812410486429859249522397)
      ·
        refine ⟨13054653932411197218570899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34812410486429859249522397 13054653932411197218570899)
        ·
          refine ⟨19581980898616795827856349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13054653932411197218570899 19581980898616795827856349)
          ·
            refine ⟨7343242836981298435446131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19581980898616795827856349 7343242836981298435446131)
            ·
              refine ⟨11014864255471947653169197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7343242836981298435446131 11014864255471947653169197)
              ·
                refine ⟨4130574095801980369938449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11014864255471947653169197 4130574095801980369938449)
                ·
                  refine ⟨3097930571851485277453837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4130574095801980369938449 3097930571851485277453837)
                  ·
                    refine ⟨1161723964444306979045189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3097930571851485277453837 1161723964444306979045189)
                    ·
                      rfl

theorem cell22_3393674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 1, 3, 2, 3].length) (baseStart_3393674 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3393674 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3393674 prefixEnd_3393674 := by exact prefixLift 3393674
  have htrace : WordTrace (prefixWord ++ tailWord_3393674) baseStart_3393674 baseEnd_3393674 := by
    simpa [prefixWord, tailWord_3393674, baseEnd_3393674] using wordTrace_append hprefix tailTrace_3393674
  have hstable : (prefixWord ++ tailWord_3393674).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3393674).length < 2 ^ (prefixWord ++ tailWord_3393674).sum := by decide
  have hdescent : baseEnd_3393674 < baseStart_3393674 := by decide
  rcases family_descends (prefixWord ++ tailWord_3393674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3393710 : List Nat := [4, 1, 4, 2, 1, 2, 2, 2, 4]
def baseStart_3393710 : Nat := 118140960795 + 3393710 * 2 ^ 59
def prefixEnd_3393710 : Nat := 4983230072969 + 3 ^ 40 * 3393710 * 2
def baseEnd_3393710 : Nat := 387245429326671628381693

theorem tailTrace_3393710 : CollatzResearch.WordTrace tailWord_3393710 prefixEnd_3393710 387245429326671628381693 := by
  unfold tailWord_3393710
  simp only [CollatzResearch.WordTrace]
  refine ⟨15472346566896968046104323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 82519181690117162912556389 15472346566896968046104323)
  ·
    refine ⟨23208519850345452069156485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15472346566896968046104323 23208519850345452069156485)
    ·
      refine ⟨4351597471939772262966841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23208519850345452069156485 4351597471939772262966841)
      ·
        refine ⟨3263698103954829197225131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4351597471939772262966841 3263698103954829197225131)
        ·
          refine ⟨4895547155932243795837697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3263698103954829197225131 4895547155932243795837697)
          ·
            refine ⟨3671660366949182846878273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4895547155932243795837697 3671660366949182846878273)
            ·
              refine ⟨2753745275211887135158705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3671660366949182846878273 2753745275211887135158705)
              ·
                refine ⟨2065308956408915351369029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2753745275211887135158705 2065308956408915351369029)
                ·
                  refine ⟨387245429326671628381693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2065308956408915351369029 387245429326671628381693)
                  ·
                    rfl

theorem cell22_3393710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 2, 2, 2, 4].length) (baseStart_3393710 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3393710 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3393710 prefixEnd_3393710 := by exact prefixLift 3393710
  have htrace : WordTrace (prefixWord ++ tailWord_3393710) baseStart_3393710 baseEnd_3393710 := by
    simpa [prefixWord, tailWord_3393710, baseEnd_3393710] using wordTrace_append hprefix tailTrace_3393710
  have hstable : (prefixWord ++ tailWord_3393710).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3393710).length < 2 ^ (prefixWord ++ tailWord_3393710).sum := by decide
  have hdescent : baseEnd_3393710 < baseStart_3393710 := by decide
  rcases family_descends (prefixWord ++ tailWord_3393710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3393760 : List Nat := [2, 1, 1, 3, 1, 3, 1, 2, 8]
def baseStart_3393760 : Nat := 118140960795 + 3393760 * 2 ^ 59
def prefixEnd_3393760 : Nat := 4983230072969 + 3 ^ 40 * 3393760 * 2
def baseEnd_3393760 : Nat := 387251134667277140464975

theorem tailTrace_3393760 : CollatzResearch.WordTrace tailWord_3393760 prefixEnd_3393760 387251134667277140464975 := by
  unfold tailWord_3393760
  simp only [CollatzResearch.WordTrace]
  refine ⟨61890298092497301454077367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82520397456663068605436489 61890298092497301454077367)
  ·
    refine ⟨92835447138745952181116051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61890298092497301454077367 92835447138745952181116051)
    ·
      refine ⟨139253170708118928271674077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92835447138745952181116051 139253170708118928271674077)
      ·
        refine ⟨52219939015544598101877779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 139253170708118928271674077 52219939015544598101877779)
        ·
          refine ⟨78329908523316897152816669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52219939015544598101877779 78329908523316897152816669)
          ·
            refine ⟨29373715696243836432306251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78329908523316897152816669 29373715696243836432306251)
            ·
              refine ⟨44060573544365754648459377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29373715696243836432306251 44060573544365754648459377)
              ·
                refine ⟨33045430158274315986344533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44060573544365754648459377 33045430158274315986344533)
                ·
                  refine ⟨387251134667277140464975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 33045430158274315986344533 387251134667277140464975)
                  ·
                    rfl

theorem cell22_3393760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 2, 8].length) (baseStart_3393760 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3393760 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3393760 prefixEnd_3393760 := by exact prefixLift 3393760
  have htrace : WordTrace (prefixWord ++ tailWord_3393760) baseStart_3393760 baseEnd_3393760 := by
    simpa [prefixWord, tailWord_3393760, baseEnd_3393760] using wordTrace_append hprefix tailTrace_3393760
  have hstable : (prefixWord ++ tailWord_3393760).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3393760).length < 2 ^ (prefixWord ++ tailWord_3393760).sum := by decide
  have hdescent : baseEnd_3393760 < baseStart_3393760 := by decide
  rcases family_descends (prefixWord ++ tailWord_3393760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3393792 : List Nat := [2, 1, 1, 2, 1, 1, 7, 1, 1, 5]
def baseStart_3393792 : Nat := 118140960795 + 3393792 * 2 ^ 59
def prefixEnd_3393792 : Nat := 4983230072969 + 3 ^ 40 * 3393792 * 2
def baseEnd_3393792 : Nat := 1161764358255794004594827

theorem tailTrace_3393792 : CollatzResearch.WordTrace tailWord_3393792 prefixEnd_3393792 1161764358255794004594827 := by
  unfold tailWord_3393792
  simp only [CollatzResearch.WordTrace]
  refine ⟨61890881660439336186659815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82521175547252448248879753 61890881660439336186659815)
  ·
    refine ⟨92836322490659004279989723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61890881660439336186659815 92836322490659004279989723)
    ·
      refine ⟨139254483735988506419984585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92836322490659004279989723 139254483735988506419984585)
      ·
        refine ⟨104440862801991379814988439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139254483735988506419984585 104440862801991379814988439)
        ·
          refine ⟨156661294202987069722482659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104440862801991379814988439 156661294202987069722482659)
          ·
            refine ⟨234991941304480604583723989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 156661294202987069722482659 234991941304480604583723989)
            ·
              refine ⟨5507623624323764169931031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 234991941304480604583723989 5507623624323764169931031)
              ·
                refine ⟨8261435436485646254896547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5507623624323764169931031 8261435436485646254896547)
                ·
                  refine ⟨12392153154728469382344821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8261435436485646254896547 12392153154728469382344821)
                  ·
                    refine ⟨1161764358255794004594827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12392153154728469382344821 1161764358255794004594827)
                    ·
                      rfl

theorem cell22_3393792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 7, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 7, 1, 1, 5].length) (baseStart_3393792 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3393792 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3393792 prefixEnd_3393792 := by exact prefixLift 3393792
  have htrace : WordTrace (prefixWord ++ tailWord_3393792) baseStart_3393792 baseEnd_3393792 := by
    simpa [prefixWord, tailWord_3393792, baseEnd_3393792] using wordTrace_append hprefix tailTrace_3393792
  have hstable : (prefixWord ++ tailWord_3393792).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3393792).length < 2 ^ (prefixWord ++ tailWord_3393792).sum := by decide
  have hdescent : baseEnd_3393792 < baseStart_3393792 := by decide
  rcases family_descends (prefixWord ++ tailWord_3393792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3393794 : List Nat := [3, 4, 1, 1, 2, 1, 2, 2, 6]
def baseStart_3393794 : Nat := 118140960795 + 3393794 * 2 ^ 59
def prefixEnd_3393794 : Nat := 4983230072969 + 3 ^ 40 * 3393794 * 2
def baseEnd_3393794 : Nat := 387255014298888888681607

theorem tailTrace_3393794 : CollatzResearch.WordTrace tailWord_3393794 prefixEnd_3393794 387255014298888888681607 := by
  unfold tailWord_3393794
  simp only [CollatzResearch.WordTrace]
  refine ⟨30945459066717856678723109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82521224177914284476594957 30945459066717856678723109)
  ·
    refine ⟨5802273575009598127260583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30945459066717856678723109 5802273575009598127260583)
    ·
      refine ⟨8703410362514397190890875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5802273575009598127260583 8703410362514397190890875)
      ·
        refine ⟨13055115543771595786336313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8703410362514397190890875 13055115543771595786336313)
        ·
          refine ⟨9791336657828696839752235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13055115543771595786336313 9791336657828696839752235)
          ·
            refine ⟨14687004986743045259628353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9791336657828696839752235 14687004986743045259628353)
            ·
              refine ⟨11015253740057283944721265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14687004986743045259628353 11015253740057283944721265)
              ·
                refine ⟨8261440305042962958540949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11015253740057283944721265 8261440305042962958540949)
                ·
                  refine ⟨387255014298888888681607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8261440305042962958540949 387255014298888888681607)
                  ·
                    rfl

theorem cell22_3393794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 2, 2, 6].length) (baseStart_3393794 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3393794 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3393794 prefixEnd_3393794 := by exact prefixLift 3393794
  have htrace : WordTrace (prefixWord ++ tailWord_3393794) baseStart_3393794 baseEnd_3393794 := by
    simpa [prefixWord, tailWord_3393794, baseEnd_3393794] using wordTrace_append hprefix tailTrace_3393794
  have hstable : (prefixWord ++ tailWord_3393794).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3393794).length < 2 ^ (prefixWord ++ tailWord_3393794).sum := by decide
  have hdescent : baseEnd_3393794 < baseStart_3393794 := by decide
  rcases family_descends (prefixWord ++ tailWord_3393794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3393796 : List Nat := [2, 3, 2, 2, 3, 1, 2, 2, 1, 4]
def baseStart_3393796 : Nat := 118140960795 + 3393796 * 2 ^ 59
def prefixEnd_3393796 : Nat := 4983230072969 + 3 ^ 40 * 3393796 * 2
def baseEnd_3393796 : Nat := 1161765727537539327494815

theorem tailTrace_3393796 : CollatzResearch.WordTrace tailWord_3393796 prefixEnd_3393796 1161765727537539327494815 := by
  unfold tailWord_3393796
  simp only [CollatzResearch.WordTrace]
  refine ⟨61890954606432090528232621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82521272808576120704310161 61890954606432090528232621)
  ·
    refine ⟨23209107977412033948087233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61890954606432090528232621 23209107977412033948087233)
    ·
      refine ⟨17406830983059025461065425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23209107977412033948087233 17406830983059025461065425)
      ·
        refine ⟨13055123237294269095799069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17406830983059025461065425 13055123237294269095799069)
        ·
          refine ⟨4895671213985350910924651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13055123237294269095799069 4895671213985350910924651)
          ·
            refine ⟨7343506820978026366386977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4895671213985350910924651 7343506820978026366386977)
            ·
              refine ⟨5507630115733519774790233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7343506820978026366386977 5507630115733519774790233)
              ·
                refine ⟨4130722586800139831092675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5507630115733519774790233 4130722586800139831092675)
                ·
                  refine ⟨6196083880200209746639013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4130722586800139831092675 6196083880200209746639013)
                  ·
                    refine ⟨1161765727537539327494815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6196083880200209746639013 1161765727537539327494815)
                    ·
                      rfl

theorem cell22_3393796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 2, 2, 1, 4].length) (baseStart_3393796 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3393796 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3393796 prefixEnd_3393796 := by exact prefixLift 3393796
  have htrace : WordTrace (prefixWord ++ tailWord_3393796) baseStart_3393796 baseEnd_3393796 := by
    simpa [prefixWord, tailWord_3393796, baseEnd_3393796] using wordTrace_append hprefix tailTrace_3393796
  have hstable : (prefixWord ++ tailWord_3393796).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3393796).length < 2 ^ (prefixWord ++ tailWord_3393796).sum := by decide
  have hdescent : baseEnd_3393796 < baseStart_3393796 := by decide
  rcases family_descends (prefixWord ++ tailWord_3393796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3393824 : List Nat := [2, 1, 1, 5, 2, 2, 1, 2, 2, 4]
def baseStart_3393824 : Nat := 118140960795 + 3393824 * 2 ^ 59
def prefixEnd_3393824 : Nat := 4983230072969 + 3 ^ 40 * 3393824 * 2
def baseEnd_3393824 : Nat := 1161775312509756587794729

theorem tailTrace_3393824 : CollatzResearch.WordTrace tailWord_3393824 prefixEnd_3393824 1161775312509756587794729 := by
  unfold tailWord_3393824
  simp only [CollatzResearch.WordTrace]
  refine ⟨61891465228381370919242263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82521953637841827892323017 61891465228381370919242263)
  ·
    refine ⟨92837197842572056378863395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61891465228381370919242263 92837197842572056378863395)
    ·
      refine ⟨139255796763858084568295093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92837197842572056378863395 139255796763858084568295093)
      ·
        refine ⟨13055230946611695428277665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 139255796763858084568295093 13055230946611695428277665)
        ·
          refine ⟨9791423209958771571208249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13055230946611695428277665 9791423209958771571208249)
          ·
            refine ⟨7343567407469078678406187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9791423209958771571208249 7343567407469078678406187)
            ·
              refine ⟨11015351111203618017609281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7343567407469078678406187 11015351111203618017609281)
              ·
                refine ⟨8261513333402713513206961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11015351111203618017609281 8261513333402713513206961)
                ·
                  refine ⟨6196135000052035134905221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8261513333402713513206961 6196135000052035134905221)
                  ·
                    refine ⟨1161775312509756587794729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6196135000052035134905221 1161775312509756587794729)
                    ·
                      rfl

theorem cell22_3393824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 1, 2, 2, 4].length) (baseStart_3393824 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3393824 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3393824 prefixEnd_3393824 := by exact prefixLift 3393824
  have htrace : WordTrace (prefixWord ++ tailWord_3393824) baseStart_3393824 baseEnd_3393824 := by
    simpa [prefixWord, tailWord_3393824, baseEnd_3393824] using wordTrace_append hprefix tailTrace_3393824
  have hstable : (prefixWord ++ tailWord_3393824).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3393824).length < 2 ^ (prefixWord ++ tailWord_3393824).sum := by decide
  have hdescent : baseEnd_3393824 < baseStart_3393824 := by decide
  rcases family_descends (prefixWord ++ tailWord_3393824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3393882 : List Nat := [3, 1, 1, 2, 1, 2, 1, 4, 2, 5]
def baseStart_3393882 : Nat := 118140960795 + 3393882 * 2 ^ 59
def prefixEnd_3393882 : Nat := 4983230072969 + 3 ^ 40 * 3393882 * 2
def baseEnd_3393882 : Nat := 1161795167095063769844551

theorem tailTrace_3393882 : CollatzResearch.WordTrace tailWord_3393882 prefixEnd_3393882 1161795167095063769844551 := by
  unfold tailWord_3393882
  simp only [CollatzResearch.WordTrace]
  refine ⟨30946261472638154436023975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82523363927035078496063933 30946261472638154436023975)
  ·
    refine ⟨46419392208957231654035963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30946261472638154436023975 46419392208957231654035963)
    ·
      refine ⟨69629088313435847481053945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46419392208957231654035963 69629088313435847481053945)
      ·
        refine ⟨52221816235076885610790459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69629088313435847481053945 52221816235076885610790459)
        ·
          refine ⟨78332724352615328416185689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52221816235076885610790459 78332724352615328416185689)
          ·
            refine ⟨58749543264461496312139267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78332724352615328416185689 58749543264461496312139267)
            ·
              refine ⟨88124314896692244468208901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58749543264461496312139267 88124314896692244468208901)
              ·
                refine ⟨16523309043129795837789169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 88124314896692244468208901 16523309043129795837789169)
                ·
                  refine ⟨12392481782347346878341877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16523309043129795837789169 12392481782347346878341877)
                  ·
                    refine ⟨1161795167095063769844551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12392481782347346878341877 1161795167095063769844551)
                    ·
                      rfl

theorem cell22_3393882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 4, 2, 5].length) (baseStart_3393882 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3393882 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3393882 prefixEnd_3393882 := by exact prefixLift 3393882
  have htrace : WordTrace (prefixWord ++ tailWord_3393882) baseStart_3393882 baseEnd_3393882 := by
    simpa [prefixWord, tailWord_3393882, baseEnd_3393882] using wordTrace_append hprefix tailTrace_3393882
  have hstable : (prefixWord ++ tailWord_3393882).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3393882).length < 2 ^ (prefixWord ++ tailWord_3393882).sum := by decide
  have hdescent : baseEnd_3393882 < baseStart_3393882 := by decide
  rcases family_descends (prefixWord ++ tailWord_3393882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3393888 : List Nat := [2, 1, 1, 3, 5, 1, 1, 4, 1, 3]
def baseStart_3393888 : Nat := 118140960795 + 3393888 * 2 ^ 59
def prefixEnd_3393888 : Nat := 4983230072969 + 3 ^ 40 * 3393888 * 2
def baseEnd_3393888 : Nat := 1161797221017681754194533

theorem tailTrace_3393888 : CollatzResearch.WordTrace tailWord_3393888 prefixEnd_3393888 1161797221017681754194533 := by
  unfold tailWord_3393888
  simp only [CollatzResearch.WordTrace]
  refine ⟨61892632364265440384407159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82523509819020587179209545 61892632364265440384407159)
  ·
    refine ⟨92838948546398160576610739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61892632364265440384407159 92838948546398160576610739)
    ·
      refine ⟨139258422819597240864916109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92838948546398160576610739 139258422819597240864916109)
      ·
        refine ⟨52221908557348965324343541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 139258422819597240864916109 52221908557348965324343541)
        ·
          refine ⟨4895803927251465499157207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 52221908557348965324343541 4895803927251465499157207)
          ·
            refine ⟨7343705890877198248735811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4895803927251465499157207 7343705890877198248735811)
            ·
              refine ⟨11015558836315797373103717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7343705890877198248735811 11015558836315797373103717)
              ·
                refine ⟨2065417281809212007456947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11015558836315797373103717 2065417281809212007456947)
                ·
                  refine ⟨3098125922713818011185421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2065417281809212007456947 3098125922713818011185421)
                  ·
                    refine ⟨1161797221017681754194533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3098125922713818011185421 1161797221017681754194533)
                    ·
                      rfl

theorem cell22_3393888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 1, 4, 1, 3].length) (baseStart_3393888 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3393888 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3393888 prefixEnd_3393888 := by exact prefixLift 3393888
  have htrace : WordTrace (prefixWord ++ tailWord_3393888) baseStart_3393888 baseEnd_3393888 := by
    simpa [prefixWord, tailWord_3393888, baseEnd_3393888] using wordTrace_append hprefix tailTrace_3393888
  have hstable : (prefixWord ++ tailWord_3393888).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3393888).length < 2 ^ (prefixWord ++ tailWord_3393888).sum := by decide
  have hdescent : baseEnd_3393888 < baseStart_3393888 := by decide
  rcases family_descends (prefixWord ++ tailWord_3393888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3393897 : List Nat := [1, 2, 1, 1, 1, 3, 3, 1, 5, 4]
def baseStart_3393897 : Nat := 118140960795 + 3393897 * 2 ^ 59
def prefixEnd_3393897 : Nat := 4983230072969 + 3 ^ 40 * 3393897 * 2
def baseEnd_3393897 : Nat := 1161800301901608730719505

theorem tailTrace_3393897 : CollatzResearch.WordTrace tailWord_3393897 prefixEnd_3393897 1161800301901608730719505 := by
  unfold tailWord_3393897
  simp only [CollatzResearch.WordTrace]
  refine ⟨123785592985498275305891945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82523728656998850203927963 123785592985498275305891945)
  ·
    refine ⟨92839194739123706479418959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123785592985498275305891945 92839194739123706479418959)
    ·
      refine ⟨139258792108685559719128439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92839194739123706479418959 139258792108685559719128439)
      ·
        refine ⟨208888188163028339578692659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139258792108685559719128439 208888188163028339578692659)
        ·
          refine ⟨313332282244542509368038989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 208888188163028339578692659 313332282244542509368038989)
          ·
            refine ⟨117499605841703441013014621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 313332282244542509368038989 117499605841703441013014621)
            ·
              refine ⟨44062352190638790379880483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 117499605841703441013014621 44062352190638790379880483)
              ·
                refine ⟨66093528285958185569820725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44062352190638790379880483 66093528285958185569820725)
                ·
                  refine ⟨6196268276808579897170693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 66093528285958185569820725 6196268276808579897170693)
                  ·
                    refine ⟨1161800301901608730719505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6196268276808579897170693 1161800301901608730719505)
                    ·
                      rfl

theorem cell22_3393897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 1, 5, 4].length) (baseStart_3393897 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3393897 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3393897 prefixEnd_3393897 := by exact prefixLift 3393897
  have htrace : WordTrace (prefixWord ++ tailWord_3393897) baseStart_3393897 baseEnd_3393897 := by
    simpa [prefixWord, tailWord_3393897, baseEnd_3393897] using wordTrace_append hprefix tailTrace_3393897
  have hstable : (prefixWord ++ tailWord_3393897).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3393897).length < 2 ^ (prefixWord ++ tailWord_3393897).sum := by decide
  have hdescent : baseEnd_3393897 < baseStart_3393897 := by decide
  rcases family_descends (prefixWord ++ tailWord_3393897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3393922 : List Nat := [3, 4, 2, 1, 2, 1, 2, 3, 1, 3]
def baseStart_3393922 : Nat := 118140960795 + 3393922 * 2 ^ 59
def prefixEnd_3393922 : Nat := 4983230072969 + 3 ^ 40 * 3393922 * 2
def baseEnd_3393922 : Nat := 1161808859912516998844429

theorem tailTrace_3393922 : CollatzResearch.WordTrace tailWord_3393922 prefixEnd_3393922 1161808859912516998844429 := by
  unfold tailWord_3393922
  simp only [CollatzResearch.WordTrace]
  refine ⟨30946626202601926143888005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82524336540271803050368013 30946626202601926143888005)
  ·
    refine ⟨5802492412987861151979001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30946626202601926143888005 5802492412987861151979001)
    ·
      refine ⟨4351869309740895863984251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5802492412987861151979001 4351869309740895863984251)
      ·
        refine ⟨6527803964611343795976377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4351869309740895863984251 6527803964611343795976377)
        ·
          refine ⟨4895852973458507846982283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6527803964611343795976377 4895852973458507846982283)
          ·
            refine ⟨7343779460187761770473425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4895852973458507846982283 7343779460187761770473425)
            ·
              refine ⟨5507834595140821327855069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7343779460187761770473425 5507834595140821327855069)
              ·
                refine ⟨2065437973177807997945651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5507834595140821327855069 2065437973177807997945651)
                ·
                  refine ⟨3098156959766711996918477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2065437973177807997945651 3098156959766711996918477)
                  ·
                    refine ⟨1161808859912516998844429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3098156959766711996918477 1161808859912516998844429)
                    ·
                      rfl

theorem cell22_3393922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 2, 3, 1, 3].length) (baseStart_3393922 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3393922 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3393922 prefixEnd_3393922 := by exact prefixLift 3393922
  have htrace : WordTrace (prefixWord ++ tailWord_3393922) baseStart_3393922 baseEnd_3393922 := by
    simpa [prefixWord, tailWord_3393922, baseEnd_3393922] using wordTrace_append hprefix tailTrace_3393922
  have hstable : (prefixWord ++ tailWord_3393922).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3393922).length < 2 ^ (prefixWord ++ tailWord_3393922).sum := by decide
  have hdescent : baseEnd_3393922 < baseStart_3393922 := by decide
  rcases family_descends (prefixWord ++ tailWord_3393922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3393931 : List Nat := [1, 1, 1, 1, 4, 4, 4, 1, 1, 4]
def baseStart_3393931 : Nat := 118140960795 + 3393931 * 2 ^ 59
def prefixEnd_3393931 : Nat := 4983230072969 + 3 ^ 40 * 3393931 * 2
def baseEnd_3393931 : Nat := 1161811940796443975369401

theorem tailTrace_3393931 : CollatzResearch.WordTrace tailWord_3393931 prefixEnd_3393931 1161811940796443975369401 := by
  unfold tailWord_3393931
  simp only [CollatzResearch.WordTrace]
  refine ⟨123786833067375099112629647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82524555378250066075086431 123786833067375099112629647)
  ·
    refine ⟨185680249601062648668944471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123786833067375099112629647 185680249601062648668944471)
    ·
      refine ⟨278520374401593973003416707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185680249601062648668944471 278520374401593973003416707)
      ·
        refine ⟨417780561602390959505125061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 278520374401593973003416707 417780561602390959505125061)
        ·
          refine ⟨78333855300448304907210949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 417780561602390959505125061 78333855300448304907210949)
          ·
            refine ⟨14687597868834057170102053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 78333855300448304907210949 14687597868834057170102053)
            ·
              refine ⟨2753924600406385719394135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14687597868834057170102053 2753924600406385719394135)
              ·
                refine ⟨4130886900609578579091203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2753924600406385719394135 4130886900609578579091203)
                ·
                  refine ⟨6196330350914367868636805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4130886900609578579091203 6196330350914367868636805)
                  ·
                    refine ⟨1161811940796443975369401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6196330350914367868636805 1161811940796443975369401)
                    ·
                      rfl

theorem cell22_3393931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 4, 1, 1, 4].length) (baseStart_3393931 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3393931 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3393931 prefixEnd_3393931 := by exact prefixLift 3393931
  have htrace : WordTrace (prefixWord ++ tailWord_3393931) baseStart_3393931 baseEnd_3393931 := by
    simpa [prefixWord, tailWord_3393931, baseEnd_3393931] using wordTrace_append hprefix tailTrace_3393931
  have hstable : (prefixWord ++ tailWord_3393931).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3393931).length < 2 ^ (prefixWord ++ tailWord_3393931).sum := by decide
  have hdescent : baseEnd_3393931 < baseStart_3393931 := by decide
  rcases family_descends (prefixWord ++ tailWord_3393931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3393946 : List Nat := [3, 1, 1, 4, 1, 2, 2, 4, 4]
def baseStart_3393946 : Nat := 118140960795 + 3393946 * 2 ^ 59
def prefixEnd_3393946 : Nat := 4983230072969 + 3 ^ 40 * 3393946 * 2
def baseEnd_3393946 : Nat := 387272358534329645414785

theorem tailTrace_3393946 : CollatzResearch.WordTrace tailWord_3393946 prefixEnd_3393946 387272358534329645414785 := by
  unfold tailWord_3393946
  simp only [CollatzResearch.WordTrace]
  refine ⟨30946845040580189168606423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82524920108213837782950461 30946845040580189168606423)
  ·
    refine ⟨46420267560870283752909635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30946845040580189168606423 46420267560870283752909635)
    ·
      refine ⟨69630401341305425629364453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46420267560870283752909635 69630401341305425629364453)
      ·
        refine ⟨13055700251494767305505835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 69630401341305425629364453 13055700251494767305505835)
        ·
          refine ⟨19583550377242150958258753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13055700251494767305505835 19583550377242150958258753)
          ·
            refine ⟨14687662782931613218694065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19583550377242150958258753 14687662782931613218694065)
            ·
              refine ⟨11015747087198709914020549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14687662782931613218694065 11015747087198709914020549)
              ·
                refine ⟨2065452578849758108878853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11015747087198709914020549 2065452578849758108878853)
                ·
                  refine ⟨387272358534329645414785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2065452578849758108878853 387272358534329645414785)
                  ·
                    rfl

theorem cell22_3393946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 2, 4, 4].length) (baseStart_3393946 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3393946 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3393946 prefixEnd_3393946 := by exact prefixLift 3393946
  have htrace : WordTrace (prefixWord ++ tailWord_3393946) baseStart_3393946 baseEnd_3393946 := by
    simpa [prefixWord, tailWord_3393946, baseEnd_3393946] using wordTrace_append hprefix tailTrace_3393946
  have hstable : (prefixWord ++ tailWord_3393946).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3393946).length < 2 ^ (prefixWord ++ tailWord_3393946).sum := by decide
  have hdescent : baseEnd_3393946 < baseStart_3393946 := by decide
  rcases family_descends (prefixWord ++ tailWord_3393946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3393957 : List Nat := [1, 3, 1, 2, 1, 1, 4, 9]
def baseStart_3393957 : Nat := 118140960795 + 3393957 * 2 ^ 59
def prefixEnd_3393957 : Nat := 4983230072969 + 3 ^ 40 * 3393957 * 2
def baseEnd_3393957 : Nat := 129091204569754286024369

theorem tailTrace_3393957 : CollatzResearch.WordTrace tailWord_3393957 prefixEnd_3393957 129091204569754286024369 := by
  unfold tailWord_3393957
  simp only [CollatzResearch.WordTrace]
  refine ⟨123787781365280905553076125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82525187576853937035384083 123787781365280905553076125)
  ·
    refine ⟨46420418011980339582403547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123787781365280905553076125 46420418011980339582403547)
    ·
      refine ⟨69630627017970509373605321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46420418011980339582403547 69630627017970509373605321)
      ·
        refine ⟨52222970263477882030203991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69630627017970509373605321 52222970263477882030203991)
        ·
          refine ⟨78334455395216823045305987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52222970263477882030203991 78334455395216823045305987)
          ·
            refine ⟨117501683092825234567958981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78334455395216823045305987 117501683092825234567958981)
            ·
              refine ⟨22031565579904731481492309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 117501683092825234567958981 22031565579904731481492309)
              ·
                refine ⟨129091204569754286024369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 22031565579904731481492309 129091204569754286024369)
                ·
                  rfl

theorem cell22_3393957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 4, 9].length) (baseStart_3393957 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3393957 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3393957 prefixEnd_3393957 := by exact prefixLift 3393957
  have htrace : WordTrace (prefixWord ++ tailWord_3393957) baseStart_3393957 baseEnd_3393957 := by
    simpa [prefixWord, tailWord_3393957, baseEnd_3393957] using wordTrace_append hprefix tailTrace_3393957
  have hstable : (prefixWord ++ tailWord_3393957).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3393957).length < 2 ^ (prefixWord ++ tailWord_3393957).sum := by decide
  have hdescent : baseEnd_3393957 < baseStart_3393957 := by decide
  rcases family_descends (prefixWord ++ tailWord_3393957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3393959 : List Nat := [1, 1, 6, 1, 1, 2, 1, 2, 1, 6]
def baseStart_3393959 : Nat := 118140960795 + 3393959 * 2 ^ 59
def prefixEnd_3393959 : Nat := 4983230072969 + 3 ^ 40 * 3393959 * 2
def baseEnd_3393959 : Nat := 1161821525768661235669315

theorem tailTrace_3393959 : CollatzResearch.WordTrace tailWord_3393959 prefixEnd_3393959 1161821525768661235669315 := by
  unfold tailWord_3393959
  simp only [CollatzResearch.WordTrace]
  refine ⟨123787854311273659894648931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82525236207515773263099287 123787854311273659894648931)
  ·
    refine ⟨185681781466910489841973397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123787854311273659894648931 185681781466910489841973397)
    ·
      refine ⟨8703833506261429211342503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 185681781466910489841973397 8703833506261429211342503)
      ·
        refine ⟨13055750259392143817013755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8703833506261429211342503 13055750259392143817013755)
        ·
          refine ⟨19583625389088215725520633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13055750259392143817013755 19583625389088215725520633)
          ·
            refine ⟨14687719041816161794140475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19583625389088215725520633 14687719041816161794140475)
            ·
              refine ⟨22031578562724242691210713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14687719041816161794140475 22031578562724242691210713)
              ·
                refine ⟨16523683922043182018408035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22031578562724242691210713 16523683922043182018408035)
                ·
                  refine ⟨24785525883064773027612053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16523683922043182018408035 24785525883064773027612053)
                  ·
                    refine ⟨1161821525768661235669315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24785525883064773027612053 1161821525768661235669315)
                    ·
                      rfl

theorem cell22_3393959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 1, 2, 1, 6].length) (baseStart_3393959 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3393959 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3393959 prefixEnd_3393959 := by exact prefixLift 3393959
  have htrace : WordTrace (prefixWord ++ tailWord_3393959) baseStart_3393959 baseEnd_3393959 := by
    simpa [prefixWord, tailWord_3393959, baseEnd_3393959] using wordTrace_append hprefix tailTrace_3393959
  have hstable : (prefixWord ++ tailWord_3393959).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3393959).length < 2 ^ (prefixWord ++ tailWord_3393959).sum := by decide
  have hdescent : baseEnd_3393959 < baseStart_3393959 := by decide
  rcases family_descends (prefixWord ++ tailWord_3393959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3393987 : List Nat := [1, 1, 1, 3, 1, 1, 3, 2, 1, 8]
def baseStart_3393987 : Nat := 118140960795 + 3393987 * 2 ^ 59
def prefixEnd_3393987 : Nat := 4983230072969 + 3 ^ 40 * 3393987 * 2
def baseEnd_3393987 : Nat := 1161831110740878495969229

theorem tailTrace_3393987 : CollatzResearch.WordTrace tailWord_3393987 prefixEnd_3393987 1161831110740878495969229 := by
  unfold tailWord_3393987
  simp only [CollatzResearch.WordTrace]
  refine ⟨123788875555172220676668215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82525917036781480451112143 123788875555172220676668215)
  ·
    refine ⟨185683313332758331015002323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123788875555172220676668215 185683313332758331015002323)
    ·
      refine ⟨278524969999137496522503485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185683313332758331015002323 278524969999137496522503485)
      ·
        refine ⟨104446863749676561195938807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 278524969999137496522503485 104446863749676561195938807)
        ·
          refine ⟨156670295624514841793908211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104446863749676561195938807 156670295624514841793908211)
          ·
            refine ⟨235005443436772262690862317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 156670295624514841793908211 235005443436772262690862317)
            ·
              refine ⟨88127041288789598509073369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 235005443436772262690862317 88127041288789598509073369)
              ·
                refine ⟨66095280966592198881805027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 88127041288789598509073369 66095280966592198881805027)
                ·
                  refine ⟨99142921449888298322707541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 66095280966592198881805027 99142921449888298322707541)
                  ·
                    refine ⟨1161831110740878495969229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 99142921449888298322707541 1161831110740878495969229)
                    ·
                      rfl

theorem cell22_3393987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 2, 1, 8].length) (baseStart_3393987 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3393987 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3393987 prefixEnd_3393987 := by exact prefixLift 3393987
  have htrace : WordTrace (prefixWord ++ tailWord_3393987) baseStart_3393987 baseEnd_3393987 := by
    simpa [prefixWord, tailWord_3393987, baseEnd_3393987] using wordTrace_append hprefix tailTrace_3393987
  have hstable : (prefixWord ++ tailWord_3393987).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3393987).length < 2 ^ (prefixWord ++ tailWord_3393987).sum := by decide
  have hdescent : baseEnd_3393987 < baseStart_3393987 := by decide
  rcases family_descends (prefixWord ++ tailWord_3393987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3394068 : List Nat := [2, 4, 3, 1, 1, 2, 1, 1, 2, 5]
def baseStart_3394068 : Nat := 118140960795 + 3394068 * 2 ^ 59
def prefixEnd_3394068 : Nat := 4983230072969 + 3 ^ 40 * 3394068 * 2
def baseEnd_3394068 : Nat := 1161858838696221284693981

theorem tailTrace_3394068 : CollatzResearch.WordTrace tailWord_3394068 prefixEnd_3394068 1161858838696221284693981 := by
  unfold tailWord_3394068
  simp only [CollatzResearch.WordTrace]
  refine ⟨61895914933939385755183429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82527886578585847673577905 61895914933939385755183429)
  ·
    refine ⟨11605484050113634829096893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 61895914933939385755183429 11605484050113634829096893)
    ·
      refine ⟨4352056518792613060911335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11605484050113634829096893 4352056518792613060911335)
      ·
        refine ⟨6528084778188919591367003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4352056518792613060911335 6528084778188919591367003)
        ·
          refine ⟨9792127167283379387050505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6528084778188919591367003 9792127167283379387050505)
          ·
            refine ⟨7344095375462534540287879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9792127167283379387050505 7344095375462534540287879)
            ·
              refine ⟨11016143063193801810431819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7344095375462534540287879 11016143063193801810431819)
              ·
                refine ⟨16524214594790702715647729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11016143063193801810431819 16524214594790702715647729)
                ·
                  refine ⟨12393160946093027036735797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16524214594790702715647729 12393160946093027036735797)
                  ·
                    refine ⟨1161858838696221284693981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12393160946093027036735797 1161858838696221284693981)
                    ·
                      rfl

theorem cell22_3394068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 1, 1, 2, 5].length) (baseStart_3394068 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3394068 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3394068 prefixEnd_3394068 := by exact prefixLift 3394068
  have htrace : WordTrace (prefixWord ++ tailWord_3394068) baseStart_3394068 baseEnd_3394068 := by
    simpa [prefixWord, tailWord_3394068, baseEnd_3394068] using wordTrace_append hprefix tailTrace_3394068
  have hstable : (prefixWord ++ tailWord_3394068).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3394068).length < 2 ^ (prefixWord ++ tailWord_3394068).sum := by decide
  have hdescent : baseEnd_3394068 < baseStart_3394068 := by decide
  rcases family_descends (prefixWord ++ tailWord_3394068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3394113 : List Nat := [1, 2, 5, 1, 1, 3, 1, 1, 4, 3]
def baseStart_3394113 : Nat := 118140960795 + 3394113 * 2 ^ 59
def prefixEnd_3394113 : Nat := 4983230072969 + 3 ^ 40 * 3394113 * 2
def baseEnd_3394113 : Nat := 1161874243115856167318843

theorem tailTrace_3394113 : CollatzResearch.WordTrace tailWord_3394113 prefixEnd_3394113 1161874243115856167318843 := by
  unfold tailWord_3394113
  simp only [CollatzResearch.WordTrace]
  refine ⟨123793471152715744195754993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82528980768477162797169995 123793471152715744195754993)
  ·
    refine ⟨92845103364536808146816245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123793471152715744195754993 92845103364536808146816245)
    ·
      refine ⟨8704228440425325763764023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 92845103364536808146816245 8704228440425325763764023)
      ·
        refine ⟨13056342660637988645646035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8704228440425325763764023 13056342660637988645646035)
        ·
          refine ⟨19584513990956982968469053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13056342660637988645646035 19584513990956982968469053)
          ·
            refine ⟨7344192746608868613175895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19584513990956982968469053 7344192746608868613175895)
            ·
              refine ⟨11016289119913302919763843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7344192746608868613175895 11016289119913302919763843)
              ·
                refine ⟨16524433679869954379645765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11016289119913302919763843 16524433679869954379645765)
                ·
                  refine ⟨3098331314975616446183581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16524433679869954379645765 3098331314975616446183581)
                  ·
                    refine ⟨1161874243115856167318843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3098331314975616446183581 1161874243115856167318843)
                    ·
                      rfl

theorem cell22_3394113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 1, 1, 4, 3].length) (baseStart_3394113 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3394113 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3394113 prefixEnd_3394113 := by exact prefixLift 3394113
  have htrace : WordTrace (prefixWord ++ tailWord_3394113) baseStart_3394113 baseEnd_3394113 := by
    simpa [prefixWord, tailWord_3394113, baseEnd_3394113] using wordTrace_append hprefix tailTrace_3394113
  have hstable : (prefixWord ++ tailWord_3394113).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3394113).length < 2 ^ (prefixWord ++ tailWord_3394113).sum := by decide
  have hdescent : baseEnd_3394113 < baseStart_3394113 := by decide
  rcases family_descends (prefixWord ++ tailWord_3394113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3394130 : List Nat := [3, 2, 2, 1, 2, 1, 5, 1, 2, 3]
def baseStart_3394130 : Nat := 118140960795 + 3394130 * 2 ^ 59
def prefixEnd_3394130 : Nat := 4983230072969 + 3 ^ 40 * 3394130 * 2
def baseEnd_3394130 : Nat := 1161880062563273789643791

theorem tailTrace_3394130 : CollatzResearch.WordTrace tailWord_3394130 prefixEnd_3394130 1161880062563273789643791 := by
  unfold tailWord_3394130
  simp only [CollatzResearch.WordTrace]
  refine ⟨30948522798413539024780961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82529394129102770732749229 30948522798413539024780961)
  ·
    refine ⟨23211392098810154268585721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30948522798413539024780961 23211392098810154268585721)
    ·
      refine ⟨17408544074107615701439291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23211392098810154268585721 17408544074107615701439291)
      ·
        refine ⟨26112816111161423552158937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17408544074107615701439291 26112816111161423552158937)
        ·
          refine ⟨19584612083371067664119203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26112816111161423552158937 19584612083371067664119203)
          ·
            refine ⟨29376918125056601496178805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19584612083371067664119203 29376918125056601496178805)
            ·
              refine ⟨2754086074224056390266763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 29376918125056601496178805 2754086074224056390266763)
              ·
                refine ⟨4131129111336084585400145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2754086074224056390266763 4131129111336084585400145)
                ·
                  refine ⟨3098346833502063439050109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4131129111336084585400145 3098346833502063439050109)
                  ·
                    refine ⟨1161880062563273789643791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3098346833502063439050109 1161880062563273789643791)
                    ·
                      rfl

theorem cell22_3394130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 5, 1, 2, 3].length) (baseStart_3394130 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3394130 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3394130 prefixEnd_3394130 := by exact prefixLift 3394130
  have htrace : WordTrace (prefixWord ++ tailWord_3394130) baseStart_3394130 baseEnd_3394130 := by
    simpa [prefixWord, tailWord_3394130, baseEnd_3394130] using wordTrace_append hprefix tailTrace_3394130
  have hstable : (prefixWord ++ tailWord_3394130).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3394130).length < 2 ^ (prefixWord ++ tailWord_3394130).sum := by decide
  have hdescent : baseEnd_3394130 < baseStart_3394130 := by decide
  rcases family_descends (prefixWord ++ tailWord_3394130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3394201 : List Nat := [1, 2, 1, 2, 1, 2, 5, 1, 3, 4]
def baseStart_3394201 : Nat := 118140960795 + 3394201 * 2 ^ 59
def prefixEnd_3394201 : Nat := 4983230072969 + 3 ^ 40 * 3394201 * 2
def baseEnd_3394201 : Nat := 1161904367314253271118573

theorem tailTrace_3394201 : CollatzResearch.WordTrace tailWord_3394201 prefixEnd_3394201 1161904367314253271118573 := by
  unfold tailWord_3394201
  simp only [CollatzResearch.WordTrace]
  refine ⟨123796680776396935224958457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82531120517597956816638971 123796680776396935224958457)
  ·
    refine ⟨92847510582297701418718843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123796680776396935224958457 92847510582297701418718843)
    ·
      refine ⟨139271265873446552128078265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92847510582297701418718843 139271265873446552128078265)
      ·
        refine ⟨104453449405084914096058699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139271265873446552128078265 104453449405084914096058699)
        ·
          refine ⟨156680174107627371144088049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104453449405084914096058699 156680174107627371144088049)
          ·
            refine ⟨117510130580720528358066037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 156680174107627371144088049 117510130580720528358066037)
            ·
              refine ⟨11016574741942549533568691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 117510130580720528358066037 11016574741942549533568691)
              ·
                refine ⟨16524862112913824300353037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11016574741942549533568691 16524862112913824300353037)
                ·
                  refine ⟨6196823292342684112632389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16524862112913824300353037 6196823292342684112632389)
                  ·
                    refine ⟨1161904367314253271118573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6196823292342684112632389 1161904367314253271118573)
                    ·
                      rfl

theorem cell22_3394201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 5, 1, 3, 4].length) (baseStart_3394201 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3394201 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3394201 prefixEnd_3394201 := by exact prefixLift 3394201
  have htrace : WordTrace (prefixWord ++ tailWord_3394201) baseStart_3394201 baseEnd_3394201 := by
    simpa [prefixWord, tailWord_3394201, baseEnd_3394201] using wordTrace_append hprefix tailTrace_3394201
  have hstable : (prefixWord ++ tailWord_3394201).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3394201).length < 2 ^ (prefixWord ++ tailWord_3394201).sum := by decide
  have hdescent : baseEnd_3394201 < baseStart_3394201 := by decide
  rcases family_descends (prefixWord ++ tailWord_3394201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3394248 : List Nat := [2, 1, 3, 1, 2, 4, 2, 1, 1, 5]
def baseStart_3394248 : Nat := 118140960795 + 3394248 * 2 ^ 59
def prefixEnd_3394248 : Nat := 4983230072969 + 3 ^ 40 * 3394248 * 2
def baseEnd_3394248 : Nat := 1161920456374760815193429

theorem tailTrace_3394248 : CollatzResearch.WordTrace tailWord_3394248 prefixEnd_3394248 1161920456374760815193429 := by
  unfold tailWord_3394248
  simp only [CollatzResearch.WordTrace]
  refine ⟨61899197503613331125959699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82532263338151108167946265 61899197503613331125959699)
  ·
    refine ⟨92848796255419996688939549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61899197503613331125959699 92848796255419996688939549)
    ·
      refine ⟨34818298595782498758352331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92848796255419996688939549 34818298595782498758352331)
      ·
        refine ⟨52227447893673748137528497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34818298595782498758352331 52227447893673748137528497)
        ·
          refine ⟨39170585920255311103146373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52227447893673748137528497 39170585920255311103146373)
          ·
            refine ⟨7344484860047870831839945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39170585920255311103146373 7344484860047870831839945)
            ·
              refine ⟨5508363645035903123879959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7344484860047870831839945 5508363645035903123879959)
              ·
                refine ⟨8262545467553854685819939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5508363645035903123879959 8262545467553854685819939)
                ·
                  refine ⟨12393818201330782028729909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8262545467553854685819939 12393818201330782028729909)
                  ·
                    refine ⟨1161920456374760815193429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12393818201330782028729909 1161920456374760815193429)
                    ·
                      rfl

theorem cell22_3394248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 2, 1, 1, 5].length) (baseStart_3394248 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3394248 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3394248 prefixEnd_3394248 := by exact prefixLift 3394248
  have htrace : WordTrace (prefixWord ++ tailWord_3394248) baseStart_3394248 baseEnd_3394248 := by
    simpa [prefixWord, tailWord_3394248, baseEnd_3394248] using wordTrace_append hprefix tailTrace_3394248
  have hstable : (prefixWord ++ tailWord_3394248).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3394248).length < 2 ^ (prefixWord ++ tailWord_3394248).sum := by decide
  have hdescent : baseEnd_3394248 < baseStart_3394248 := by decide
  rcases family_descends (prefixWord ++ tailWord_3394248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3394263 : List Nat := [1, 1, 3, 2, 1, 4, 3, 1, 2, 4]
def baseStart_3394263 : Nat := 118140960795 + 3394263 * 2 ^ 59
def prefixEnd_3394263 : Nat := 4983230072969 + 3 ^ 40 * 3394263 * 2
def baseEnd_3394263 : Nat := 1161925591181305776068383

theorem tailTrace_3394263 : CollatzResearch.WordTrace tailWord_3394263 prefixEnd_3394263 1161925591181305776068383 := by
  unfold tailWord_3394263
  simp only [CollatzResearch.WordTrace]
  refine ⟨123798942102172319813715443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82532628068114879875810295 123798942102172319813715443)
  ·
    refine ⟨185698413153258479720573165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123798942102172319813715443 185698413153258479720573165)
    ·
      refine ⟨69636904932471929895214937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 185698413153258479720573165 69636904932471929895214937)
      ·
        refine ⟨52227678699353947421411203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69636904932471929895214937 52227678699353947421411203)
        ·
          refine ⟨78341518049030921132116805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52227678699353947421411203 78341518049030921132116805)
          ·
            refine ⟨14689034634193297712271901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 78341518049030921132116805 14689034634193297712271901)
            ·
              refine ⟨5508387987822486642101963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14689034634193297712271901 5508387987822486642101963)
              ·
                refine ⟨8262581981733729963152945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5508387987822486642101963 8262581981733729963152945)
                ·
                  refine ⟨6196936486300297472364709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8262581981733729963152945 6196936486300297472364709)
                  ·
                    refine ⟨1161925591181305776068383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6196936486300297472364709 1161925591181305776068383)
                    ·
                      rfl

theorem cell22_3394263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 3, 1, 2, 4].length) (baseStart_3394263 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3394263 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3394263 prefixEnd_3394263 := by exact prefixLift 3394263
  have htrace : WordTrace (prefixWord ++ tailWord_3394263) baseStart_3394263 baseEnd_3394263 := by
    simpa [prefixWord, tailWord_3394263, baseEnd_3394263] using wordTrace_append hprefix tailTrace_3394263
  have hstable : (prefixWord ++ tailWord_3394263).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3394263).length < 2 ^ (prefixWord ++ tailWord_3394263).sum := by decide
  have hdescent : baseEnd_3394263 < baseStart_3394263 := by decide
  rcases family_descends (prefixWord ++ tailWord_3394263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3394321 : List Nat := [1, 2, 2, 1, 1, 3, 2, 2, 1, 7]
def baseStart_3394321 : Nat := 118140960795 + 3394321 * 2 ^ 59
def prefixEnd_3394321 : Nat := 4983230072969 + 3 ^ 40 * 3394321 * 2
def baseEnd_3394321 : Nat := 1161945445766612958118205

theorem tailTrace_3394321 : CollatzResearch.WordTrace tailWord_3394321 prefixEnd_3394321 1161945445766612958118205 := by
  unfold tailWord_3394321
  simp only [CollatzResearch.WordTrace]
  refine ⟨123801057535962195719326817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82534038357308130479551211 123801057535962195719326817)
  ·
    refine ⟨92850793151971646789495113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123801057535962195719326817 92850793151971646789495113)
    ·
      refine ⟨69638094863978735092121335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92850793151971646789495113 69638094863978735092121335)
      ·
        refine ⟨104457142295968102638182003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69638094863978735092121335 104457142295968102638182003)
        ·
          refine ⟨156685713443952153957273005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104457142295968102638182003 156685713443952153957273005)
          ·
            refine ⟨58757142541482057733977377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 156685713443952153957273005 58757142541482057733977377)
            ·
              refine ⟨44067856906111543300483033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58757142541482057733977377 44067856906111543300483033)
              ·
                refine ⟨33050892679583657475362275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44067856906111543300483033 33050892679583657475362275)
                ·
                  refine ⟨49576339019375486213043413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33050892679583657475362275 49576339019375486213043413)
                  ·
                    refine ⟨1161945445766612958118205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 49576339019375486213043413 1161945445766612958118205)
                    ·
                      rfl

theorem cell22_3394321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 7].length) (baseStart_3394321 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3394321 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3394321 prefixEnd_3394321 := by exact prefixLift 3394321
  have htrace : WordTrace (prefixWord ++ tailWord_3394321) baseStart_3394321 baseEnd_3394321 := by
    simpa [prefixWord, tailWord_3394321, baseEnd_3394321] using wordTrace_append hprefix tailTrace_3394321
  have hstable : (prefixWord ++ tailWord_3394321).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3394321).length < 2 ^ (prefixWord ++ tailWord_3394321).sum := by decide
  have hdescent : baseEnd_3394321 < baseStart_3394321 := by decide
  rcases family_descends (prefixWord ++ tailWord_3394321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3394344 : List Nat := [2, 1, 5, 1, 1, 1, 5, 2, 1, 3]
def baseStart_3394344 : Nat := 118140960795 + 3394344 * 2 ^ 59
def prefixEnd_3394344 : Nat := 4983230072969 + 3 ^ 40 * 3394344 * 2
def baseEnd_3394344 : Nat := 1161953319136648564793135

theorem tailTrace_3394344 : CollatzResearch.WordTrace tailWord_3394344 prefixEnd_3394344 1161953319136648564793135 := by
  unfold tailWord_3394344
  simp only [CollatzResearch.WordTrace]
  refine ⟨61900948207439435323707043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82534597609919247098276057 61900948207439435323707043)
  ·
    refine ⟨92851422311159152985560565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61900948207439435323707043 92851422311159152985560565)
    ·
      refine ⟨8704820841671170592396303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 92851422311159152985560565 8704820841671170592396303)
      ·
        refine ⟨13057231262506755888594455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8704820841671170592396303 13057231262506755888594455)
        ·
          refine ⟨19585846893760133832891683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13057231262506755888594455 19585846893760133832891683)
          ·
            refine ⟨29378770340640200749337525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19585846893760133832891683 29378770340640200749337525)
            ·
              refine ⟨2754259719435018820250393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 29378770340640200749337525 2754259719435018820250393)
              ·
                refine ⟨2065694789576264115187795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2754259719435018820250393 2065694789576264115187795)
                ·
                  refine ⟨3098542184364396172781693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2065694789576264115187795 3098542184364396172781693)
                  ·
                    refine ⟨1161953319136648564793135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3098542184364396172781693 1161953319136648564793135)
                    ·
                      rfl

theorem cell22_3394344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 5, 2, 1, 3].length) (baseStart_3394344 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3394344 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3394344 prefixEnd_3394344 := by exact prefixLift 3394344
  have htrace : WordTrace (prefixWord ++ tailWord_3394344) baseStart_3394344 baseEnd_3394344 := by
    simpa [prefixWord, tailWord_3394344, baseEnd_3394344] using wordTrace_append hprefix tailTrace_3394344
  have hstable : (prefixWord ++ tailWord_3394344).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3394344).length < 2 ^ (prefixWord ++ tailWord_3394344).sum := by decide
  have hdescent : baseEnd_3394344 < baseStart_3394344 := by decide
  rcases family_descends (prefixWord ++ tailWord_3394344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3394353 : List Nat := [1, 2, 2, 3, 2, 1, 2, 2, 3, 4]
def baseStart_3394353 : Nat := 118140960795 + 3394353 * 2 ^ 59
def prefixEnd_3394353 : Nat := 4983230072969 + 3 ^ 40 * 3394353 * 2
def baseEnd_3394353 : Nat := 1161956400020575541318107

theorem tailTrace_3394353 : CollatzResearch.WordTrace tailWord_3394353 prefixEnd_3394353 1161956400020575541318107 := by
  unfold tailWord_3394353
  simp only [CollatzResearch.WordTrace]
  refine ⟨123802224671846265184491713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82534816447897510122994475 123802224671846265184491713)
  ·
    refine ⟨92851668503884698888368785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123802224671846265184491713 92851668503884698888368785)
    ·
      refine ⟨69638751377913524166276589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92851668503884698888368785 69638751377913524166276589)
      ·
        refine ⟨26114531766717571562353721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69638751377913524166276589 26114531766717571562353721)
        ·
          refine ⟨19585898825038178671765291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26114531766717571562353721 19585898825038178671765291)
          ·
            refine ⟨29378848237557268007647937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19585898825038178671765291 29378848237557268007647937)
            ·
              refine ⟨22034136178167951005735953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29378848237557268007647937 22034136178167951005735953)
              ·
                refine ⟨16525602133625963254301965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22034136178167951005735953 16525602133625963254301965)
                ·
                  refine ⟨6197100800109736220363237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16525602133625963254301965 6197100800109736220363237)
                  ·
                    refine ⟨1161956400020575541318107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6197100800109736220363237 1161956400020575541318107)
                    ·
                      rfl

theorem cell22_3394353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 2, 2, 3, 4].length) (baseStart_3394353 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3394353 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3394353 prefixEnd_3394353 := by exact prefixLift 3394353
  have htrace : WordTrace (prefixWord ++ tailWord_3394353) baseStart_3394353 baseEnd_3394353 := by
    simpa [prefixWord, tailWord_3394353, baseEnd_3394353] using wordTrace_append hprefix tailTrace_3394353
  have hstable : (prefixWord ++ tailWord_3394353).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3394353).length < 2 ^ (prefixWord ++ tailWord_3394353).sum := by decide
  have hdescent : baseEnd_3394353 < baseStart_3394353 := by decide
  rcases family_descends (prefixWord ++ tailWord_3394353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3394357 : List Nat := [1, 3, 3, 1, 3, 3, 2, 1, 5]
def baseStart_3394357 : Nat := 118140960795 + 3394357 * 2 ^ 59
def prefixEnd_3394357 : Nat := 4983230072969 + 3 ^ 40 * 3394357 * 2
def baseEnd_3394357 : Nat := 387319256434106954739365

theorem tailTrace_3394357 : CollatzResearch.WordTrace tailWord_3394357 prefixEnd_3394357 387319256434106954739365 := by
  unfold tailWord_3394357
  simp only [CollatzResearch.WordTrace]
  refine ⟨123802370563831773867637325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82534913709221182578424883 123802370563831773867637325)
  ·
    refine ⟨46425888961436915200363997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123802370563831773867637325 46425888961436915200363997)
    ·
      refine ⟨17409708360538843200136499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46425888961436915200363997 17409708360538843200136499)
      ·
        refine ⟨26114562540808264800204749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17409708360538843200136499 26114562540808264800204749)
        ·
          refine ⟨9792960952803099300076781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26114562540808264800204749 9792960952803099300076781)
          ·
            refine ⟨3672360357301162237528793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9792960952803099300076781 3672360357301162237528793)
            ·
              refine ⟨2754270267975871678146595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3672360357301162237528793 2754270267975871678146595)
              ·
                refine ⟨4131405401963807517219893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2754270267975871678146595 4131405401963807517219893)
                ·
                  refine ⟨387319256434106954739365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4131405401963807517219893 387319256434106954739365)
                  ·
                    rfl

theorem cell22_3394357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 3, 2, 1, 5].length) (baseStart_3394357 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3394357 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3394357 prefixEnd_3394357 := by exact prefixLift 3394357
  have htrace : WordTrace (prefixWord ++ tailWord_3394357) baseStart_3394357 baseEnd_3394357 := by
    simpa [prefixWord, tailWord_3394357, baseEnd_3394357] using wordTrace_append hprefix tailTrace_3394357
  have hstable : (prefixWord ++ tailWord_3394357).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3394357).length < 2 ^ (prefixWord ++ tailWord_3394357).sum := by decide
  have hdescent : baseEnd_3394357 < baseStart_3394357 := by decide
  rcases family_descends (prefixWord ++ tailWord_3394357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3394473 : List Nat := [1, 2, 1, 1, 1, 1, 5, 3, 2, 5]
def baseStart_3394473 : Nat := 118140960795 + 3394473 * 2 ^ 59
def prefixEnd_3394473 : Nat := 4983230072969 + 3 ^ 40 * 3394473 * 2
def baseEnd_3394473 : Nat := 1161997478472935228317739

theorem tailTrace_3394473 : CollatzResearch.WordTrace tailWord_3394473 prefixEnd_3394473 1161997478472935228317739 := by
  unfold tailWord_3394473
  simp only [CollatzResearch.WordTrace]
  refine ⟨123806601431411525678860073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82537734287607683785906715 123806601431411525678860073)
  ·
    refine ⟨92854951073558644259145055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123806601431411525678860073 92854951073558644259145055)
    ·
      refine ⟨139282426610337966388717583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92854951073558644259145055 139282426610337966388717583)
      ·
        refine ⟨208923639915506949583076375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139282426610337966388717583 208923639915506949583076375)
        ·
          refine ⟨313385459873260424374614563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 208923639915506949583076375 313385459873260424374614563)
          ·
            refine ⟨470078189809890636561921845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 313385459873260424374614563 470078189809890636561921845)
            ·
              refine ⟨44069830294677247177680173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 470078189809890636561921845 44069830294677247177680173)
              ·
                refine ⟨16526186360503967691630065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44069830294677247177680173 16526186360503967691630065)
                ·
                  refine ⟨12394639770377975768722549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16526186360503967691630065 12394639770377975768722549)
                  ·
                    refine ⟨1161997478472935228317739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12394639770377975768722549 1161997478472935228317739)
                    ·
                      rfl

theorem cell22_3394473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 3, 2, 5].length) (baseStart_3394473 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3394473 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3394473 prefixEnd_3394473 := by exact prefixLift 3394473
  have htrace : WordTrace (prefixWord ++ tailWord_3394473) baseStart_3394473 baseEnd_3394473 := by
    simpa [prefixWord, tailWord_3394473, baseEnd_3394473] using wordTrace_append hprefix tailTrace_3394473
  have hstable : (prefixWord ++ tailWord_3394473).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3394473).length < 2 ^ (prefixWord ++ tailWord_3394473).sum := by decide
  have hdescent : baseEnd_3394473 < baseStart_3394473 := by decide
  rcases family_descends (prefixWord ++ tailWord_3394473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3394503 : List Nat := [1, 1, 4, 1, 1, 2, 2, 2, 8]
def baseStart_3394503 : Nat := 118140960795 + 3394503 * 2 ^ 59
def prefixEnd_3394503 : Nat := 4983230072969 + 3 ^ 40 * 3394503 * 2
def baseEnd_3394503 : Nat := 387335916028675050022549

theorem tailTrace_3394503 : CollatzResearch.WordTrace tailWord_3394503 prefixEnd_3394503 387335916028675050022549 := by
  unfold tailWord_3394503
  simp only [CollatzResearch.WordTrace]
  refine ⟨123807695621302840802452163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82538463747535227201634775 123807695621302840802452163)
  ·
    refine ⟨185711543431954261203678245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123807695621302840802452163 185711543431954261203678245)
    ·
      refine ⟨34820914393491423975689671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 185711543431954261203678245 34820914393491423975689671)
      ·
        refine ⟨52231371590237135963534507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34820914393491423975689671 52231371590237135963534507)
        ·
          refine ⟨78347057385355703945301761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52231371590237135963534507 78347057385355703945301761)
          ·
            refine ⟨58760293039016777958976321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78347057385355703945301761 58760293039016777958976321)
            ·
              refine ⟨44070219779262583469232241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58760293039016777958976321 44070219779262583469232241)
              ·
                refine ⟨33052664834446937601924181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44070219779262583469232241 33052664834446937601924181)
                ·
                  refine ⟨387335916028675050022549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 33052664834446937601924181 387335916028675050022549)
                  ·
                    rfl

theorem cell22_3394503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 2, 8].length) (baseStart_3394503 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3394503 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3394503 prefixEnd_3394503 := by exact prefixLift 3394503
  have htrace : WordTrace (prefixWord ++ tailWord_3394503) baseStart_3394503 baseEnd_3394503 := by
    simpa [prefixWord, tailWord_3394503, baseEnd_3394503] using wordTrace_append hprefix tailTrace_3394503
  have hstable : (prefixWord ++ tailWord_3394503).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3394503).length < 2 ^ (prefixWord ++ tailWord_3394503).sum := by decide
  have hdescent : baseEnd_3394503 < baseStart_3394503 := by decide
  rcases family_descends (prefixWord ++ tailWord_3394503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3394520 : List Nat := [2, 1, 2, 2, 2, 3, 3, 1, 6]
def baseStart_3394520 : Nat := 118140960795 + 3394520 * 2 ^ 59
def prefixEnd_3394520 : Nat := 4983230072969 + 3 ^ 40 * 3394520 * 2
def baseEnd_3394520 : Nat := 387337855844480924130865

theorem tailTrace_3394520 : CollatzResearch.WordTrace tailWord_3394520 prefixEnd_3394520 387337855844480924130865 := by
  unfold tailWord_3394520
  simp only [CollatzResearch.WordTrace]
  refine ⟨61904157831120626352910507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82538877108160835137214009 61904157831120626352910507)
  ·
    refine ⟨92856236746680939529365761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61904157831120626352910507 92856236746680939529365761)
    ·
      refine ⟨69642177560010704647024321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92856236746680939529365761 69642177560010704647024321)
      ·
        refine ⟨52231633170008028485268241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69642177560010704647024321 52231633170008028485268241)
        ·
          refine ⟨39173724877506021363951181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52231633170008028485268241 39173724877506021363951181)
          ·
            refine ⟨14690146829064758011481693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39173724877506021363951181 14690146829064758011481693)
            ·
              refine ⟨5508805060899284254305635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14690146829064758011481693 5508805060899284254305635)
              ·
                refine ⟨8263207591348926381458453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5508805060899284254305635 8263207591348926381458453)
                ·
                  refine ⟨387337855844480924130865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8263207591348926381458453 387337855844480924130865)
                  ·
                    rfl

theorem cell22_3394520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 3, 1, 6].length) (baseStart_3394520 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3394520 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3394520 prefixEnd_3394520 := by exact prefixLift 3394520
  have htrace : WordTrace (prefixWord ++ tailWord_3394520) baseStart_3394520 baseEnd_3394520 := by
    simpa [prefixWord, tailWord_3394520, baseEnd_3394520] using wordTrace_append hprefix tailTrace_3394520
  have hstable : (prefixWord ++ tailWord_3394520).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3394520).length < 2 ^ (prefixWord ++ tailWord_3394520).sum := by decide
  have hdescent : baseEnd_3394520 < baseStart_3394520 := by decide
  rcases family_descends (prefixWord ++ tailWord_3394520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3394597 : List Nat := [1, 3, 1, 2, 2, 2, 3, 2, 3, 3]
def baseStart_3394597 : Nat := 118140960795 + 3394597 * 2 ^ 59
def prefixEnd_3394597 : Nat := 4983230072969 + 3 ^ 40 * 3394597 * 2
def baseEnd_3394597 : Nat := 1162039926207040238217359

theorem tailTrace_3394597 : CollatzResearch.WordTrace tailWord_3394597 prefixEnd_3394597 1162039926207040238217359 := by
  unfold tailWord_3394597
  simp only [CollatzResearch.WordTrace]
  refine ⟨123811124082962294856374045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82540749388641529904249363 123811124082962294856374045)
  ·
    refine ⟨46429171531110860571140267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123811124082962294856374045 46429171531110860571140267)
    ·
      refine ⟨69643757296666290856710401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46429171531110860571140267 69643757296666290856710401)
      ·
        refine ⟨52232817972499718142532801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69643757296666290856710401 52232817972499718142532801)
        ·
          refine ⟨39174613479374788606899601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52232817972499718142532801 39174613479374788606899601)
          ·
            refine ⟨29380960109531091455174701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39174613479374788606899601 29380960109531091455174701)
            ·
              refine ⟨11017860041074159295690513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29380960109531091455174701 11017860041074159295690513)
              ·
                refine ⟨8263395030805619471767885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11017860041074159295690513 8263395030805619471767885)
                ·
                  refine ⟨3098773136552107301912957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8263395030805619471767885 3098773136552107301912957)
                  ·
                    refine ⟨1162039926207040238217359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3098773136552107301912957 1162039926207040238217359)
                    ·
                      rfl

theorem cell22_3394597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 3, 2, 3, 3].length) (baseStart_3394597 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3394597 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3394597 prefixEnd_3394597 := by exact prefixLift 3394597
  have htrace : WordTrace (prefixWord ++ tailWord_3394597) baseStart_3394597 baseEnd_3394597 := by
    simpa [prefixWord, tailWord_3394597, baseEnd_3394597] using wordTrace_append hprefix tailTrace_3394597
  have hstable : (prefixWord ++ tailWord_3394597).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3394597).length < 2 ^ (prefixWord ++ tailWord_3394597).sum := by decide
  have hdescent : baseEnd_3394597 < baseStart_3394597 := by decide
  rcases family_descends (prefixWord ++ tailWord_3394597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3394599 : List Nat := [1, 1, 7, 1, 1, 2, 3, 6]
def baseStart_3394599 : Nat := 118140960795 + 3394599 * 2 ^ 59
def prefixEnd_3394599 : Nat := 4983230072969 + 3 ^ 40 * 3394599 * 2
def baseEnd_3394599 : Nat := 129115623427545877740817

theorem tailTrace_3394599 : CollatzResearch.WordTrace tailWord_3394599 prefixEnd_3394599 129115623427545877740817 := by
  unfold tailWord_3394599
  simp only [CollatzResearch.WordTrace]
  refine ⟨123811197028955049197946851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82540798019303366131964567 123811197028955049197946851)
  ·
    refine ⟨185716795543432573796920277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123811197028955049197946851 185716795543432573796920277)
    ·
      refine ⟨4352737395549200948365319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 185716795543432573796920277 4352737395549200948365319)
      ·
        refine ⟨6529106093323801422547979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4352737395549200948365319 6529106093323801422547979)
        ·
          refine ⟨9793659139985702133821969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6529106093323801422547979 9793659139985702133821969)
          ·
            refine ⟨7345244354989276600366477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9793659139985702133821969 7345244354989276600366477)
            ·
              refine ⟨2754466633120978725137429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7345244354989276600366477 2754466633120978725137429)
              ·
                refine ⟨129115623427545877740817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2754466633120978725137429 129115623427545877740817)
                ·
                  rfl

theorem cell22_3394599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 3, 6].length) (baseStart_3394599 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3394599 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3394599 prefixEnd_3394599 := by exact prefixLift 3394599
  have htrace : WordTrace (prefixWord ++ tailWord_3394599) baseStart_3394599 baseEnd_3394599 := by
    simpa [prefixWord, tailWord_3394599, baseEnd_3394599] using wordTrace_append hprefix tailTrace_3394599
  have hstable : (prefixWord ++ tailWord_3394599).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3394599).length < 2 ^ (prefixWord ++ tailWord_3394599).sum := by decide
  have hdescent : baseEnd_3394599 < baseStart_3394599 := by decide
  rcases family_descends (prefixWord ++ tailWord_3394599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3394610 : List Nat := [3, 2, 1, 1, 2, 2, 2, 2, 7]
def baseStart_3394610 : Nat := 118140960795 + 3394610 * 2 ^ 59
def prefixEnd_3394610 : Nat := 4983230072969 + 3 ^ 40 * 3394610 * 2
def baseEnd_3394610 : Nat := 387348125457570845880773

theorem tailTrace_3394610 : CollatzResearch.WordTrace tailWord_3394610 prefixEnd_3394610 387348125457570845880773 := by
  unfold tailWord_3394610
  simp only [CollatzResearch.WordTrace]
  refine ⟨30952899557978799519149321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82541065487943465384398189 30952899557978799519149321)
  ·
    refine ⟨23214674668484099639361991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30952899557978799519149321 23214674668484099639361991)
    ·
      refine ⟨34822012002726149459042987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23214674668484099639361991 34822012002726149459042987)
      ·
        refine ⟨52233018004089224188564481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34822012002726149459042987 52233018004089224188564481)
        ·
          refine ⟨39174763503066918141423361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52233018004089224188564481 39174763503066918141423361)
          ·
            refine ⟨29381072627300188606067521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39174763503066918141423361 29381072627300188606067521)
            ·
              refine ⟨22035804470475141454550641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29381072627300188606067521 22035804470475141454550641)
              ·
                refine ⟨16526853352856356090912981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22035804470475141454550641 16526853352856356090912981)
                ·
                  refine ⟨387348125457570845880773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16526853352856356090912981 387348125457570845880773)
                  ·
                    rfl

theorem cell22_3394610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 2, 2, 7].length) (baseStart_3394610 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3394610 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3394610 prefixEnd_3394610 := by exact prefixLift 3394610
  have htrace : WordTrace (prefixWord ++ tailWord_3394610) baseStart_3394610 baseEnd_3394610 := by
    simpa [prefixWord, tailWord_3394610, baseEnd_3394610] using wordTrace_append hprefix tailTrace_3394610
  have hstable : (prefixWord ++ tailWord_3394610).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3394610).length < 2 ^ (prefixWord ++ tailWord_3394610).sum := by decide
  have hdescent : baseEnd_3394610 < baseStart_3394610 := by decide
  rcases family_descends (prefixWord ++ tailWord_3394610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3394640 : List Nat := [2, 1, 1, 1, 1, 3, 1, 3, 5, 4]
def baseStart_3394640 : Nat := 118140960795 + 3394640 * 2 ^ 59
def prefixEnd_3394640 : Nat := 4983230072969 + 3 ^ 40 * 3394640 * 2
def baseEnd_3394640 : Nat := 1162054645985802459392227

theorem tailTrace_3394640 : CollatzResearch.WordTrace tailWord_3394640 prefixEnd_3394640 1162054645985802459392227 := by
  unfold tailWord_3394640
  simp only [CollatzResearch.WordTrace]
  refine ⟨61906346210903256600094687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82541794947871008800126249 61906346210903256600094687)
  ·
    refine ⟨92859519316354884900142031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61906346210903256600094687 92859519316354884900142031)
    ·
      refine ⟨139289278974532327350213047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92859519316354884900142031 139289278974532327350213047)
      ·
        refine ⟨208933918461798491025319571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139289278974532327350213047 208933918461798491025319571)
        ·
          refine ⟨313400877692697736537979357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 208933918461798491025319571 313400877692697736537979357)
          ·
            refine ⟨117525329134761651201742259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 313400877692697736537979357 117525329134761651201742259)
            ·
              refine ⟨176287993702142476802613389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 117525329134761651201742259 176287993702142476802613389)
              ·
                refine ⟨66107997638303428800980021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 176287993702142476802613389 66107997638303428800980021)
                ·
                  refine ⟨6197624778590946450091877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 66107997638303428800980021 6197624778590946450091877)
                  ·
                    refine ⟨1162054645985802459392227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6197624778590946450091877 1162054645985802459392227)
                    ·
                      rfl

theorem cell22_3394640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 3, 5, 4].length) (baseStart_3394640 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3394640 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3394640 prefixEnd_3394640 := by exact prefixLift 3394640
  have htrace : WordTrace (prefixWord ++ tailWord_3394640) baseStart_3394640 baseEnd_3394640 := by
    simpa [prefixWord, tailWord_3394640, baseEnd_3394640] using wordTrace_append hprefix tailTrace_3394640
  have hstable : (prefixWord ++ tailWord_3394640).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3394640).length < 2 ^ (prefixWord ++ tailWord_3394640).sum := by decide
  have hdescent : baseEnd_3394640 < baseStart_3394640 := by decide
  rcases family_descends (prefixWord ++ tailWord_3394640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3394642 : List Nat := [3, 2, 2, 1, 3, 1, 2, 1, 2, 5]
def baseStart_3394642 : Nat := 118140960795 + 3394642 * 2 ^ 59
def prefixEnd_3394642 : Nat := 4983230072969 + 3 ^ 40 * 3394642 * 2
def baseEnd_3394642 : Nat := 1162055330626675120842221

theorem tailTrace_3394642 : CollatzResearch.WordTrace tailWord_3394642 prefixEnd_3394642 1162055330626675120842221 := by
  unfold tailWord_3394642
  simp only [CollatzResearch.WordTrace]
  refine ⟨30953191341949816885440545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82541843578532845027841453 30953191341949816885440545)
  ·
    refine ⟨23214893506462362664080409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30953191341949816885440545 23214893506462362664080409)
    ·
      refine ⟨17411170129846771998060307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23214893506462362664080409 17411170129846771998060307)
      ·
        refine ⟨26116755194770157997090461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17411170129846771998060307 26116755194770157997090461)
        ·
          refine ⟨9793783198038809248908923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26116755194770157997090461 9793783198038809248908923)
          ·
            refine ⟨14690674797058213873363385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9793783198038809248908923 14690674797058213873363385)
            ·
              refine ⟨11018006097793660405022539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14690674797058213873363385 11018006097793660405022539)
              ·
                refine ⟨16527009146690490607533809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11018006097793660405022539 16527009146690490607533809)
                ·
                  refine ⟨12395256860017867955650357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16527009146690490607533809 12395256860017867955650357)
                  ·
                    refine ⟨1162055330626675120842221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12395256860017867955650357 1162055330626675120842221)
                    ·
                      rfl

theorem cell22_3394642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 2, 1, 2, 5].length) (baseStart_3394642 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3394642 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3394642 prefixEnd_3394642 := by exact prefixLift 3394642
  have htrace : WordTrace (prefixWord ++ tailWord_3394642) baseStart_3394642 baseEnd_3394642 := by
    simpa [prefixWord, tailWord_3394642, baseEnd_3394642] using wordTrace_append hprefix tailTrace_3394642
  have hstable : (prefixWord ++ tailWord_3394642).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3394642).length < 2 ^ (prefixWord ++ tailWord_3394642).sum := by decide
  have hdescent : baseEnd_3394642 < baseStart_3394642 := by decide
  rcases family_descends (prefixWord ++ tailWord_3394642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3394655 : List Nat := [1, 1, 2, 3, 1, 1, 3, 4, 6]
def baseStart_3394655 : Nat := 118140960795 + 3394655 * 2 ^ 59
def prefixEnd_3394655 : Nat := 4983230072969 + 3 ^ 40 * 3394655 * 2
def baseEnd_3394655 : Nat := 387353260264115806755727

theorem tailTrace_3394655 : CollatzResearch.WordTrace tailWord_3394655 prefixEnd_3394655 387353260264115806755727 := by
  unfold tailWord_3394655
  simp only [CollatzResearch.WordTrace]
  refine ⟨123813239516752170761985419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82542159677834780507990279 123813239516752170761985419)
  ·
    refine ⟨185719859275128256142978129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123813239516752170761985419 185719859275128256142978129)
    ·
      refine ⟨139289894456346192107233597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 185719859275128256142978129 139289894456346192107233597)
      ·
        refine ⟨52233710421129822040212599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 139289894456346192107233597 52233710421129822040212599)
        ·
          refine ⟨78350565631694733060318899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52233710421129822040212599 78350565631694733060318899)
          ·
            refine ⟨117525848447542099590478349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78350565631694733060318899 117525848447542099590478349)
            ·
              refine ⟨44072193167828287346429381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 117525848447542099590478349 44072193167828287346429381)
              ·
                refine ⟨8263536218967803877455509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44072193167828287346429381 8263536218967803877455509)
                ·
                  refine ⟨387353260264115806755727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8263536218967803877455509 387353260264115806755727)
                  ·
                    rfl

theorem cell22_3394655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 4, 6].length) (baseStart_3394655 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3394655 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3394655 prefixEnd_3394655 := by exact prefixLift 3394655
  have htrace : WordTrace (prefixWord ++ tailWord_3394655) baseStart_3394655 baseEnd_3394655 := by
    simpa [prefixWord, tailWord_3394655, baseEnd_3394655] using wordTrace_append hprefix tailTrace_3394655
  have hstable : (prefixWord ++ tailWord_3394655).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3394655).length < 2 ^ (prefixWord ++ tailWord_3394655).sum := by decide
  have hdescent : baseEnd_3394655 < baseStart_3394655 := by decide
  rcases family_descends (prefixWord ++ tailWord_3394655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3394657 : List Nat := [1, 2, 3, 1, 1, 2, 3, 4, 1, 4]
def baseStart_3394657 : Nat := 118140960795 + 3394657 * 2 ^ 59
def prefixEnd_3394657 : Nat := 4983230072969 + 3 ^ 40 * 3394657 * 2
def baseEnd_3394657 : Nat := 1162060465433220081717175

theorem tailTrace_3394657 : CollatzResearch.WordTrace tailWord_3394657 prefixEnd_3394657 1162060465433220081717175 := by
  unfold tailWord_3394657
  simp only [CollatzResearch.WordTrace]
  refine ⟨123813312462744925103558225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82542208308496616735705483 123813312462744925103558225)
  ·
    refine ⟨92859984347058693827668669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123813312462744925103558225 92859984347058693827668669)
    ·
      refine ⟨34822494130147010185375751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92859984347058693827668669 34822494130147010185375751)
      ·
        refine ⟨52233741195220515278063627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34822494130147010185375751 52233741195220515278063627)
        ·
          refine ⟨78350611792830772917095441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52233741195220515278063627 78350611792830772917095441)
          ·
            refine ⟨58762958844623079687821581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78350611792830772917095441 58762958844623079687821581)
            ·
              refine ⟨22036109566733654882933093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58762958844623079687821581 22036109566733654882933093)
              ·
                refine ⟨4131770543762560290549955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22036109566733654882933093 4131770543762560290549955)
                ·
                  refine ⟨6197655815643840435824933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4131770543762560290549955 6197655815643840435824933)
                  ·
                    refine ⟨1162060465433220081717175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6197655815643840435824933 1162060465433220081717175)
                    ·
                      rfl

theorem cell22_3394657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 3, 4, 1, 4].length) (baseStart_3394657 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3394657 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3394657 prefixEnd_3394657 := by exact prefixLift 3394657
  have htrace : WordTrace (prefixWord ++ tailWord_3394657) baseStart_3394657 baseEnd_3394657 := by
    simpa [prefixWord, tailWord_3394657, baseEnd_3394657] using wordTrace_append hprefix tailTrace_3394657
  have hstable : (prefixWord ++ tailWord_3394657).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3394657).length < 2 ^ (prefixWord ++ tailWord_3394657).sum := by decide
  have hdescent : baseEnd_3394657 < baseStart_3394657 := by decide
  rcases family_descends (prefixWord ++ tailWord_3394657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3394689 : List Nat := [1, 2, 4, 2, 2, 3, 1, 1, 6]
def baseStart_3394689 : Nat := 118140960795 + 3394689 * 2 ^ 59
def prefixEnd_3394689 : Nat := 4983230072969 + 3 ^ 40 * 3394689 * 2
def baseEnd_3394689 : Nat := 387357139895727554972359

theorem tailTrace_3394689 : CollatzResearch.WordTrace tailWord_3394689 prefixEnd_3394689 387357139895727554972359 := by
  unfold tailWord_3394689
  simp only [CollatzResearch.WordTrace]
  refine ⟨123814479598628994568723121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82542986399085996379148747 123814479598628994568723121)
  ·
    refine ⟨92860859698971745926542341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123814479598628994568723121 92860859698971745926542341)
    ·
      refine ⟨17411411193557202361226689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 92860859698971745926542341 17411411193557202361226689)
      ·
        refine ⟨13058558395167901770920017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17411411193557202361226689 13058558395167901770920017)
        ·
          refine ⟨9793918796375926328190013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13058558395167901770920017 9793918796375926328190013)
          ·
            refine ⟨3672719548640972373071255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9793918796375926328190013 3672719548640972373071255)
            ·
              refine ⟨5509079322961458559606883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3672719548640972373071255 5509079322961458559606883)
              ·
                refine ⟨8263618984442187839410325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5509079322961458559606883 8263618984442187839410325)
                ·
                  refine ⟨387357139895727554972359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8263618984442187839410325 387357139895727554972359)
                  ·
                    rfl

theorem cell22_3394689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 3, 1, 1, 6].length) (baseStart_3394689 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3394689 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3394689 prefixEnd_3394689 := by exact prefixLift 3394689
  have htrace : WordTrace (prefixWord ++ tailWord_3394689) baseStart_3394689 baseEnd_3394689 := by
    simpa [prefixWord, tailWord_3394689, baseEnd_3394689] using wordTrace_append hprefix tailTrace_3394689
  have hstable : (prefixWord ++ tailWord_3394689).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3394689).length < 2 ^ (prefixWord ++ tailWord_3394689).sum := by decide
  have hdescent : baseEnd_3394689 < baseStart_3394689 := by decide
  rcases family_descends (prefixWord ++ tailWord_3394689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3394732 : List Nat := [2, 2, 1, 1, 1, 1, 1, 3, 7, 3]
def baseStart_3394732 : Nat := 118140960795 + 3394732 * 2 ^ 59
def prefixEnd_3394732 : Nat := 4983230072969 + 3 ^ 40 * 3394732 * 2
def baseEnd_3394732 : Nat := 1162086139465944886091945

theorem tailTrace_3394732 : CollatzResearch.WordTrace tailWord_3394732 prefixEnd_3394732 1162086139465944886091945 := by
  unfold tailWord_3394732
  simp only [CollatzResearch.WordTrace]
  refine ⟨61908023968736606456269225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82544031958315475275025633 61908023968736606456269225)
  ·
    refine ⟨46431017976552454842201919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61908023968736606456269225 46431017976552454842201919)
    ·
      refine ⟨69646526964828682263302879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46431017976552454842201919 69646526964828682263302879)
      ·
        refine ⟨104469790447243023394954319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69646526964828682263302879 104469790447243023394954319)
        ·
          refine ⟨156704685670864535092431479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104469790447243023394954319 156704685670864535092431479)
          ·
            refine ⟨235057028506296802638647219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 156704685670864535092431479 235057028506296802638647219)
            ·
              refine ⟨352585542759445203957970829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 235057028506296802638647219 352585542759445203957970829)
              ·
                refine ⟨132219578534791951484239061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 352585542759445203957970829 132219578534791951484239061)
                ·
                  refine ⟨3098896371909186362911853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 132219578534791951484239061 3098896371909186362911853)
                  ·
                    refine ⟨1162086139465944886091945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3098896371909186362911853 1162086139465944886091945)
                    ·
                      rfl

theorem cell22_3394732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 7, 3].length) (baseStart_3394732 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3394732 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3394732 prefixEnd_3394732 := by exact prefixLift 3394732
  have htrace : WordTrace (prefixWord ++ tailWord_3394732) baseStart_3394732 baseEnd_3394732 := by
    simpa [prefixWord, tailWord_3394732, baseEnd_3394732] using wordTrace_append hprefix tailTrace_3394732
  have hstable : (prefixWord ++ tailWord_3394732).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3394732).length < 2 ^ (prefixWord ++ tailWord_3394732).sum := by decide
  have hdescent : baseEnd_3394732 < baseStart_3394732 := by decide
  rcases family_descends (prefixWord ++ tailWord_3394732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3394766 : List Nat := [4, 1, 1, 1, 5, 1, 1, 2, 3, 3]
def baseStart_3394766 : Nat := 118140960795 + 3394766 * 2 ^ 59
def prefixEnd_3394766 : Nat := 4983230072969 + 3 ^ 40 * 3394766 * 2
def baseEnd_3394766 : Nat := 1162097778360780130741841

theorem tailTrace_3394766 : CollatzResearch.WordTrace tailWord_3394766 prefixEnd_3394766 1162097778360780130741841 := by
  unfold tailWord_3394766
  simp only [CollatzResearch.WordTrace]
  refine ⟨15477161002418754589909519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 82544858679566691146184101 15477161002418754589909519)
  ·
    refine ⟨23215741503628131884864279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15477161002418754589909519 23215741503628131884864279)
    ·
      refine ⟨34823612255442197827296419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23215741503628131884864279 34823612255442197827296419)
      ·
        refine ⟨52235418383163296740944629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34823612255442197827296419 52235418383163296740944629)
        ·
          refine ⟨4897070473421559069463559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 52235418383163296740944629 4897070473421559069463559)
          ·
            refine ⟨7345605710132338604195339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4897070473421559069463559 7345605710132338604195339)
            ·
              refine ⟨11018408565198507906293009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7345605710132338604195339 11018408565198507906293009)
              ·
                refine ⟨8263806423898880929719757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11018408565198507906293009 8263806423898880929719757)
                ·
                  refine ⟨3098927408962080348644909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8263806423898880929719757 3098927408962080348644909)
                  ·
                    refine ⟨1162097778360780130741841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3098927408962080348644909 1162097778360780130741841)
                    ·
                      rfl

theorem cell22_3394766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 1, 2, 3, 3].length) (baseStart_3394766 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3394766 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3394766 prefixEnd_3394766 := by exact prefixLift 3394766
  have htrace : WordTrace (prefixWord ++ tailWord_3394766) baseStart_3394766 baseEnd_3394766 := by
    simpa [prefixWord, tailWord_3394766, baseEnd_3394766] using wordTrace_append hprefix tailTrace_3394766
  have hstable : (prefixWord ++ tailWord_3394766).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3394766).length < 2 ^ (prefixWord ++ tailWord_3394766).sum := by decide
  have hdescent : baseEnd_3394766 < baseStart_3394766 := by decide
  rcases family_descends (prefixWord ++ tailWord_3394766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3394834 : List Nat := [3, 2, 4, 2, 2, 1, 1, 3, 1, 3]
def baseStart_3394834 : Nat := 118140960795 + 3394834 * 2 ^ 59
def prefixEnd_3394834 : Nat := 4983230072969 + 3 ^ 40 * 3394834 * 2
def baseEnd_3394834 : Nat := 1162121056150450620041633

theorem tailTrace_3394834 : CollatzResearch.WordTrace tailWord_3394834 prefixEnd_3394834 1162121056150450620041633 := by
  unfold tailWord_3394834
  simp only [CollatzResearch.WordTrace]
  refine ⟨30954942045775921083187889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82546512122069122888501037 30954942045775921083187889)
  ·
    refine ⟨23216206534331940812390917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30954942045775921083187889 23216206534331940812390917)
    ·
      refine ⟨4353038725187238902323297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23216206534331940812390917 4353038725187238902323297)
      ·
        refine ⟨3264779043890429176742473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4353038725187238902323297 3264779043890429176742473)
        ·
          refine ⟨2448584282917821882556855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3264779043890429176742473 2448584282917821882556855)
          ·
            refine ⟨3672876424376732823835283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2448584282917821882556855 3672876424376732823835283)
            ·
              refine ⟨5509314636565099235752925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3672876424376732823835283 5509314636565099235752925)
              ·
                refine ⟨2065992988711912213407347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5509314636565099235752925 2065992988711912213407347)
                ·
                  refine ⟨3098989483067868320111021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2065992988711912213407347 3098989483067868320111021)
                  ·
                    refine ⟨1162121056150450620041633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3098989483067868320111021 1162121056150450620041633)
                    ·
                      rfl

theorem cell22_3394834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 2, 1, 1, 3, 1, 3].length) (baseStart_3394834 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3394834 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3394834 prefixEnd_3394834 := by exact prefixLift 3394834
  have htrace : WordTrace (prefixWord ++ tailWord_3394834) baseStart_3394834 baseEnd_3394834 := by
    simpa [prefixWord, tailWord_3394834, baseEnd_3394834] using wordTrace_append hprefix tailTrace_3394834
  have hstable : (prefixWord ++ tailWord_3394834).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3394834).length < 2 ^ (prefixWord ++ tailWord_3394834).sum := by decide
  have hdescent : baseEnd_3394834 < baseStart_3394834 := by decide
  rcases family_descends (prefixWord ++ tailWord_3394834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3394839 : List Nat := [1, 1, 3, 4, 1, 1, 1, 1, 6, 3]
def baseStart_3394839 : Nat := 118140960795 + 3394839 * 2 ^ 59
def prefixEnd_3394839 : Nat := 4983230072969 + 3 ^ 40 * 3394839 * 2
def baseEnd_3394839 : Nat := 1162122767752632273666617

theorem tailTrace_3394839 : CollatzResearch.WordTrace tailWord_3394839 prefixEnd_3394839 1162122767752632273666617 := by
  unfold tailWord_3394839
  simp only [CollatzResearch.WordTrace]
  refine ⟨123819950548085570186683571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82546633698723713457789047 123819950548085570186683571)
  ·
    refine ⟨185729925822128355280025357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123819950548085570186683571 185729925822128355280025357)
    ·
      refine ⟨69648722183298133230009509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 185729925822128355280025357 69648722183298133230009509)
      ·
        refine ⟨13059135409368399980626783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 69648722183298133230009509 13059135409368399980626783)
        ·
          refine ⟨19588703114052599970940175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13059135409368399980626783 19588703114052599970940175)
          ·
            refine ⟨29383054671078899956410263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19588703114052599970940175 29383054671078899956410263)
            ·
              refine ⟨44074582006618349934615395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29383054671078899956410263 44074582006618349934615395)
              ·
                refine ⟨66111873009927524901923093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44074582006618349934615395 66111873009927524901923093)
                ·
                  refine ⟨3098994047340352729777645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 66111873009927524901923093 3098994047340352729777645)
                  ·
                    refine ⟨1162122767752632273666617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3098994047340352729777645 1162122767752632273666617)
                    ·
                      rfl

theorem cell22_3394839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 1, 6, 3].length) (baseStart_3394839 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3394839 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3394839 prefixEnd_3394839 := by exact prefixLift 3394839
  have htrace : WordTrace (prefixWord ++ tailWord_3394839) baseStart_3394839 baseEnd_3394839 := by
    simpa [prefixWord, tailWord_3394839, baseEnd_3394839] using wordTrace_append hprefix tailTrace_3394839
  have hstable : (prefixWord ++ tailWord_3394839).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3394839).length < 2 ^ (prefixWord ++ tailWord_3394839).sum := by decide
  have hdescent : baseEnd_3394839 < baseStart_3394839 := by decide
  rcases family_descends (prefixWord ++ tailWord_3394839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3394856 : List Nat := [2, 1, 5, 1, 2, 1, 2, 1, 4, 3]
def baseStart_3394856 : Nat := 118140960795 + 3394856 * 2 ^ 59
def prefixEnd_3394856 : Nat := 4983230072969 + 3 ^ 40 * 3394856 * 2
def baseEnd_3394856 : Nat := 1162128587200049895991565

theorem tailTrace_3394856 : CollatzResearch.WordTrace tailWord_3394856 prefixEnd_3394856 1162128587200049895991565 := by
  unfold tailWord_3394856
  simp only [CollatzResearch.WordTrace]
  refine ⟨61910285294511991045026211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82547047059349321393368281 61910285294511991045026211)
  ·
    refine ⟨92865427941767986567539317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61910285294511991045026211 92865427941767986567539317)
    ·
      refine ⟨8706133869540748740706811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 92865427941767986567539317 8706133869540748740706811)
      ·
        refine ⟨13059200804311123111060217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8706133869540748740706811 13059200804311123111060217)
        ·
          refine ⟨9794400603233342333295163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13059200804311123111060217 9794400603233342333295163)
          ·
            refine ⟨14691600904850013499942745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9794400603233342333295163 14691600904850013499942745)
            ·
              refine ⟨11018700678637510124957059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14691600904850013499942745 11018700678637510124957059)
              ·
                refine ⟨16528051017956265187435589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11018700678637510124957059 16528051017956265187435589)
                ·
                  refine ⟨3099009565866799722644173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16528051017956265187435589 3099009565866799722644173)
                  ·
                    refine ⟨1162128587200049895991565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3099009565866799722644173 1162128587200049895991565)
                    ·
                      rfl

theorem cell22_3394856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 2, 1, 4, 3].length) (baseStart_3394856 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3394856 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3394856 prefixEnd_3394856 := by exact prefixLift 3394856
  have htrace : WordTrace (prefixWord ++ tailWord_3394856) baseStart_3394856 baseEnd_3394856 := by
    simpa [prefixWord, tailWord_3394856, baseEnd_3394856] using wordTrace_append hprefix tailTrace_3394856
  have hstable : (prefixWord ++ tailWord_3394856).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3394856).length < 2 ^ (prefixWord ++ tailWord_3394856).sum := by decide
  have hdescent : baseEnd_3394856 < baseStart_3394856 := by decide
  rcases family_descends (prefixWord ++ tailWord_3394856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3394869 : List Nat := [1, 3, 3, 1, 2, 3, 2, 7]
def baseStart_3394869 : Nat := 118140960795 + 3394869 * 2 ^ 59
def prefixEnd_3394869 : Nat := 4983230072969 + 3 ^ 40 * 3394869 * 2
def baseEnd_3394869 : Nat := 129125893040635799490725

theorem tailTrace_3394869 : CollatzResearch.WordTrace tailWord_3394869 prefixEnd_3394869 129125893040635799490725 := by
  unfold tailWord_3394869
  simp only [CollatzResearch.WordTrace]
  refine ⟨123821044737976885310275661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82547363158651256873517107 123821044737976885310275661)
  ·
    refine ⟨46432891776741331991353373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123821044737976885310275661 46432891776741331991353373)
    ·
      refine ⟨17412334416277999496757515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46432891776741331991353373 17412334416277999496757515)
      ·
        refine ⟨26118501624416999245136273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17412334416277999496757515 26118501624416999245136273)
        ·
          refine ⟨19588876218312749433852205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26118501624416999245136273 19588876218312749433852205)
          ·
            refine ⟨7345828581867281037694577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19588876218312749433852205 7345828581867281037694577)
            ·
              refine ⟨5509371436400460778270933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7345828581867281037694577 5509371436400460778270933)
              ·
                refine ⟨129125893040635799490725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5509371436400460778270933 129125893040635799490725)
                ·
                  rfl

theorem cell22_3394869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 2, 7].length) (baseStart_3394869 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3394869 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3394869 prefixEnd_3394869 := by exact prefixLift 3394869
  have htrace : WordTrace (prefixWord ++ tailWord_3394869) baseStart_3394869 baseEnd_3394869 := by
    simpa [prefixWord, tailWord_3394869, baseEnd_3394869] using wordTrace_append hprefix tailTrace_3394869
  have hstable : (prefixWord ++ tailWord_3394869).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3394869).length < 2 ^ (prefixWord ++ tailWord_3394869).sum := by decide
  have hdescent : baseEnd_3394869 < baseStart_3394869 := by decide
  rcases family_descends (prefixWord ++ tailWord_3394869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3394873 : List Nat := [1, 2, 1, 6, 2, 1, 1, 3, 2, 3]
def baseStart_3394873 : Nat := 118140960795 + 3394873 * 2 ^ 59
def prefixEnd_3394873 : Nat := 4983230072969 + 3 ^ 40 * 3394873 * 2
def baseEnd_3394873 : Nat := 1162134406647467518316513

theorem tailTrace_3394873 : CollatzResearch.WordTrace tailWord_3394873 prefixEnd_3394873 1162134406647467518316513 := by
  unfold tailWord_3394873
  simp only [CollatzResearch.WordTrace]
  refine ⟨123821190629962393993421273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82547460419974929328947515 123821190629962393993421273)
  ·
    refine ⟨92865892972471795495065955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123821190629962393993421273 92865892972471795495065955)
    ·
      refine ⟨139298839458707693242598933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92865892972471795495065955 139298839458707693242598933)
      ·
        refine ⟨6529633099626923120746825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 139298839458707693242598933 6529633099626923120746825)
        ·
          refine ⟨4897224824720192340560119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6529633099626923120746825 4897224824720192340560119)
          ·
            refine ⟨7345837237080288510840179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4897224824720192340560119 7345837237080288510840179)
            ·
              refine ⟨11018755855620432766260269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7345837237080288510840179 11018755855620432766260269)
              ·
                refine ⟨4132033445857662287347601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11018755855620432766260269 4132033445857662287347601)
                ·
                  refine ⟨3099025084393246715510701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4132033445857662287347601 3099025084393246715510701)
                  ·
                    refine ⟨1162134406647467518316513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3099025084393246715510701 1162134406647467518316513)
                    ·
                      rfl

theorem cell22_3394873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 1, 3, 2, 3].length) (baseStart_3394873 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3394873 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3394873 prefixEnd_3394873 := by exact prefixLift 3394873
  have htrace : WordTrace (prefixWord ++ tailWord_3394873) baseStart_3394873 baseEnd_3394873 := by
    simpa [prefixWord, tailWord_3394873, baseEnd_3394873] using wordTrace_append hprefix tailTrace_3394873
  have hstable : (prefixWord ++ tailWord_3394873).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3394873).length < 2 ^ (prefixWord ++ tailWord_3394873).sum := by decide
  have hdescent : baseEnd_3394873 < baseStart_3394873 := by decide
  rcases family_descends (prefixWord ++ tailWord_3394873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3394909 : List Nat := [1, 4, 5, 1, 1, 2, 2, 2, 4]
def baseStart_3394909 : Nat := 118140960795 + 3394909 * 2 ^ 59
def prefixEnd_3394909 : Nat := 4983230072969 + 3 ^ 40 * 3394909 * 2
def baseEnd_3394909 : Nat := 387382243394391808138801

theorem tailTrace_3394909 : CollatzResearch.WordTrace tailWord_3394909 prefixEnd_3394909 387382243394391808138801 := by
  unfold tailWord_3394909
  simp only [CollatzResearch.WordTrace]
  refine ⟨123822503657831972141731781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82548335771887981427821187 123822503657831972141731781)
  ·
    refine ⟨23216719435843494776574709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 123822503657831972141731781 23216719435843494776574709)
    ·
      refine ⟨2176567447110327635303879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 23216719435843494776574709 2176567447110327635303879)
      ·
        refine ⟨3264851170665491452955819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2176567447110327635303879 3264851170665491452955819)
        ·
          refine ⟨4897276755998237179433729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3264851170665491452955819 4897276755998237179433729)
          ·
            refine ⟨3672957566998677884575297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4897276755998237179433729 3672957566998677884575297)
            ·
              refine ⟨2754718175249008413431473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3672957566998677884575297 2754718175249008413431473)
              ·
                refine ⟨2066038631436756310073605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2754718175249008413431473 2066038631436756310073605)
                ·
                  refine ⟨387382243394391808138801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2066038631436756310073605 387382243394391808138801)
                  ·
                    rfl

theorem cell22_3394909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 2, 2, 2, 4].length) (baseStart_3394909 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3394909 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3394909 prefixEnd_3394909 := by exact prefixLift 3394909
  have htrace : WordTrace (prefixWord ++ tailWord_3394909) baseStart_3394909 baseEnd_3394909 := by
    simpa [prefixWord, tailWord_3394909, baseEnd_3394909] using wordTrace_append hprefix tailTrace_3394909
  have hstable : (prefixWord ++ tailWord_3394909).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3394909).length < 2 ^ (prefixWord ++ tailWord_3394909).sum := by decide
  have hdescent : baseEnd_3394909 < baseStart_3394909 := by decide
  rcases family_descends (prefixWord ++ tailWord_3394909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3394976 : List Nat := [2, 1, 1, 4, 1, 2, 1, 6, 4]
def baseStart_3394976 : Nat := 118140960795 + 3394976 * 2 ^ 59
def prefixEnd_3394976 : Nat := 4983230072969 + 3 ^ 40 * 3394976 * 2
def baseEnd_3394976 : Nat := 387389888550803194330399

theorem tailTrace_3394976 : CollatzResearch.WordTrace tailWord_3394976 prefixEnd_3394976 387389888550803194330399 := by
  unfold tailWord_3394976
  simp only [CollatzResearch.WordTrace]
  refine ⟨61912473674294621292210391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82549964899059495056280521 61912473674294621292210391)
  ·
    refine ⟨92868710511441931938315587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61912473674294621292210391 92868710511441931938315587)
    ·
      refine ⟨139303065767162897907473381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92868710511441931938315587 139303065767162897907473381)
      ·
        refine ⟨26119324831343043357651259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 139303065767162897907473381 26119324831343043357651259)
        ·
          refine ⟨39178987247014565036476889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26119324831343043357651259 39178987247014565036476889)
          ·
            refine ⟨29384240435260923777357667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39178987247014565036476889 29384240435260923777357667)
            ·
              refine ⟨44076360652891385666036501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29384240435260923777357667 44076360652891385666036501)
              ·
                refine ⟨2066079405604283703095461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 44076360652891385666036501 2066079405604283703095461)
                ·
                  refine ⟨387389888550803194330399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2066079405604283703095461 387389888550803194330399)
                  ·
                    rfl

theorem cell22_3394976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 6, 4].length) (baseStart_3394976 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3394976 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3394976 prefixEnd_3394976 := by exact prefixLift 3394976
  have htrace : WordTrace (prefixWord ++ tailWord_3394976) baseStart_3394976 baseEnd_3394976 := by
    simpa [prefixWord, tailWord_3394976, baseEnd_3394976] using wordTrace_append hprefix tailTrace_3394976
  have hstable : (prefixWord ++ tailWord_3394976).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3394976).length < 2 ^ (prefixWord ++ tailWord_3394976).sum := by decide
  have hdescent : baseEnd_3394976 < baseStart_3394976 := by decide
  rcases family_descends (prefixWord ++ tailWord_3394976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3394991 : List Nat := [1, 1, 2, 1, 2, 2, 1, 7, 2, 3]
def baseStart_3394991 : Nat := 118140960795 + 3394991 * 2 ^ 59
def prefixEnd_3394991 : Nat := 4983230072969 + 3 ^ 40 * 3394991 * 2
def baseEnd_3394991 : Nat := 1162174800458954543866151

theorem tailTrace_3394991 : CollatzResearch.WordTrace tailWord_3394991 prefixEnd_3394991 1162174800458954543866151 := by
  unfold tailWord_3394991
  simp only [CollatzResearch.WordTrace]
  refine ⟨123825494443534900146216827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82550329629023266764144551 123825494443534900146216827)
  ·
    refine ⟨185738241665302350219325241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123825494443534900146216827 185738241665302350219325241)
    ·
      refine ⟨139303681248976762664493931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 185738241665302350219325241 139303681248976762664493931)
      ·
        refine ⟨208955521873465143996740897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139303681248976762664493931 208955521873465143996740897)
        ·
          refine ⟨156716641405098857997555673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 208955521873465143996740897 156716641405098857997555673)
          ·
            refine ⟨117537481053824143498166755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 156716641405098857997555673 117537481053824143498166755)
            ·
              refine ⟨176306221580736215247250133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 117537481053824143498166755 176306221580736215247250133)
              ·
                refine ⟨4132177068298505044857425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 176306221580736215247250133 4132177068298505044857425)
                ·
                  refine ⟨3099132801223878783643069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4132177068298505044857425 3099132801223878783643069)
                  ·
                    refine ⟨1162174800458954543866151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3099132801223878783643069 1162174800458954543866151)
                    ·
                      rfl

theorem cell22_3394991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 7, 2, 3].length) (baseStart_3394991 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3394991 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3394991 prefixEnd_3394991 := by exact prefixLift 3394991
  have htrace : WordTrace (prefixWord ++ tailWord_3394991) baseStart_3394991 baseEnd_3394991 := by
    simpa [prefixWord, tailWord_3394991, baseEnd_3394991] using wordTrace_append hprefix tailTrace_3394991
  have hstable : (prefixWord ++ tailWord_3394991).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3394991).length < 2 ^ (prefixWord ++ tailWord_3394991).sum := by decide
  have hdescent : baseEnd_3394991 < baseStart_3394991 := by decide
  rcases family_descends (prefixWord ++ tailWord_3394991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3395006 : List Nat := [4, 2, 1, 1, 1, 1, 1, 5, 2, 4]
def baseStart_3395006 : Nat := 118140960795 + 3395006 * 2 ^ 59
def prefixEnd_3395006 : Nat := 4983230072969 + 3 ^ 40 * 3395006 * 2
def baseEnd_3395006 : Nat := 1162179935265499504741105

theorem tailTrace_3395006 : CollatzResearch.WordTrace tailWord_3395006 prefixEnd_3395006 1162179935265499504741105 := by
  unfold tailWord_3395006
  simp only [CollatzResearch.WordTrace]
  refine ⟨15478255192310069713501609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 82550694358987038472008581 15478255192310069713501609)
  ·
    refine ⟨11608691394232552285126207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15478255192310069713501609 11608691394232552285126207)
    ·
      refine ⟨17413037091348828427689311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11608691394232552285126207 17413037091348828427689311)
      ·
        refine ⟨26119555637023242641533967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17413037091348828427689311 26119555637023242641533967)
        ·
          refine ⟨39179333455534863962300951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26119555637023242641533967 39179333455534863962300951)
          ·
            refine ⟨58769000183302295943451427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39179333455534863962300951 58769000183302295943451427)
            ·
              refine ⟨88153500274953443915177141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58769000183302295943451427 88153500274953443915177141)
              ·
                refine ⟨8264390650776885367047857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 88153500274953443915177141 8264390650776885367047857)
                ·
                  refine ⟨6198292988082664025285893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8264390650776885367047857 6198292988082664025285893)
                  ·
                    refine ⟨1162179935265499504741105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6198292988082664025285893 1162179935265499504741105)
                    ·
                      rfl

theorem cell22_3395006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 5, 2, 4].length) (baseStart_3395006 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3395006 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3395006 prefixEnd_3395006 := by exact prefixLift 3395006
  have htrace : WordTrace (prefixWord ++ tailWord_3395006) baseStart_3395006 baseEnd_3395006 := by
    simpa [prefixWord, tailWord_3395006, baseEnd_3395006] using wordTrace_append hprefix tailTrace_3395006
  have hstable : (prefixWord ++ tailWord_3395006).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3395006).length < 2 ^ (prefixWord ++ tailWord_3395006).sum := by decide
  have hdescent : baseEnd_3395006 < baseStart_3395006 := by decide
  rcases family_descends (prefixWord ++ tailWord_3395006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3395078 : List Nat := [6, 2, 1, 1, 3, 1, 2, 2, 4]
def baseStart_3395078 : Nat := 118140960795 + 3395078 * 2 ^ 59
def prefixEnd_3395078 : Nat := 4983230072969 + 3 ^ 40 * 3395078 * 2
def baseEnd_3395078 : Nat := 387401527445638438980295

theorem tailTrace_3395078 : CollatzResearch.WordTrace tailWord_3395078 prefixEnd_3395078 387401527445638438980295 := by
  unfold tailWord_3395078
  simp only [CollatzResearch.WordTrace]
  refine ⟨3869645862319366062644809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 82552445062813142669755925 3869645862319366062644809)
  ·
    refine ⟨2902234396739524546983607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3869645862319366062644809 2902234396739524546983607)
    ·
      refine ⟨4353351595109286820475411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2902234396739524546983607 4353351595109286820475411)
      ·
        refine ⟨6530027392663930230713117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4353351595109286820475411 6530027392663930230713117)
        ·
          refine ⟨2448760272248973836517419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6530027392663930230713117 2448760272248973836517419)
          ·
            refine ⟨3673140408373460754776129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2448760272248973836517419 3673140408373460754776129)
            ·
              refine ⟨2754855306280095566082097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3673140408373460754776129 2754855306280095566082097)
              ·
                refine ⟨2066141479710071674561573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2754855306280095566082097 2066141479710071674561573)
                ·
                  refine ⟨387401527445638438980295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2066141479710071674561573 387401527445638438980295)
                  ·
                    rfl

theorem cell22_3395078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 3, 1, 2, 2, 4].length) (baseStart_3395078 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3395078 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3395078 prefixEnd_3395078 := by exact prefixLift 3395078
  have htrace : WordTrace (prefixWord ++ tailWord_3395078) baseStart_3395078 baseEnd_3395078 := by
    simpa [prefixWord, tailWord_3395078, baseEnd_3395078] using wordTrace_append hprefix tailTrace_3395078
  have hstable : (prefixWord ++ tailWord_3395078).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3395078).length < 2 ^ (prefixWord ++ tailWord_3395078).sum := by decide
  have hdescent : baseEnd_3395078 < baseStart_3395078 := by decide
  rcases family_descends (prefixWord ++ tailWord_3395078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3395083 : List Nat := [1, 1, 1, 1, 8, 1, 2, 2, 5]
def baseStart_3395083 : Nat := 118140960795 + 3395083 * 2 ^ 59
def prefixEnd_3395083 : Nat := 4983230072969 + 3 ^ 40 * 3395083 * 2
def baseEnd_3395083 : Nat := 387402097979698990188623

theorem tailTrace_3395083 : CollatzResearch.WordTrace tailWord_3395083 prefixEnd_3395083 387402097979698990188623 := by
  unfold tailWord_3395083
  simp only [CollatzResearch.WordTrace]
  refine ⟨123828849959201599858565903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82552566639467733239043935 123828849959201599858565903)
  ·
    refine ⟨185743274938802399787848855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123828849959201599858565903 185743274938802399787848855)
    ·
      refine ⟨278614912408203599681773283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185743274938802399787848855 278614912408203599681773283)
      ·
        refine ⟨417922368612305399522659925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 278614912408203599681773283 417922368612305399522659925)
        ·
          refine ⟨4897527757175453900656171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 417922368612305399522659925 4897527757175453900656171)
          ·
            refine ⟨7346291635763180850984257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4897527757175453900656171 7346291635763180850984257)
            ·
              refine ⟨5509718726822385638238193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7346291635763180850984257 5509718726822385638238193)
              ·
                refine ⟨4132289045116789228678645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5509718726822385638238193 4132289045116789228678645)
                ·
                  refine ⟨387402097979698990188623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4132289045116789228678645 387402097979698990188623)
                  ·
                    rfl

theorem cell22_3395083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 2, 2, 5].length) (baseStart_3395083 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3395083 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3395083 prefixEnd_3395083 := by exact prefixLift 3395083
  have htrace : WordTrace (prefixWord ++ tailWord_3395083) baseStart_3395083 baseEnd_3395083 := by
    simpa [prefixWord, tailWord_3395083, baseEnd_3395083] using wordTrace_append hprefix tailTrace_3395083
  have hstable : (prefixWord ++ tailWord_3395083).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3395083).length < 2 ^ (prefixWord ++ tailWord_3395083).sum := by decide
  have hdescent : baseEnd_3395083 < baseStart_3395083 := by decide
  rcases family_descends (prefixWord ++ tailWord_3395083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3395128 : List Nat := [2, 1, 2, 1, 4, 2, 1, 5, 4]
def baseStart_3395128 : Nat := 118140960795 + 3395128 * 2 ^ 59
def prefixEnd_3395128 : Nat := 4983230072969 + 3 ^ 40 * 3395128 * 2
def baseEnd_3395128 : Nat := 387407232786243951063577

theorem tailTrace_3395128 : CollatzResearch.WordTrace tailWord_3395128 prefixEnd_3395128 387407232786243951063577 := by
  unfold tailWord_3395128
  simp only [CollatzResearch.WordTrace]
  refine ⟨61915245622019286271977019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82553660829359048362636025 61915245622019286271977019)
  ·
    refine ⟨92872868433028929407965529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61915245622019286271977019 92872868433028929407965529)
    ·
      refine ⟨69654651324771697055974147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92872868433028929407965529 69654651324771697055974147)
      ·
        refine ⟨104481976987157545583961221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69654651324771697055974147 104481976987157545583961221)
        ·
          refine ⟨19590370685092039796992729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 104481976987157545583961221 19590370685092039796992729)
          ·
            refine ⟨14692778013819029847744547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19590370685092039796992729 14692778013819029847744547)
            ·
              refine ⟨22039167020728544771616821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14692778013819029847744547 22039167020728544771616821)
              ·
                refine ⟨2066171908193301072339077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22039167020728544771616821 2066171908193301072339077)
                ·
                  refine ⟨387407232786243951063577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2066171908193301072339077 387407232786243951063577)
                  ·
                    rfl

theorem cell22_3395128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 1, 5, 4].length) (baseStart_3395128 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3395128 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3395128 prefixEnd_3395128 := by exact prefixLift 3395128
  have htrace : WordTrace (prefixWord ++ tailWord_3395128) baseStart_3395128 baseEnd_3395128 := by
    simpa [prefixWord, tailWord_3395128, baseEnd_3395128] using wordTrace_append hprefix tailTrace_3395128
  have hstable : (prefixWord ++ tailWord_3395128).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3395128).length < 2 ^ (prefixWord ++ tailWord_3395128).sum := by decide
  have hdescent : baseEnd_3395128 < baseStart_3395128 := by decide
  rcases family_descends (prefixWord ++ tailWord_3395128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3395141 : List Nat := [1, 3, 1, 1, 1, 4, 2, 1, 4, 4]
def baseStart_3395141 : Nat := 118140960795 + 3395141 * 2 ^ 59
def prefixEnd_3395141 : Nat := 4983230072969 + 3 ^ 40 * 3395141 * 2
def baseEnd_3395141 : Nat := 1162226148524404152615691

theorem tailTrace_3395141 : CollatzResearch.WordTrace tailWord_3395141 prefixEnd_3395141 1162226148524404152615691 := by
  unfold tailWord_3395141
  simp only [CollatzResearch.WordTrace]
  refine ⟨123830965392991475764177277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82553976928660983842784851 123830965392991475764177277)
  ·
    refine ⟨46436612022371803411566479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123830965392991475764177277 46436612022371803411566479)
    ·
      refine ⟨69654918033557705117349719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46436612022371803411566479 69654918033557705117349719)
      ·
        refine ⟨104482377050336557676024579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69654918033557705117349719 104482377050336557676024579)
        ·
          refine ⟨156723565575504836514036869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104482377050336557676024579 156723565575504836514036869)
          ·
            refine ⟨29385668545407156846381913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 156723565575504836514036869 29385668545407156846381913)
            ·
              refine ⟨22039251409055367634786435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29385668545407156846381913 22039251409055367634786435)
              ·
                refine ⟨33058877113583051452179653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22039251409055367634786435 33058877113583051452179653)
                ·
                  refine ⟨6198539458796822147283685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33058877113583051452179653 6198539458796822147283685)
                  ·
                    refine ⟨1162226148524404152615691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6198539458796822147283685 1162226148524404152615691)
                    ·
                      rfl

theorem cell22_3395141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 2, 1, 4, 4].length) (baseStart_3395141 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3395141 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3395141 prefixEnd_3395141 := by exact prefixLift 3395141
  have htrace : WordTrace (prefixWord ++ tailWord_3395141) baseStart_3395141 baseEnd_3395141 := by
    simpa [prefixWord, tailWord_3395141, baseEnd_3395141] using wordTrace_append hprefix tailTrace_3395141
  have hstable : (prefixWord ++ tailWord_3395141).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3395141).length < 2 ^ (prefixWord ++ tailWord_3395141).sum := by decide
  have hdescent : baseEnd_3395141 < baseStart_3395141 := by decide
  rcases family_descends (prefixWord ++ tailWord_3395141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3395156 : List Nat := [2, 4, 1, 1, 1, 2, 2, 9]
def baseStart_3395156 : Nat := 118140960795 + 3395156 * 2 ^ 59
def prefixEnd_3395156 : Nat := 4983230072969 + 3 ^ 40 * 3395156 * 2
def baseEnd_3395156 : Nat := 129136809258994345943405

theorem tailTrace_3395156 : CollatzResearch.WordTrace tailWord_3395156 prefixEnd_3395156 129136809258994345943405 := by
  unfold tailWord_3395156
  simp only [CollatzResearch.WordTrace]
  refine ⟨61915756243968566662986661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82554341658624755550648881 61915756243968566662986661)
  ·
    refine ⟨11609204295744106249309999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 61915756243968566662986661 11609204295744106249309999)
    ·
      refine ⟨17413806443616159373964999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11609204295744106249309999 17413806443616159373964999)
      ·
        refine ⟨26120709665424239060947499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17413806443616159373964999 26120709665424239060947499)
        ·
          refine ⟨39181064498136358591421249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26120709665424239060947499 39181064498136358591421249)
          ·
            refine ⟨29385798373602268943565937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39181064498136358591421249 29385798373602268943565937)
            ·
              refine ⟨22039348780201701707674453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29385798373602268943565937 22039348780201701707674453)
              ·
                refine ⟨129136809258994345943405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 22039348780201701707674453 129136809258994345943405)
                ·
                  rfl

theorem cell22_3395156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 2, 9].length) (baseStart_3395156 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3395156 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3395156 prefixEnd_3395156 := by exact prefixLift 3395156
  have htrace : WordTrace (prefixWord ++ tailWord_3395156) baseStart_3395156 baseEnd_3395156 := by
    simpa [prefixWord, tailWord_3395156, baseEnd_3395156] using wordTrace_append hprefix tailTrace_3395156
  have hstable : (prefixWord ++ tailWord_3395156).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3395156).length < 2 ^ (prefixWord ++ tailWord_3395156).sum := by decide
  have hdescent : baseEnd_3395156 < baseStart_3395156 := by decide
  rcases family_descends (prefixWord ++ tailWord_3395156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3395173 : List Nat := [1, 3, 1, 3, 3, 1, 4, 6]
def baseStart_3395173 : Nat := 118140960795 + 3395173 * 2 ^ 59
def prefixEnd_3395173 : Nat := 4983230072969 + 3 ^ 40 * 3395173 * 2
def baseEnd_3395173 : Nat := 129137455864262970646177

theorem tailTrace_3395173 : CollatzResearch.WordTrace tailWord_3395173 prefixEnd_3395173 129137455864262970646177 := by
  unfold tailWord_3395173
  simp only [CollatzResearch.WordTrace]
  refine ⟨123832132528875545229342173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82554755019250363486228115 123832132528875545229342173)
  ·
    refine ⟨46437049698328329461003315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123832132528875545229342173 46437049698328329461003315)
    ·
      refine ⟨69655574547492494191504973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46437049698328329461003315 69655574547492494191504973)
      ·
        refine ⟨26120840455309685321814365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69655574547492494191504973 26120840455309685321814365)
        ·
          refine ⟨9795315170741131995680387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26120840455309685321814365 9795315170741131995680387)
          ·
            refine ⟨14692972756111697993520581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9795315170741131995680387 14692972756111697993520581)
            ·
              refine ⟨2754932391770943373785109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14692972756111697993520581 2754932391770943373785109)
              ·
                refine ⟨129137455864262970646177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2754932391770943373785109 129137455864262970646177)
                ·
                  rfl

theorem cell22_3395173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 4, 6].length) (baseStart_3395173 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3395173 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3395173 prefixEnd_3395173 := by exact prefixLift 3395173
  have htrace : WordTrace (prefixWord ++ tailWord_3395173) baseStart_3395173 baseEnd_3395173 := by
    simpa [prefixWord, tailWord_3395173, baseEnd_3395173] using wordTrace_append hprefix tailTrace_3395173
  have hstable : (prefixWord ++ tailWord_3395173).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3395173).length < 2 ^ (prefixWord ++ tailWord_3395173).sum := by decide
  have hdescent : baseEnd_3395173 < baseStart_3395173 := by decide
  rcases family_descends (prefixWord ++ tailWord_3395173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3395216 : List Nat := [2, 1, 1, 1, 1, 1, 3, 5, 2, 5]
def baseStart_3395216 : Nat := 118140960795 + 3395216 * 2 ^ 59
def prefixEnd_3395216 : Nat := 4983230072969 + 3 ^ 40 * 3395216 * 2
def baseEnd_3395216 : Nat := 1162251822557128956990461

theorem tailTrace_3395216 : CollatzResearch.WordTrace tailWord_3395216 prefixEnd_3395216 1162251822557128956990461 := by
  unfold tailWord_3395216
  simp only [CollatzResearch.WordTrace]
  refine ⟨61916850433859881786578751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82555800578479842382105001 61916850433859881786578751)
  ·
    refine ⟨92875275650789822679868127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61916850433859881786578751 92875275650789822679868127)
    ·
      refine ⟨139312913476184734019802191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92875275650789822679868127 139312913476184734019802191)
      ·
        refine ⟨208969370214277101029703287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139312913476184734019802191 208969370214277101029703287)
        ·
          refine ⟨313454055321415651544554931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 208969370214277101029703287 313454055321415651544554931)
          ·
            refine ⟨470181082982123477316832397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 313454055321415651544554931 470181082982123477316832397)
            ·
              refine ⟨176317906118296303993812149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 470181082982123477316832397 176317906118296303993812149)
              ·
                refine ⟨16529803698590278499419889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 176317906118296303993812149 16529803698590278499419889)
                ·
                  refine ⟨12397352773942708874564917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16529803698590278499419889 12397352773942708874564917)
                  ·
                    refine ⟨1162251822557128956990461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12397352773942708874564917 1162251822557128956990461)
                    ·
                      rfl

theorem cell22_3395216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 5, 2, 5].length) (baseStart_3395216 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3395216 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3395216 prefixEnd_3395216 := by exact prefixLift 3395216
  have htrace : WordTrace (prefixWord ++ tailWord_3395216) baseStart_3395216 baseEnd_3395216 := by
    simpa [prefixWord, tailWord_3395216, baseEnd_3395216] using wordTrace_append hprefix tailTrace_3395216
  have hstable : (prefixWord ++ tailWord_3395216).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3395216).length < 2 ^ (prefixWord ++ tailWord_3395216).sum := by decide
  have hdescent : baseEnd_3395216 < baseStart_3395216 := by decide
  rcases family_descends (prefixWord ++ tailWord_3395216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3395248 : List Nat := [2, 1, 1, 1, 2, 1, 4, 5, 1, 4]
def baseStart_3395248 : Nat := 118140960795 + 3395248 * 2 ^ 59
def prefixEnd_3395248 : Nat := 4983230072969 + 3 ^ 40 * 3395248 * 2
def baseEnd_3395248 : Nat := 1162262776811091540190363

theorem tailTrace_3395248 : CollatzResearch.WordTrace tailWord_3395248 prefixEnd_3395248 1162262776811091540190363 := by
  unfold tailWord_3395248
  simp only [CollatzResearch.WordTrace]
  refine ⟨61917434001801916519161199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82556578669069222025548265 61917434001801916519161199)
  ·
    refine ⟨92876151002702874778741799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61917434001801916519161199 92876151002702874778741799)
    ·
      refine ⟨139314226504054312168112699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92876151002702874778741799 139314226504054312168112699)
      ·
        refine ⟨208971339756081468252169049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139314226504054312168112699 208971339756081468252169049)
        ·
          refine ⟨156728504817061101189126787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 208971339756081468252169049 156728504817061101189126787)
          ·
            refine ⟨235092757225591651783690181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 156728504817061101189126787 235092757225591651783690181)
            ·
              refine ⟨44079891979798434709441909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 235092757225591651783690181 44079891979798434709441909)
              ·
                refine ⟨4132489873106103254010179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 44079891979798434709441909 4132489873106103254010179)
                ·
                  refine ⟨6198734809659154881015269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4132489873106103254010179 6198734809659154881015269)
                  ·
                    refine ⟨1162262776811091540190363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6198734809659154881015269 1162262776811091540190363)
                    ·
                      rfl

theorem cell22_3395248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 5, 1, 4].length) (baseStart_3395248 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3395248 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3395248 prefixEnd_3395248 := by exact prefixLift 3395248
  have htrace : WordTrace (prefixWord ++ tailWord_3395248) baseStart_3395248 baseEnd_3395248 := by
    simpa [prefixWord, tailWord_3395248, baseEnd_3395248] using wordTrace_append hprefix tailTrace_3395248
  have hstable : (prefixWord ++ tailWord_3395248).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3395248).length < 2 ^ (prefixWord ++ tailWord_3395248).sum := by decide
  have hdescent : baseEnd_3395248 < baseStart_3395248 := by decide
  rcases family_descends (prefixWord ++ tailWord_3395248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3395297 : List Nat := [1, 2, 3, 1, 5, 1, 2, 3, 4]
def baseStart_3395297 : Nat := 118140960795 + 3395297 * 2 ^ 59
def prefixEnd_3395297 : Nat := 4983230072969 + 3 ^ 40 * 3395297 * 2
def baseEnd_3395297 : Nat := 387426516837490581905071

theorem tailTrace_3395297 : CollatzResearch.WordTrace tailWord_3395297 prefixEnd_3395297 387426516837490581905071 := by
  unfold tailWord_3395297
  simp only [CollatzResearch.WordTrace]
  refine ⟨123836655180426314406856145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82557770120284209604570763 123836655180426314406856145)
  ·
    refine ⟨92877491385319735805142109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123836655180426314406856145 92877491385319735805142109)
    ·
      refine ⟨34829059269494900926928291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92877491385319735805142109 34829059269494900926928291)
      ·
        refine ⟨52243588904242351390392437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34829059269494900926928291 52243588904242351390392437)
        ·
          refine ⟨4897836459772720442849291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 52243588904242351390392437 4897836459772720442849291)
          ·
            refine ⟨7346754689659080664273937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4897836459772720442849291 7346754689659080664273937)
            ·
              refine ⟨5510066017244310498205453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7346754689659080664273937 5510066017244310498205453)
              ·
                refine ⟨2066274756466616436827045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5510066017244310498205453 2066274756466616436827045)
                ·
                  refine ⟨387426516837490581905071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2066274756466616436827045 387426516837490581905071)
                  ·
                    rfl

theorem cell22_3395297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 2, 3, 4].length) (baseStart_3395297 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3395297 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3395297 prefixEnd_3395297 := by exact prefixLift 3395297
  have htrace : WordTrace (prefixWord ++ tailWord_3395297) baseStart_3395297 baseEnd_3395297 := by
    simpa [prefixWord, tailWord_3395297, baseEnd_3395297] using wordTrace_append hprefix tailTrace_3395297
  have hstable : (prefixWord ++ tailWord_3395297).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3395297).length < 2 ^ (prefixWord ++ tailWord_3395297).sum := by decide
  have hdescent : baseEnd_3395297 < baseStart_3395297 := by decide
  rcases family_descends (prefixWord ++ tailWord_3395297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3395299 : List Nat := [1, 1, 1, 7, 2, 2, 2, 1, 1, 4]
def baseStart_3395299 : Nat := 118140960795 + 3395299 * 2 ^ 59
def prefixEnd_3395299 : Nat := 4983230072969 + 3 ^ 40 * 3395299 * 2
def baseEnd_3395299 : Nat := 1162280235153344407165207

theorem tailTrace_3395299 : CollatzResearch.WordTrace tailWord_3395299 prefixEnd_3395299 1162280235153344407165207 := by
  unfold tailWord_3395299
  simp only [CollatzResearch.WordTrace]
  refine ⟨123836728126419068748428951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82557818750946045832285967 123836728126419068748428951)
  ·
    refine ⟨185755092189628603122643427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123836728126419068748428951 185755092189628603122643427)
    ·
      refine ⟨278632638284442904683965141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185755092189628603122643427 278632638284442904683965141)
      ·
        refine ⟨6530452459791630578530433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 278632638284442904683965141 6530452459791630578530433)
        ·
          refine ⟨4897839344843722933897825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6530452459791630578530433 4897839344843722933897825)
          ·
            refine ⟨3673379508632792200423369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4897839344843722933897825 3673379508632792200423369)
            ·
              refine ⟨2755034631474594150317527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3673379508632792200423369 2755034631474594150317527)
              ·
                refine ⟨4132551947211891225476291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2755034631474594150317527 4132551947211891225476291)
                ·
                  refine ⟨6198827920817836838214437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4132551947211891225476291 6198827920817836838214437)
                  ·
                    refine ⟨1162280235153344407165207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6198827920817836838214437 1162280235153344407165207)
                    ·
                      rfl

theorem cell22_3395299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 2, 2, 1, 1, 4].length) (baseStart_3395299 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3395299 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3395299 prefixEnd_3395299 := by exact prefixLift 3395299
  have htrace : WordTrace (prefixWord ++ tailWord_3395299) baseStart_3395299 baseEnd_3395299 := by
    simpa [prefixWord, tailWord_3395299, baseEnd_3395299] using wordTrace_append hprefix tailTrace_3395299
  have hstable : (prefixWord ++ tailWord_3395299).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3395299).length < 2 ^ (prefixWord ++ tailWord_3395299).sum := by decide
  have hdescent : baseEnd_3395299 < baseStart_3395299 := by decide
  rcases family_descends (prefixWord ++ tailWord_3395299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3395340 : List Nat := [2, 2, 1, 2, 2, 1, 4, 2, 3, 3]
def baseStart_3395340 : Nat := 118140960795 + 3395340 * 2 ^ 59
def prefixEnd_3395340 : Nat := 4983230072969 + 3 ^ 40 * 3395340 * 2
def baseEnd_3395340 : Nat := 1162294270291233966890081

theorem tailTrace_3395340 : CollatzResearch.WordTrace tailWord_3395340 prefixEnd_3395340 1162294270291233966890081 := by
  unfold tailWord_3395340
  simp only [CollatzResearch.WordTrace]
  refine ⟨61919111759635266375335737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82558815679513688500447649 61919111759635266375335737)
  ·
    refine ⟨46439333819726449781501803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61919111759635266375335737 46439333819726449781501803)
    ·
      refine ⟨69659000729589674672252705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46439333819726449781501803 69659000729589674672252705)
      ·
        refine ⟨52244250547192256004189529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69659000729589674672252705 52244250547192256004189529)
        ·
          refine ⟨39183187910394192003142147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52244250547192256004189529 39183187910394192003142147)
          ·
            refine ⟨58774781865591288004713221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39183187910394192003142147 58774781865591288004713221)
            ·
              refine ⟨11020271599798366500883729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 58774781865591288004713221 11020271599798366500883729)
              ·
                refine ⟨8265203699848774875662797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11020271599798366500883729 8265203699848774875662797)
                ·
                  refine ⟨3099451387443290578373549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8265203699848774875662797 3099451387443290578373549)
                  ·
                    refine ⟨1162294270291233966890081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3099451387443290578373549 1162294270291233966890081)
                    ·
                      rfl

theorem cell22_3395340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 4, 2, 3, 3].length) (baseStart_3395340 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3395340 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3395340 prefixEnd_3395340 := by exact prefixLift 3395340
  have htrace : WordTrace (prefixWord ++ tailWord_3395340) baseStart_3395340 baseEnd_3395340 := by
    simpa [prefixWord, tailWord_3395340, baseEnd_3395340] using wordTrace_append hprefix tailTrace_3395340
  have hstable : (prefixWord ++ tailWord_3395340).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3395340).length < 2 ^ (prefixWord ++ tailWord_3395340).sum := by decide
  have hdescent : baseEnd_3395340 < baseStart_3395340 := by decide
  rcases family_descends (prefixWord ++ tailWord_3395340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3395348 : List Nat := [2, 4, 4, 1, 1, 2, 1, 3, 4]
def baseStart_3395348 : Nat := 118140960795 + 3395348 * 2 ^ 59
def prefixEnd_3395348 : Nat := 4983230072969 + 3 ^ 40 * 3395348 * 2
def baseEnd_3395348 : Nat := 387432336284908204230019

theorem tailTrace_3395348 : CollatzResearch.WordTrace tailWord_3395348 prefixEnd_3395348 387432336284908204230019 := by
  unfold tailWord_3395348
  simp only [CollatzResearch.WordTrace]
  refine ⟨61919257651620775058481349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82559010202161033411308465 61919257651620775058481349)
  ·
    refine ⟨11609860809678895323465253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 61919257651620775058481349 11609860809678895323465253)
    ·
      refine ⟨2176848901814792873149735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11609860809678895323465253 2176848901814792873149735)
      ·
        refine ⟨3265273352722189309724603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2176848901814792873149735 3265273352722189309724603)
        ·
          refine ⟨4897910029083283964586905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3265273352722189309724603 4897910029083283964586905)
          ·
            refine ⟨3673432521812462973440179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4897910029083283964586905 3673432521812462973440179)
            ·
              refine ⟨5510148782718694460160269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3673432521812462973440179 5510148782718694460160269)
              ·
                refine ⟨2066305793519510422560101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5510148782718694460160269 2066305793519510422560101)
                ·
                  refine ⟨387432336284908204230019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2066305793519510422560101 387432336284908204230019)
                  ·
                    rfl

theorem cell22_3395348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 2, 1, 3, 4].length) (baseStart_3395348 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3395348 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3395348 prefixEnd_3395348 := by exact prefixLift 3395348
  have htrace : WordTrace (prefixWord ++ tailWord_3395348) baseStart_3395348 baseEnd_3395348 := by
    simpa [prefixWord, tailWord_3395348, baseEnd_3395348] using wordTrace_append hprefix tailTrace_3395348
  have hstable : (prefixWord ++ tailWord_3395348).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3395348).length < 2 ^ (prefixWord ++ tailWord_3395348).sum := by decide
  have hdescent : baseEnd_3395348 < baseStart_3395348 := by decide
  rcases family_descends (prefixWord ++ tailWord_3395348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3395400 : List Nat := [2, 1, 3, 1, 1, 5, 1, 1, 3, 4]
def baseStart_3395400 : Nat := 118140960795 + 3395400 * 2 ^ 59
def prefixEnd_3395400 : Nat := 4983230072969 + 3 ^ 40 * 3395400 * 2
def baseEnd_3395400 : Nat := 1162314809517413810389897

theorem tailTrace_3395400 : CollatzResearch.WordTrace tailWord_3395400 prefixEnd_3395400 1162314809517413810389897 := by
  unfold tailWord_3395400
  simp only [CollatzResearch.WordTrace]
  refine ⟨61920205949526581498927827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82560274599368775331903769 61920205949526581498927827)
  ·
    refine ⟨92880308924289872248391741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61920205949526581498927827 92880308924289872248391741)
    ·
      refine ⟨34830115846608702093146903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92880308924289872248391741 34830115846608702093146903)
      ·
        refine ⟨52245173769913053139720355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34830115846608702093146903 52245173769913053139720355)
        ·
          refine ⟨78367760654869579709580533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52245173769913053139720355 78367760654869579709580533)
          ·
            refine ⟨7346977561394023097773175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 78367760654869579709580533 7346977561394023097773175)
            ·
              refine ⟨11020466342091034646659763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7346977561394023097773175 11020466342091034646659763)
              ·
                refine ⟨16530699513136551969989645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11020466342091034646659763 16530699513136551969989645)
                ·
                  refine ⟨6199012317426206988746117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16530699513136551969989645 6199012317426206988746117)
                  ·
                    refine ⟨1162314809517413810389897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6199012317426206988746117 1162314809517413810389897)
                    ·
                      rfl

theorem cell22_3395400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 1, 1, 3, 4].length) (baseStart_3395400 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3395400 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3395400 prefixEnd_3395400 := by exact prefixLift 3395400
  have htrace : WordTrace (prefixWord ++ tailWord_3395400) baseStart_3395400 baseEnd_3395400 := by
    simpa [prefixWord, tailWord_3395400, baseEnd_3395400] using wordTrace_append hprefix tailTrace_3395400
  have hstable : (prefixWord ++ tailWord_3395400).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3395400).length < 2 ^ (prefixWord ++ tailWord_3395400).sum := by decide
  have hdescent : baseEnd_3395400 < baseStart_3395400 := by decide
  rcases family_descends (prefixWord ++ tailWord_3395400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3395417 : List Nat := [1, 2, 1, 2, 2, 3, 5, 1, 1, 4]
def baseStart_3395417 : Nat := 118140960795 + 3395417 * 2 ^ 59
def prefixEnd_3395417 : Nat := 4983230072969 + 3 ^ 40 * 3395417 * 2
def baseEnd_3395417 : Nat := 1162320628964831432714845

theorem tailTrace_3395417 : CollatzResearch.WordTrace tailWord_3395417 prefixEnd_3395417 1162320628964831432714845 := by
  unfold tailWord_3395417
  simp only [CollatzResearch.WordTrace]
  refine ⟨123841031939991574901224505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82560687959994383267483003 123841031939991574901224505)
  ·
    refine ⟨92880773954993681175918379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123841031939991574901224505 92880773954993681175918379)
    ·
      refine ⟨139321160932490521763877569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92880773954993681175918379 139321160932490521763877569)
      ·
        refine ⟨104490870699367891322908177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139321160932490521763877569 104490870699367891322908177)
        ·
          refine ⟨78368153024525918492181133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104490870699367891322908177 78368153024525918492181133)
          ·
            refine ⟨29388057384197219434567925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78368153024525918492181133 29388057384197219434567925)
            ·
              refine ⟨2755130379768489321990743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 29388057384197219434567925 2755130379768489321990743)
              ·
                refine ⟨4132695569652733982986115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2755130379768489321990743 4132695569652733982986115)
                ·
                  refine ⟨6199043354479100974479173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4132695569652733982986115 6199043354479100974479173)
                  ·
                    refine ⟨1162320628964831432714845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6199043354479100974479173 1162320628964831432714845)
                    ·
                      rfl

theorem cell22_3395417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 5, 1, 1, 4].length) (baseStart_3395417 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3395417 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3395417 prefixEnd_3395417 := by exact prefixLift 3395417
  have htrace : WordTrace (prefixWord ++ tailWord_3395417) baseStart_3395417 baseEnd_3395417 := by
    simpa [prefixWord, tailWord_3395417, baseEnd_3395417] using wordTrace_append hprefix tailTrace_3395417
  have hstable : (prefixWord ++ tailWord_3395417).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3395417).length < 2 ^ (prefixWord ++ tailWord_3395417).sum := by decide
  have hdescent : baseEnd_3395417 < baseStart_3395417 := by decide
  rcases family_descends (prefixWord ++ tailWord_3395417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3395432 : List Nat := [2, 1, 4, 2, 1, 1, 3, 4, 4]
def baseStart_3395432 : Nat := 118140960795 + 3395432 * 2 ^ 59
def prefixEnd_3395432 : Nat := 4983230072969 + 3 ^ 40 * 3395432 * 2
def baseEnd_3395432 : Nat := 387441921257125464529933

theorem tailTrace_3395432 : CollatzResearch.WordTrace tailWord_3395432 prefixEnd_3395432 387441921257125464529933 := by
  unfold tailWord_3395432
  simp only [CollatzResearch.WordTrace]
  refine ⟨61920789517468616231510275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82561052689958154975347033 61920789517468616231510275)
  ·
    refine ⟨92881184276202924347265413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61920789517468616231510275 92881184276202924347265413)
    ·
      refine ⟨17415222051788048315112265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 92881184276202924347265413 17415222051788048315112265)
      ·
        refine ⟨13061416538841036236334199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17415222051788048315112265 13061416538841036236334199)
        ·
          refine ⟨19592124808261554354501299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13061416538841036236334199 19592124808261554354501299)
          ·
            refine ⟨29388187212392331531751949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19592124808261554354501299 29388187212392331531751949)
            ·
              refine ⟨11020570204647124324406981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29388187212392331531751949 11020570204647124324406981)
              ·
                refine ⟨2066356913371335810826309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11020570204647124324406981 2066356913371335810826309)
                ·
                  refine ⟨387441921257125464529933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2066356913371335810826309 387441921257125464529933)
                  ·
                    rfl

theorem cell22_3395432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 3, 4, 4].length) (baseStart_3395432 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3395432 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3395432 prefixEnd_3395432 := by exact prefixLift 3395432
  have htrace : WordTrace (prefixWord ++ tailWord_3395432) baseStart_3395432 baseEnd_3395432 := by
    simpa [prefixWord, tailWord_3395432, baseEnd_3395432] using wordTrace_append hprefix tailTrace_3395432
  have hstable : (prefixWord ++ tailWord_3395432).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3395432).length < 2 ^ (prefixWord ++ tailWord_3395432).sum := by decide
  have hdescent : baseEnd_3395432 < baseStart_3395432 := by decide
  rcases family_descends (prefixWord ++ tailWord_3395432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3395445 : List Nat := [1, 3, 4, 1, 1, 1, 2, 2, 1, 6]
def baseStart_3395445 : Nat := 118140960795 + 3395445 * 2 ^ 59
def prefixEnd_3395445 : Nat := 4983230072969 + 3 ^ 40 * 3395445 * 2
def baseEnd_3395445 : Nat := 1162330213937048693014759

theorem tailTrace_3395445 : CollatzResearch.WordTrace tailWord_3395445 prefixEnd_3395445 1162330213937048693014759 := by
  unfold tailWord_3395445
  simp only [CollatzResearch.WordTrace]
  refine ⟨123842053183890135683243789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82561368789260090455495859 123842053183890135683243789)
  ·
    refine ⟨46440769943958800881216421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123842053183890135683243789 46440769943958800881216421)
    ·
      refine ⟨8707644364492275165228079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46440769943958800881216421 8707644364492275165228079)
      ·
        refine ⟨13061466546738412747842119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8707644364492275165228079 13061466546738412747842119)
        ·
          refine ⟨19592199820107619121763179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13061466546738412747842119 19592199820107619121763179)
          ·
            refine ⟨29388299730161428682644769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19592199820107619121763179 29388299730161428682644769)
            ·
              refine ⟨22041224797621071511983577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29388299730161428682644769 22041224797621071511983577)
              ·
                refine ⟨16530918598215803633987683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22041224797621071511983577 16530918598215803633987683)
                ·
                  refine ⟨24796377897323705450981525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16530918598215803633987683 24796377897323705450981525)
                  ·
                    refine ⟨1162330213937048693014759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24796377897323705450981525 1162330213937048693014759)
                    ·
                      rfl

theorem cell22_3395445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 2, 2, 1, 6].length) (baseStart_3395445 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3395445 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3395445 prefixEnd_3395445 := by exact prefixLift 3395445
  have htrace : WordTrace (prefixWord ++ tailWord_3395445) baseStart_3395445 baseEnd_3395445 := by
    simpa [prefixWord, tailWord_3395445, baseEnd_3395445] using wordTrace_append hprefix tailTrace_3395445
  have hstable : (prefixWord ++ tailWord_3395445).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3395445).length < 2 ^ (prefixWord ++ tailWord_3395445).sum := by decide
  have hdescent : baseEnd_3395445 < baseStart_3395445 := by decide
  rcases family_descends (prefixWord ++ tailWord_3395445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3395492 : List Nat := [2, 3, 1, 2, 1, 3, 1, 3, 3, 3]
def baseStart_3395492 : Nat := 118140960795 + 3395492 * 2 ^ 59
def prefixEnd_3395492 : Nat := 4983230072969 + 3 ^ 40 * 3395492 * 2
def baseEnd_3395492 : Nat := 1162346302997556237089615

theorem tailTrace_3395492 : CollatzResearch.WordTrace tailWord_3395492 prefixEnd_3395492 1162346302997556237089615 := by
  unfold tailWord_3395492
  simp only [CollatzResearch.WordTrace]
  refine ⟨61921883707359931355102365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82562511609813241806803153 61921883707359931355102365)
  ·
    refine ⟨23220706390259974258163387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61921883707359931355102365 23220706390259974258163387)
    ·
      refine ⟨34831059585389961387245081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23220706390259974258163387 34831059585389961387245081)
      ·
        refine ⟨26123294689042471040433811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34831059585389961387245081 26123294689042471040433811)
        ·
          refine ⟨39184942033563706560650717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26123294689042471040433811 39184942033563706560650717)
          ·
            refine ⟨14694353262586389960244019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39184942033563706560650717 14694353262586389960244019)
            ·
              refine ⟨22041529893879584940366029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14694353262586389960244019 22041529893879584940366029)
              ·
                refine ⟨8265573710204844352637261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22041529893879584940366029 8265573710204844352637261)
                ·
                  refine ⟨3099590141326816632238973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8265573710204844352637261 3099590141326816632238973)
                  ·
                    refine ⟨1162346302997556237089615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3099590141326816632238973 1162346302997556237089615)
                    ·
                      rfl

theorem cell22_3395492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 1, 3, 3, 3].length) (baseStart_3395492 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3395492 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3395492 prefixEnd_3395492 := by exact prefixLift 3395492
  have htrace : WordTrace (prefixWord ++ tailWord_3395492) baseStart_3395492 baseEnd_3395492 := by
    simpa [prefixWord, tailWord_3395492, baseEnd_3395492] using wordTrace_append hprefix tailTrace_3395492
  have hstable : (prefixWord ++ tailWord_3395492).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3395492).length < 2 ^ (prefixWord ++ tailWord_3395492).sum := by decide
  have hdescent : baseEnd_3395492 < baseStart_3395492 := by decide
  rcases family_descends (prefixWord ++ tailWord_3395492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3395590 : List Nat := [6, 2, 1, 2, 1, 1, 2, 2, 5]
def baseStart_3395590 : Nat := 118140960795 + 3395590 * 2 ^ 59
def prefixEnd_3395590 : Nat := 4983230072969 + 3 ^ 40 * 3395590 * 2
def baseEnd_3395590 : Nat := 387459950133438882713105

theorem tailTrace_3395590 : CollatzResearch.WordTrace tailWord_3395590 prefixEnd_3395590 387459950133438882713105 := by
  unfold tailWord_3395590
  simp only [CollatzResearch.WordTrace]
  refine ⟨3870229430261400795227257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 82564894512243216964848149 3870229430261400795227257)
  ·
    refine ⟨2902672072696050596420443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3870229430261400795227257 2902672072696050596420443)
    ·
      refine ⟨4354008109044075894630665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2902672072696050596420443 4354008109044075894630665)
      ·
        refine ⟨3265506081783056920972999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4354008109044075894630665 3265506081783056920972999)
        ·
          refine ⟨4898259122674585381459499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3265506081783056920972999 4898259122674585381459499)
          ·
            refine ⟨7347388684011878072189249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4898259122674585381459499 7347388684011878072189249)
            ·
              refine ⟨5510541513008908554141937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7347388684011878072189249 5510541513008908554141937)
              ·
                refine ⟨4132906134756681415606453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5510541513008908554141937 4132906134756681415606453)
                ·
                  refine ⟨387459950133438882713105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4132906134756681415606453 387459950133438882713105)
                  ·
                    rfl

theorem cell22_3395590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 2, 2, 5].length) (baseStart_3395590 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3395590 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3395590 prefixEnd_3395590 := by exact prefixLift 3395590
  have htrace : WordTrace (prefixWord ++ tailWord_3395590) baseStart_3395590 baseEnd_3395590 := by
    simpa [prefixWord, tailWord_3395590, baseEnd_3395590] using wordTrace_append hprefix tailTrace_3395590
  have hstable : (prefixWord ++ tailWord_3395590).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3395590).length < 2 ^ (prefixWord ++ tailWord_3395590).sum := by decide
  have hdescent : baseEnd_3395590 < baseStart_3395590 := by decide
  rcases family_descends (prefixWord ++ tailWord_3395590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3395612 : List Nat := [2, 2, 3, 1, 3, 1, 3, 7]
def baseStart_3395612 : Nat := 118140960795 + 3395612 * 2 ^ 59
def prefixEnd_3395612 : Nat := 4983230072969 + 3 ^ 40 * 3395612 * 2
def baseEnd_3395612 : Nat := 129154153494435102676583

theorem tailTrace_3395612 : CollatzResearch.WordTrace tailWord_3395612 prefixEnd_3395612 129154153494435102676583 := by
  unfold tailWord_3395612
  simp only [CollatzResearch.WordTrace]
  refine ⟨61924072087142561602286545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82565429449523415469715393 61924072087142561602286545)
  ·
    refine ⟨46443054065356921201714909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61924072087142561602286545 46443054065356921201714909)
    ·
      refine ⟨17416145274508845450643091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46443054065356921201714909 17416145274508845450643091)
      ·
        refine ⟨26124217911763268175964637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17416145274508845450643091 26124217911763268175964637)
        ·
          refine ⟨9796581716911225565986739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26124217911763268175964637 9796581716911225565986739)
          ·
            refine ⟨14694872575366838348980109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9796581716911225565986739 14694872575366838348980109)
            ·
              refine ⟨5510577215762564380867541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14694872575366838348980109 5510577215762564380867541)
              ·
                refine ⟨129154153494435102676583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5510577215762564380867541 129154153494435102676583)
                ·
                  rfl

theorem cell22_3395612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 3, 7].length) (baseStart_3395612 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3395612 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3395612 prefixEnd_3395612 := by exact prefixLift 3395612
  have htrace : WordTrace (prefixWord ++ tailWord_3395612) baseStart_3395612 baseEnd_3395612 := by
    simpa [prefixWord, tailWord_3395612, baseEnd_3395612] using wordTrace_append hprefix tailTrace_3395612
  have hstable : (prefixWord ++ tailWord_3395612).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3395612).length < 2 ^ (prefixWord ++ tailWord_3395612).sum := by decide
  have hdescent : baseEnd_3395612 < baseStart_3395612 := by decide
  rcases family_descends (prefixWord ++ tailWord_3395612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3395661 : List Nat := [1, 6, 1, 1, 1, 1, 4, 1, 3, 3]
def baseStart_3395661 : Nat := 118140960795 + 3395661 * 2 ^ 59
def prefixEnd_3395661 : Nat := 4983230072969 + 3 ^ 40 * 3395661 * 2
def baseEnd_3395661 : Nat := 1162404155151296129614097

theorem tailTrace_3395661 : CollatzResearch.WordTrace tailWord_3395661 prefixEnd_3395661 1162404155151296129614097 := by
  unfold tailWord_3395661
  simp only [CollatzResearch.WordTrace]
  refine ⟨123849931351107604573106837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82566620900738403048737891 123849931351107604573106837)
  ·
    refine ⟨5805465532083168964364383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 123849931351107604573106837 5805465532083168964364383)
    ·
      refine ⟨8708198298124753446546575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5805465532083168964364383 8708198298124753446546575)
      ·
        refine ⟨13062297447187130169819863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8708198298124753446546575 13062297447187130169819863)
        ·
          refine ⟨19593446170780695254729795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13062297447187130169819863 19593446170780695254729795)
          ·
            refine ⟨29390169256171042882094693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19593446170780695254729795 29390169256171042882094693)
            ·
              refine ⟨5510656735532070540392755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29390169256171042882094693 5510656735532070540392755)
              ·
                refine ⟨8265985103298105810589133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5510656735532070540392755 8265985103298105810589133)
                ·
                  refine ⟨3099744413736789678970925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8265985103298105810589133 3099744413736789678970925)
                  ·
                    refine ⟨1162404155151296129614097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3099744413736789678970925 1162404155151296129614097)
                    ·
                      rfl

theorem cell22_3395661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 4, 1, 3, 3].length) (baseStart_3395661 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3395661 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3395661 prefixEnd_3395661 := by exact prefixLift 3395661
  have htrace : WordTrace (prefixWord ++ tailWord_3395661) baseStart_3395661 baseEnd_3395661 := by
    simpa [prefixWord, tailWord_3395661, baseEnd_3395661] using wordTrace_append hprefix tailTrace_3395661
  have hstable : (prefixWord ++ tailWord_3395661).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3395661).length < 2 ^ (prefixWord ++ tailWord_3395661).sum := by decide
  have hdescent : baseEnd_3395661 < baseStart_3395661 := by decide
  rcases family_descends (prefixWord ++ tailWord_3395661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3395672 : List Nat := [2, 1, 2, 2, 1, 4, 2, 1, 2, 5]
def baseStart_3395672 : Nat := 118140960795 + 3395672 * 2 ^ 59
def prefixEnd_3395672 : Nat := 4983230072969 + 3 ^ 40 * 3395672 * 2
def baseEnd_3395672 : Nat := 1162407920676095767589063

theorem tailTrace_3395672 : CollatzResearch.WordTrace tailWord_3395672 prefixEnd_3395672 1162407920676095767589063 := by
  unfold tailWord_3395672
  simp only [CollatzResearch.WordTrace]
  refine ⟨61925166277033876725878635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82566888369378502301171513 61925166277033876725878635)
  ·
    refine ⟨92887749415550815088817953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61925166277033876725878635 92887749415550815088817953)
    ·
      refine ⟨69665812061663111316613465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92887749415550815088817953 69665812061663111316613465)
      ·
        refine ⟨52249359046247333487460099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69665812061663111316613465 52249359046247333487460099)
        ·
          refine ⟨78374038569371000231190149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52249359046247333487460099 78374038569371000231190149)
          ·
            refine ⟨14695132231757062543348153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 78374038569371000231190149 14695132231757062543348153)
            ·
              refine ⟨11021349173817796907511115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14695132231757062543348153 11021349173817796907511115)
              ·
                refine ⟨16532023760726695361266673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11021349173817796907511115 16532023760726695361266673)
                ·
                  refine ⟨12399017820545021520950005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16532023760726695361266673 12399017820545021520950005)
                  ·
                    refine ⟨1162407920676095767589063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12399017820545021520950005 1162407920676095767589063)
                    ·
                      rfl

theorem cell22_3395672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 2, 1, 2, 5].length) (baseStart_3395672 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3395672 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3395672 prefixEnd_3395672 := by exact prefixLift 3395672
  have htrace : WordTrace (prefixWord ++ tailWord_3395672) baseStart_3395672 baseEnd_3395672 := by
    simpa [prefixWord, tailWord_3395672, baseEnd_3395672] using wordTrace_append hprefix tailTrace_3395672
  have hstable : (prefixWord ++ tailWord_3395672).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3395672).length < 2 ^ (prefixWord ++ tailWord_3395672).sum := by decide
  have hdescent : baseEnd_3395672 < baseStart_3395672 := by decide
  rcases family_descends (prefixWord ++ tailWord_3395672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3395674 : List Nat := [3, 1, 1, 2, 1, 1, 7, 1, 5]
def baseStart_3395674 : Nat := 118140960795 + 3395674 * 2 ^ 59
def prefixEnd_3395674 : Nat := 4983230072969 + 3 ^ 40 * 3395674 * 2
def baseEnd_3395674 : Nat := 387469535105656143013019

theorem tailTrace_3395674 : CollatzResearch.WordTrace tailWord_3395674 prefixEnd_3395674 387469535105656143013019 := by
  unfold tailWord_3395674
  simp only [CollatzResearch.WordTrace]
  refine ⟨30962601375015126948332519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82566937000040338528886717 30962601375015126948332519)
  ·
    refine ⟨46443902062522690422498779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30962601375015126948332519 46443902062522690422498779)
    ·
      refine ⟨69665853093784035633748169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46443902062522690422498779 69665853093784035633748169)
      ·
        refine ⟨52249389820338026725311127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69665853093784035633748169 52249389820338026725311127)
        ·
          refine ⟨78374084730507040087966691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52249389820338026725311127 78374084730507040087966691)
          ·
            refine ⟨117561127095760560131950037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78374084730507040087966691 117561127095760560131950037)
            ·
              refine ⟨2755338916306888128092579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 117561127095760560131950037 2755338916306888128092579)
              ·
                refine ⟨4133008374460332192138869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2755338916306888128092579 4133008374460332192138869)
                ·
                  refine ⟨387469535105656143013019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4133008374460332192138869 387469535105656143013019)
                  ·
                    rfl

theorem cell22_3395674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 7, 1, 5].length) (baseStart_3395674 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3395674 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3395674 prefixEnd_3395674 := by exact prefixLift 3395674
  have htrace : WordTrace (prefixWord ++ tailWord_3395674) baseStart_3395674 baseEnd_3395674 := by
    simpa [prefixWord, tailWord_3395674, baseEnd_3395674] using wordTrace_append hprefix tailTrace_3395674
  have hstable : (prefixWord ++ tailWord_3395674).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3395674).length < 2 ^ (prefixWord ++ tailWord_3395674).sum := by decide
  have hdescent : baseEnd_3395674 < baseStart_3395674 := by decide
  rcases family_descends (prefixWord ++ tailWord_3395674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3395719 : List Nat := [1, 1, 4, 2, 1, 1, 2, 6, 4]
def baseStart_3395719 : Nat := 118140960795 + 3395719 * 2 ^ 59
def prefixEnd_3395719 : Nat := 4983230072969 + 3 ^ 40 * 3395719 * 2
def baseEnd_3395719 : Nat := 387474669912201103887973

theorem tailTrace_3395719 : CollatzResearch.WordTrace tailWord_3395719 prefixEnd_3395719 387474669912201103887973 := by
  unfold tailWord_3395719
  simp only [CollatzResearch.WordTrace]
  refine ⟨123852046784897480478718211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82568031189931653652478807 123852046784897480478718211)
  ·
    refine ⟨185778070177346220718077317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123852046784897480478718211 185778070177346220718077317)
    ·
      refine ⟨34833388158252416384639497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 185778070177346220718077317 34833388158252416384639497)
      ·
        refine ⟨26125041118689312288479623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34833388158252416384639497 26125041118689312288479623)
        ·
          refine ⟨39187561678033968432719435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26125041118689312288479623 39187561678033968432719435)
          ·
            refine ⟨58781342517050952649079153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39187561678033968432719435 58781342517050952649079153)
            ·
              refine ⟨44086006887788214486809365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58781342517050952649079153 44086006887788214486809365)
              ·
                refine ⟨2066531572865072554069189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 44086006887788214486809365 2066531572865072554069189)
                ·
                  refine ⟨387474669912201103887973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2066531572865072554069189 387474669912201103887973)
                  ·
                    rfl

theorem cell22_3395719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 6, 4].length) (baseStart_3395719 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3395719 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3395719 prefixEnd_3395719 := by exact prefixLift 3395719
  have htrace : WordTrace (prefixWord ++ tailWord_3395719) baseStart_3395719 baseEnd_3395719 := by
    simpa [prefixWord, tailWord_3395719, baseEnd_3395719] using wordTrace_append hprefix tailTrace_3395719
  have hstable : (prefixWord ++ tailWord_3395719).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3395719).length < 2 ^ (prefixWord ++ tailWord_3395719).sum := by decide
  have hdescent : baseEnd_3395719 < baseStart_3395719 := by decide
  rcases family_descends (prefixWord ++ tailWord_3395719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3395738 : List Nat := [3, 1, 1, 5, 2, 2, 1, 2, 1, 4]
def baseStart_3395738 : Nat := 118140960795 + 3395738 * 2 ^ 59
def prefixEnd_3395738 : Nat := 4983230072969 + 3 ^ 40 * 3395738 * 2
def baseEnd_3395738 : Nat := 1162430513824893595438861

theorem tailTrace_3395738 : CollatzResearch.WordTrace tailWord_3395738 prefixEnd_3395738 1162430513824893595438861 := by
  unfold tailWord_3395738
  simp only [CollatzResearch.WordTrace]
  refine ⟨30963184942957161680914967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82568493181219097815773245 30963184942957161680914967)
  ·
    refine ⟨46444777414435742521372451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30963184942957161680914967 46444777414435742521372451)
    ·
      refine ⟨69667166121653613782058677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46444777414435742521372451 69667166121653613782058677)
      ·
        refine ⟨6531296823905026292068001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 69667166121653613782058677 6531296823905026292068001)
        ·
          refine ⟨4898472617928769719051001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6531296823905026292068001 4898472617928769719051001)
          ·
            refine ⟨3673854463446577289288251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4898472617928769719051001 3673854463446577289288251)
            ·
              refine ⟨5510781695169865933932377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3673854463446577289288251 5510781695169865933932377)
              ·
                refine ⟨4133086271377399450449283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5510781695169865933932377 4133086271377399450449283)
                ·
                  refine ⟨6199629407066099175673925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4133086271377399450449283 6199629407066099175673925)
                  ·
                    refine ⟨1162430513824893595438861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6199629407066099175673925 1162430513824893595438861)
                    ·
                      rfl

theorem cell22_3395738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 2, 1, 2, 1, 4].length) (baseStart_3395738 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3395738 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3395738 prefixEnd_3395738 := by exact prefixLift 3395738
  have htrace : WordTrace (prefixWord ++ tailWord_3395738) baseStart_3395738 baseEnd_3395738 := by
    simpa [prefixWord, tailWord_3395738, baseEnd_3395738] using wordTrace_append hprefix tailTrace_3395738
  have hstable : (prefixWord ++ tailWord_3395738).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3395738).length < 2 ^ (prefixWord ++ tailWord_3395738).sum := by decide
  have hdescent : baseEnd_3395738 < baseStart_3395738 := by decide
  rcases family_descends (prefixWord ++ tailWord_3395738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3395749 : List Nat := [1, 3, 1, 2, 1, 3, 4, 1, 2, 4]
def baseStart_3395749 : Nat := 118140960795 + 3395749 * 2 ^ 59
def prefixEnd_3395749 : Nat := 4983230072969 + 3 ^ 40 * 3395749 * 2
def baseEnd_3395749 : Nat := 1162434279349693233413827

theorem tailTrace_3395749 : CollatzResearch.WordTrace tailWord_3395749 prefixEnd_3395749 1162434279349693233413827 := by
  unfold tailWord_3395749
  simp only [CollatzResearch.WordTrace]
  refine ⟨123853140974788795602310301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82568760649859197068206867 123853140974788795602310301)
  ·
    refine ⟨46444927865545798350866363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123853140974788795602310301 46444927865545798350866363)
    ·
      refine ⟨69667391798318697526299545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46444927865545798350866363 69667391798318697526299545)
      ·
        refine ⟨52250543848739023144724659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69667391798318697526299545 52250543848739023144724659)
        ·
          refine ⟨78375815773108534717086989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52250543848739023144724659 78375815773108534717086989)
          ·
            refine ⟨29390930914915700518907621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78375815773108534717086989 29390930914915700518907621)
            ·
              refine ⟨5510799546546693847295179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29390930914915700518907621 5510799546546693847295179)
              ·
                refine ⟨8266199319820040770942769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5510799546546693847295179 8266199319820040770942769)
                ·
                  refine ⟨6199649489865030578207077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8266199319820040770942769 6199649489865030578207077)
                  ·
                    refine ⟨1162434279349693233413827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6199649489865030578207077 1162434279349693233413827)
                    ·
                      rfl

theorem cell22_3395749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 4, 1, 2, 4].length) (baseStart_3395749 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3395749 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3395749 prefixEnd_3395749 := by exact prefixLift 3395749
  have htrace : WordTrace (prefixWord ++ tailWord_3395749) baseStart_3395749 baseEnd_3395749 := by
    simpa [prefixWord, tailWord_3395749, baseEnd_3395749] using wordTrace_append hprefix tailTrace_3395749
  have hstable : (prefixWord ++ tailWord_3395749).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3395749).length < 2 ^ (prefixWord ++ tailWord_3395749).sum := by decide
  have hdescent : baseEnd_3395749 < baseStart_3395749 := by decide
  rcases family_descends (prefixWord ++ tailWord_3395749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3395751 : List Nat := [1, 1, 6, 2, 2, 1, 1, 2, 1, 5]
def baseStart_3395751 : Nat := 118140960795 + 3395751 * 2 ^ 59
def prefixEnd_3395751 : Nat := 4983230072969 + 3 ^ 40 * 3395751 * 2
def baseEnd_3395751 : Nat := 1162434963990565894863821

theorem tailTrace_3395751 : CollatzResearch.WordTrace tailWord_3395751 prefixEnd_3395751 1162434963990565894863821 := by
  unfold tailWord_3395751
  simp only [CollatzResearch.WordTrace]
  refine ⟨123853213920781549943883107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82568809280521033295922071 123853213920781549943883107)
  ·
    refine ⟨185779820881172324915824661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123853213920781549943883107 185779820881172324915824661)
    ·
      refine ⟨8708429103804952730429281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 185779820881172324915824661 8708429103804952730429281)
      ·
        refine ⟨6531321827853714547821961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8708429103804952730429281 6531321827853714547821961)
        ·
          refine ⟨4898491370890285910866471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6531321827853714547821961 4898491370890285910866471)
          ·
            refine ⟨7347737056335428866299707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4898491370890285910866471 7347737056335428866299707)
            ·
              refine ⟨11021605584503143299449561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7347737056335428866299707 11021605584503143299449561)
              ·
                refine ⟨8266204188377357474587171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11021605584503143299449561 8266204188377357474587171)
                ·
                  refine ⟨12399306282566036211880757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8266204188377357474587171 12399306282566036211880757)
                  ·
                    refine ⟨1162434963990565894863821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12399306282566036211880757 1162434963990565894863821)
                    ·
                      rfl

theorem cell22_3395751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 1, 2, 1, 5].length) (baseStart_3395751 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3395751 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3395751 prefixEnd_3395751 := by exact prefixLift 3395751
  have htrace : WordTrace (prefixWord ++ tailWord_3395751) baseStart_3395751 baseEnd_3395751 := by
    simpa [prefixWord, tailWord_3395751, baseEnd_3395751] using wordTrace_append hprefix tailTrace_3395751
  have hstable : (prefixWord ++ tailWord_3395751).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3395751).length < 2 ^ (prefixWord ++ tailWord_3395751).sum := by decide
  have hdescent : baseEnd_3395751 < baseStart_3395751 := by decide
  rcases family_descends (prefixWord ++ tailWord_3395751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3395798 : List Nat := [5, 2, 1, 2, 1, 2, 3, 6]
def baseStart_3395798 : Nat := 118140960795 + 3395798 * 2 ^ 59
def prefixEnd_3395798 : Nat := 4983230072969 + 3 ^ 40 * 3395798 * 2
def baseEnd_3395798 : Nat := 129161228116785937659853

theorem tailTrace_3395798 : CollatzResearch.WordTrace tailWord_3395798 prefixEnd_3395798 129161228116785937659853 := by
  unfold tailWord_3395798
  simp only [CollatzResearch.WordTrace]
  refine ⟨7740933009475704810677753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 82569952101074184647229365 7740933009475704810677753)
  ·
    refine ⟨5805699757106778608008315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7740933009475704810677753 5805699757106778608008315)
    ·
      refine ⟨8708549635660167912012473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5805699757106778608008315 8708549635660167912012473)
      ·
        refine ⟨6531412226745125934009355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8708549635660167912012473 6531412226745125934009355)
        ·
          refine ⟨9797118340117688901014033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6531412226745125934009355 9797118340117688901014033)
          ·
            refine ⟨7347838755088266675760525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9797118340117688901014033 7347838755088266675760525)
            ·
              refine ⟨2755439533158100003410197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7347838755088266675760525 2755439533158100003410197)
              ·
                refine ⟨129161228116785937659853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2755439533158100003410197 129161228116785937659853)
                ·
                  rfl

theorem cell22_3395798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 3, 6].length) (baseStart_3395798 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3395798 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3395798 prefixEnd_3395798 := by exact prefixLift 3395798
  have htrace : WordTrace (prefixWord ++ tailWord_3395798) baseStart_3395798 baseEnd_3395798 := by
    simpa [prefixWord, tailWord_3395798, baseEnd_3395798] using wordTrace_append hprefix tailTrace_3395798
  have hstable : (prefixWord ++ tailWord_3395798).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3395798).length < 2 ^ (prefixWord ++ tailWord_3395798).sum := by decide
  have hdescent : baseEnd_3395798 < baseStart_3395798 := by decide
  rcases family_descends (prefixWord ++ tailWord_3395798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3395807 : List Nat := [1, 1, 2, 3, 2, 1, 1, 1, 3, 7]
def baseStart_3395807 : Nat := 118140960795 + 3395807 * 2 ^ 59
def prefixEnd_3395807 : Nat := 4983230072969 + 3 ^ 40 * 3395807 * 2
def baseEnd_3395807 : Nat := 1162454133935000415463649

theorem tailTrace_3395807 : CollatzResearch.WordTrace tailWord_3395807 prefixEnd_3395807 1162454133935000415463649 := by
  unfold tailWord_3395807
  simp only [CollatzResearch.WordTrace]
  refine ⟨123855256408578671507921675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82570170939052447671947783 123855256408578671507921675)
  ·
    refine ⟨185782884612868007261882513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123855256408578671507921675 185782884612868007261882513)
    ·
      refine ⟨139337163459651005446411885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 185782884612868007261882513 139337163459651005446411885)
      ·
        refine ⟨52251436297369127042404457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 139337163459651005446411885 52251436297369127042404457)
        ·
          refine ⟨39188577223026845281803343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52251436297369127042404457 39188577223026845281803343)
          ·
            refine ⟨58782865834540267922705015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39188577223026845281803343 58782865834540267922705015)
            ·
              refine ⟨88174298751810401884057523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58782865834540267922705015 88174298751810401884057523)
              ·
                refine ⟨132261448127715602826086285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88174298751810401884057523 132261448127715602826086285)
                ·
                  refine ⟨49598043047893351059782357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 132261448127715602826086285 49598043047893351059782357)
                  ·
                    refine ⟨1162454133935000415463649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 49598043047893351059782357 1162454133935000415463649)
                    ·
                      rfl

theorem cell22_3395807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 1, 3, 7].length) (baseStart_3395807 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3395807 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3395807 prefixEnd_3395807 := by exact prefixLift 3395807
  have htrace : WordTrace (prefixWord ++ tailWord_3395807) baseStart_3395807 baseEnd_3395807 := by
    simpa [prefixWord, tailWord_3395807, baseEnd_3395807] using wordTrace_append hprefix tailTrace_3395807
  have hstable : (prefixWord ++ tailWord_3395807).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3395807).length < 2 ^ (prefixWord ++ tailWord_3395807).sum := by decide
  have hdescent : baseEnd_3395807 < baseStart_3395807 := by decide
  rcases family_descends (prefixWord ++ tailWord_3395807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3395813 : List Nat := [1, 3, 1, 4, 2, 1, 1, 5, 1, 3]
def baseStart_3395813 : Nat := 118140960795 + 3395813 * 2 ^ 59
def prefixEnd_3395813 : Nat := 4983230072969 + 3 ^ 40 * 3395813 * 2
def baseEnd_3395813 : Nat := 1162456187857618399813631

theorem tailTrace_3395813 : CollatzResearch.WordTrace tailWord_3395813 prefixEnd_3395813 1162456187857618399813631 := by
  unfold tailWord_3395813
  simp only [CollatzResearch.WordTrace]
  refine ⟨123855475246556934532640093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82570316831037956355093395 123855475246556934532640093)
  ·
    refine ⟨46445803217458850449740035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123855475246556934532640093 46445803217458850449740035)
    ·
      refine ⟨69668704826188275674610053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46445803217458850449740035 69668704826188275674610053)
      ·
        refine ⟨13062882154910301688989385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 69668704826188275674610053 13062882154910301688989385)
        ·
          refine ⟨9797161616182726266742039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13062882154910301688989385 9797161616182726266742039)
          ·
            refine ⟨14695742424274089400113059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9797161616182726266742039 14695742424274089400113059)
            ·
              refine ⟨22043613636411134100169589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14695742424274089400113059 22043613636411134100169589)
              ·
                refine ⟨2066588778413543821890899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22043613636411134100169589 2066588778413543821890899)
                ·
                  refine ⟨3099883167620315732836349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2066588778413543821890899 3099883167620315732836349)
                  ·
                    refine ⟨1162456187857618399813631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3099883167620315732836349 1162456187857618399813631)
                    ·
                      rfl

theorem cell22_3395813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 1, 5, 1, 3].length) (baseStart_3395813 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3395813 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3395813 prefixEnd_3395813 := by exact prefixLift 3395813
  have htrace : WordTrace (prefixWord ++ tailWord_3395813) baseStart_3395813 baseEnd_3395813 := by
    simpa [prefixWord, tailWord_3395813, baseEnd_3395813] using wordTrace_append hprefix tailTrace_3395813
  have hstable : (prefixWord ++ tailWord_3395813).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3395813).length < 2 ^ (prefixWord ++ tailWord_3395813).sum := by decide
  have hdescent : baseEnd_3395813 < baseStart_3395813 := by decide
  rcases family_descends (prefixWord ++ tailWord_3395813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3395826 : List Nat := [3, 2, 1, 3, 2, 1, 3, 2, 5]
def baseStart_3395826 : Nat := 118140960795 + 3395826 * 2 ^ 59
def prefixEnd_3395826 : Nat := 4983230072969 + 3 ^ 40 * 3395826 * 2
def baseEnd_3395826 : Nat := 387486879341096899746197

theorem tailTrace_3395826 : CollatzResearch.WordTrace tailWord_3395826 prefixEnd_3395826 387486879341096899746197 := by
  unfold tailWord_3395826
  simp only [CollatzResearch.WordTrace]
  refine ⟨30963987348877459438215833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82570632930339891835242221 30963987348877459438215833)
  ·
    refine ⟨23222990511658094578661875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30963987348877459438215833 23222990511658094578661875)
    ·
      refine ⟨34834485767487141867992813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23222990511658094578661875 34834485767487141867992813)
      ·
        refine ⟨13062932162807678200497305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34834485767487141867992813 13062932162807678200497305)
        ·
          refine ⟨9797199122105758650372979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13062932162807678200497305 9797199122105758650372979)
          ·
            refine ⟨14695798683158637975559469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9797199122105758650372979 14695798683158637975559469)
            ·
              refine ⟨5510924506184489240834801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14695798683158637975559469 5510924506184489240834801)
              ·
                refine ⟨4133193379638366930626101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5510924506184489240834801 4133193379638366930626101)
                ·
                  refine ⟨387486879341096899746197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4133193379638366930626101 387486879341096899746197)
                  ·
                    rfl

theorem cell22_3395826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 3, 2, 5].length) (baseStart_3395826 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3395826 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3395826 prefixEnd_3395826 := by exact prefixLift 3395826
  have htrace : WordTrace (prefixWord ++ tailWord_3395826) baseStart_3395826 baseEnd_3395826 := by
    simpa [prefixWord, tailWord_3395826, baseEnd_3395826] using wordTrace_append hprefix tailTrace_3395826
  have hstable : (prefixWord ++ tailWord_3395826).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3395826).length < 2 ^ (prefixWord ++ tailWord_3395826).sum := by decide
  have hdescent : baseEnd_3395826 < baseStart_3395826 := by decide
  rcases family_descends (prefixWord ++ tailWord_3395826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3395854 : List Nat := [4, 1, 1, 2, 1, 2, 1, 4, 6]
def baseStart_3395854 : Nat := 118140960795 + 3395854 * 2 ^ 59
def prefixEnd_3395854 : Nat := 4983230072969 + 3 ^ 40 * 3395854 * 2
def baseEnd_3395854 : Nat := 387490074331835986512835

theorem tailTrace_3395854 : CollatzResearch.WordTrace tailWord_3395854 prefixEnd_3395854 387490074331835986512835 := by
  unfold tailWord_3395854
  simp only [CollatzResearch.WordTrace]
  refine ⟨15482121329926049816860327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 82571313759605599023255077 15482121329926049816860327)
  ·
    refine ⟨23223181994889074725290491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15482121329926049816860327 23223181994889074725290491)
    ·
      refine ⟨34834772992333612087935737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23223181994889074725290491 34834772992333612087935737)
      ·
        refine ⟨26126079744250209065951803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34834772992333612087935737 26126079744250209065951803)
        ·
          refine ⟨39189119616375313598927705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26126079744250209065951803 39189119616375313598927705)
          ·
            refine ⟨29391839712281485199195779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39189119616375313598927705 29391839712281485199195779)
            ·
              refine ⟨44087759568422227798793669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29391839712281485199195779 44087759568422227798793669)
              ·
                refine ⟨8266454919079167712273813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44087759568422227798793669 8266454919079167712273813)
                ·
                  refine ⟨387490074331835986512835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8266454919079167712273813 387490074331835986512835)
                  ·
                    rfl

theorem cell22_3395854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 4, 6].length) (baseStart_3395854 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3395854 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3395854 prefixEnd_3395854 := by exact prefixLift 3395854
  have htrace : WordTrace (prefixWord ++ tailWord_3395854) baseStart_3395854 baseEnd_3395854 := by
    simpa [prefixWord, tailWord_3395854, baseEnd_3395854] using wordTrace_append hprefix tailTrace_3395854
  have hstable : (prefixWord ++ tailWord_3395854).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3395854).length < 2 ^ (prefixWord ++ tailWord_3395854).sum := by decide
  have hdescent : baseEnd_3395854 < baseStart_3395854 := by decide
  rcases family_descends (prefixWord ++ tailWord_3395854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3395884 : List Nat := [2, 2, 1, 1, 1, 3, 3, 1, 4, 4]
def baseStart_3395884 : Nat := 118140960795 + 3395884 * 2 ^ 59
def prefixEnd_3395884 : Nat := 4983230072969 + 3 ^ 40 * 3395884 * 2
def baseEnd_3395884 : Nat := 1162480492608597881288413

theorem tailTrace_3395884 : CollatzResearch.WordTrace tailWord_3395884 prefixEnd_3395884 1162480492608597881288413 := by
  unfold tailWord_3395884
  simp only [CollatzResearch.WordTrace]
  refine ⟨61929032414649856829237353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82572043219533142438983137 61929032414649856829237353)
  ·
    refine ⟨46446774310987392621928015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61929032414649856829237353 46446774310987392621928015)
    ·
      refine ⟨69670161466481088932892023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46446774310987392621928015 69670161466481088932892023)
      ·
        refine ⟨104505242199721633399338035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69670161466481088932892023 104505242199721633399338035)
        ·
          refine ⟨156757863299582450099007053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104505242199721633399338035 156757863299582450099007053)
          ·
            refine ⟨58784198737343418787127645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 156757863299582450099007053 58784198737343418787127645)
            ·
              refine ⟨22044074526503782045172867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58784198737343418787127645 22044074526503782045172867)
              ·
                refine ⟨33066111789755673067759301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22044074526503782045172867 33066111789755673067759301)
                ·
                  refine ⟨6199895960579188700204869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33066111789755673067759301 6199895960579188700204869)
                  ·
                    refine ⟨1162480492608597881288413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6199895960579188700204869 1162480492608597881288413)
                    ·
                      rfl

theorem cell22_3395884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 4].length) (baseStart_3395884 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3395884 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3395884 prefixEnd_3395884 := by exact prefixLift 3395884
  have htrace : WordTrace (prefixWord ++ tailWord_3395884) baseStart_3395884 baseEnd_3395884 := by
    simpa [prefixWord, tailWord_3395884, baseEnd_3395884] using wordTrace_append hprefix tailTrace_3395884
  have hstable : (prefixWord ++ tailWord_3395884).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3395884).length < 2 ^ (prefixWord ++ tailWord_3395884).sum := by decide
  have hdescent : baseEnd_3395884 < baseStart_3395884 := by decide
  rcases family_descends (prefixWord ++ tailWord_3395884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3395946 : List Nat := [3, 1, 3, 3, 1, 1, 1, 1, 2, 6]
def baseStart_3395946 : Nat := 118140960795 + 3395946 * 2 ^ 59
def prefixEnd_3395946 : Nat := 4983230072969 + 3 ^ 40 * 3395946 * 2
def baseEnd_3395946 : Nat := 1162501716475650386238223

theorem tailTrace_3395946 : CollatzResearch.WordTrace tailWord_3395946 prefixEnd_3395946 1162501716475650386238223 := by
  unfold tailWord_3395946
  simp only [CollatzResearch.WordTrace]
  refine ⟨30965081538768774561807923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82573550770050065498154461 30965081538768774561807923)
  ·
    refine ⟨46447622308153161842711885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30965081538768774561807923 46447622308153161842711885)
    ·
      refine ⟨17417858365557435691016957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46447622308153161842711885 17417858365557435691016957)
      ·
        refine ⟨6531696887084038384131359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17417858365557435691016957 6531696887084038384131359)
        ·
          refine ⟨9797545330626057576197039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6531696887084038384131359 9797545330626057576197039)
          ·
            refine ⟨14696317995939086364295559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9797545330626057576197039 14696317995939086364295559)
            ·
              refine ⟨22044476993908629546443339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14696317995939086364295559 22044476993908629546443339)
              ·
                refine ⟨33066715490862944319665009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22044476993908629546443339 33066715490862944319665009)
                ·
                  refine ⟨24800036618147208239748757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33066715490862944319665009 24800036618147208239748757)
                  ·
                    refine ⟨1162501716475650386238223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24800036618147208239748757 1162501716475650386238223)
                    ·
                      rfl

theorem cell22_3395946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 1, 1, 2, 6].length) (baseStart_3395946 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3395946 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3395946 prefixEnd_3395946 := by exact prefixLift 3395946
  have htrace : WordTrace (prefixWord ++ tailWord_3395946) baseStart_3395946 baseEnd_3395946 := by
    simpa [prefixWord, tailWord_3395946, baseEnd_3395946] using wordTrace_append hprefix tailTrace_3395946
  have hstable : (prefixWord ++ tailWord_3395946).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3395946).length < 2 ^ (prefixWord ++ tailWord_3395946).sum := by decide
  have hdescent : baseEnd_3395946 < baseStart_3395946 := by decide
  rcases family_descends (prefixWord ++ tailWord_3395946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3395982 : List Nat := [4, 1, 1, 4, 1, 2, 2, 3, 1, 3]
def baseStart_3395982 : Nat := 118140960795 + 3395982 * 2 ^ 59
def prefixEnd_3395982 : Nat := 4983230072969 + 3 ^ 40 * 3395982 * 2
def baseEnd_3395982 : Nat := 1162514040011358292338113

theorem tailTrace_3395982 : CollatzResearch.WordTrace tailWord_3395982 prefixEnd_3395982 1162514040011358292338113 := by
  unfold tailWord_3395982
  simp only [CollatzResearch.WordTrace]
  refine ⟨15482704897868084549442775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 82574426121963117597028133 15482704897868084549442775)
  ·
    refine ⟨23224057346802126824164163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15482704897868084549442775 23224057346802126824164163)
    ·
      refine ⟨34836086020203190236246245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23224057346802126824164163 34836086020203190236246245)
      ·
        refine ⟨6531766128788098169296171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34836086020203190236246245 6531766128788098169296171)
        ·
          refine ⟨9797649193182147253944257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6531766128788098169296171 9797649193182147253944257)
          ·
            refine ⟨7348236894886610440458193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9797649193182147253944257 7348236894886610440458193)
            ·
              refine ⟨5511177671164957830343645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7348236894886610440458193 5511177671164957830343645)
              ·
                refine ⟨2066691626686859186378867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5511177671164957830343645 2066691626686859186378867)
                ·
                  refine ⟨3100037440030288779568301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2066691626686859186378867 3100037440030288779568301)
                  ·
                    refine ⟨1162514040011358292338113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3100037440030288779568301 1162514040011358292338113)
                    ·
                      rfl

theorem cell22_3395982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 2, 3, 1, 3].length) (baseStart_3395982 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3395982 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3395982 prefixEnd_3395982 := by exact prefixLift 3395982
  have htrace : WordTrace (prefixWord ++ tailWord_3395982) baseStart_3395982 baseEnd_3395982 := by
    simpa [prefixWord, tailWord_3395982, baseEnd_3395982] using wordTrace_append hprefix tailTrace_3395982
  have hstable : (prefixWord ++ tailWord_3395982).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3395982).length < 2 ^ (prefixWord ++ tailWord_3395982).sum := by decide
  have hdescent : baseEnd_3395982 < baseStart_3395982 := by decide
  rcases family_descends (prefixWord ++ tailWord_3395982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3395989 : List Nat := [1, 3, 2, 1, 1, 2, 1, 1, 10]
def baseStart_3395989 : Nat := 118140960795 + 3395989 * 2 ^ 59
def prefixEnd_3395989 : Nat := 4983230072969 + 3 ^ 40 * 3395989 * 2
def baseEnd_3395989 : Nat := 387505478751470869137697

theorem tailTrace_3395989 : CollatzResearch.WordTrace tailWord_3395989 prefixEnd_3395989 387505478751470869137697 := by
  unfold tailWord_3395989
  simp only [CollatzResearch.WordTrace]
  refine ⟨123861894493919316591047021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82574596329279544394031347 123861894493919316591047021)
  ·
    refine ⟨46448210435219743721642633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123861894493919316591047021 46448210435219743721642633)
    ·
      refine ⟨34836157826414807791231975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46448210435219743721642633 34836157826414807791231975)
      ·
        refine ⟨52254236739622211686847963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34836157826414807791231975 52254236739622211686847963)
        ·
          refine ⟨78381355109433317530271945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52254236739622211686847963 78381355109433317530271945)
          ·
            refine ⟨58786016332074988147703959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78381355109433317530271945 58786016332074988147703959)
            ·
              refine ⟨88179024498112482221555939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58786016332074988147703959 88179024498112482221555939)
              ·
                refine ⟨132268536747168723332333909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88179024498112482221555939 132268536747168723332333909)
                ·
                  refine ⟨387505478751470869137697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 132268536747168723332333909 387505478751470869137697)
                  ·
                    rfl

theorem cell22_3395989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 1, 10].length) (baseStart_3395989 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3395989 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3395989 prefixEnd_3395989 := by exact prefixLift 3395989
  have htrace : WordTrace (prefixWord ++ tailWord_3395989) baseStart_3395989 baseEnd_3395989 := by
    simpa [prefixWord, tailWord_3395989, baseEnd_3395989] using wordTrace_append hprefix tailTrace_3395989
  have hstable : (prefixWord ++ tailWord_3395989).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3395989).length < 2 ^ (prefixWord ++ tailWord_3395989).sum := by decide
  have hdescent : baseEnd_3395989 < baseStart_3395989 := by decide
  rcases family_descends (prefixWord ++ tailWord_3395989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3396033 : List Nat := [1, 2, 7, 1, 2, 1, 1, 3, 1, 3]
def baseStart_3396033 : Nat := 118140960795 + 3396033 * 2 ^ 59
def prefixEnd_3396033 : Nat := 4983230072969 + 3 ^ 40 * 3396033 * 2
def baseEnd_3396033 : Nat := 1162531498353611159312957

theorem tailTrace_3396033 : CollatzResearch.WordTrace tailWord_3396033 prefixEnd_3396033 1162531498353611159312957 := by
  unfold tailWord_3396033
  simp only [CollatzResearch.WordTrace]
  refine ⟨123863499305759912105648753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82575666203839941403765835 123863499305759912105648753)
  ·
    refine ⟨92897624479319934079236565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123863499305759912105648753 92897624479319934079236565)
    ·
      refine ⟨2177288073734060954982107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 92897624479319934079236565 2177288073734060954982107)
      ·
        refine ⟨3265932110601091432473161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2177288073734060954982107 3265932110601091432473161)
        ·
          refine ⟨2449449082950818574354871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3265932110601091432473161 2449449082950818574354871)
          ·
            refine ⟨3674173624426227861532307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2449449082950818574354871 3674173624426227861532307)
            ·
              refine ⟨5511260436639341792298461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3674173624426227861532307 5511260436639341792298461)
              ·
                refine ⟨2066722663739753172111923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5511260436639341792298461 2066722663739753172111923)
                ·
                  refine ⟨3100083995609629758167885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2066722663739753172111923 3100083995609629758167885)
                  ·
                    refine ⟨1162531498353611159312957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3100083995609629758167885 1162531498353611159312957)
                    ·
                      rfl

theorem cell22_3396033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 2, 1, 1, 3, 1, 3].length) (baseStart_3396033 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3396033 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3396033 prefixEnd_3396033 := by exact prefixLift 3396033
  have htrace : WordTrace (prefixWord ++ tailWord_3396033) baseStart_3396033 baseEnd_3396033 := by
    simpa [prefixWord, tailWord_3396033, baseEnd_3396033] using wordTrace_append hprefix tailTrace_3396033
  have hstable : (prefixWord ++ tailWord_3396033).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3396033).length < 2 ^ (prefixWord ++ tailWord_3396033).sum := by decide
  have hdescent : baseEnd_3396033 < baseStart_3396033 := by decide
  rcases family_descends (prefixWord ++ tailWord_3396033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3396040 : List Nat := [2, 1, 3, 1, 3, 4, 1, 3, 4]
def baseStart_3396040 : Nat := 118140960795 + 3396040 * 2 ^ 59
def prefixEnd_3396040 : Nat := 4983230072969 + 3 ^ 40 * 3396040 * 2
def baseEnd_3396040 : Nat := 387511298198888491462645

theorem tailTrace_3396040 : CollatzResearch.WordTrace tailWord_3396040 prefixEnd_3396040 387511298198888491462645 := by
  unfold tailWord_3396040
  simp only [CollatzResearch.WordTrace]
  refine ⟨61931877308367276150576787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82575836411156368200769049 61931877308367276150576787)
  ·
    refine ⟨92897815962550914225865181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61931877308367276150576787 92897815962550914225865181)
    ·
      refine ⟨34836680985956592834699443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92897815962550914225865181 34836680985956592834699443)
      ·
        refine ⟨52255021478934889252049165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34836680985956592834699443 52255021478934889252049165)
        ·
          refine ⟨19595633054600583469518437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52255021478934889252049165 19595633054600583469518437)
          ·
            refine ⟨3674181197737609400534707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19595633054600583469518437 3674181197737609400534707)
            ·
              refine ⟨5511271796606414100802061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3674181197737609400534707 5511271796606414100802061)
              ·
                refine ⟨2066726923727405287800773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5511271796606414100802061 2066726923727405287800773)
                ·
                  refine ⟨387511298198888491462645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2066726923727405287800773 387511298198888491462645)
                  ·
                    rfl

theorem cell22_3396040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 4, 1, 3, 4].length) (baseStart_3396040 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3396040 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3396040 prefixEnd_3396040 := by exact prefixLift 3396040
  have htrace : WordTrace (prefixWord ++ tailWord_3396040) baseStart_3396040 baseEnd_3396040 := by
    simpa [prefixWord, tailWord_3396040, baseEnd_3396040] using wordTrace_append hprefix tailTrace_3396040
  have hstable : (prefixWord ++ tailWord_3396040).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3396040).length < 2 ^ (prefixWord ++ tailWord_3396040).sum := by decide
  have hdescent : baseEnd_3396040 < baseStart_3396040 := by decide
  rcases family_descends (prefixWord ++ tailWord_3396040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3396053 : List Nat := [1, 3, 2, 3, 1, 3, 1, 2, 2, 4]
def baseStart_3396053 : Nat := 118140960795 + 3396053 * 2 ^ 59
def prefixEnd_3396053 : Nat := 4983230072969 + 3 ^ 40 * 3396053 * 2
def baseEnd_3396053 : Nat := 1162538344762337773812895

theorem tailTrace_3396053 : CollatzResearch.WordTrace tailWord_3396053 prefixEnd_3396053 1162538344762337773812895 := by
  unfold tailWord_3396053
  simp only [CollatzResearch.WordTrace]
  refine ⟨123864228765687455521376813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82576152510458303680917875 123864228765687455521376813)
  ·
    refine ⟨46449085787132795820516305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123864228765687455521376813 46449085787132795820516305)
    ·
      refine ⟨34836814340349596865387229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46449085787132795820516305 34836814340349596865387229)
      ·
        refine ⟨13063805377631098824520211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34836814340349596865387229 13063805377631098824520211)
        ·
          refine ⟨19595708066446648236780317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13063805377631098824520211 19595708066446648236780317)
          ·
            refine ⟨7348390524917493088792619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19595708066446648236780317 7348390524917493088792619)
            ·
              refine ⟨11022585787376239633188929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7348390524917493088792619 11022585787376239633188929)
              ·
                refine ⟨8266939340532179724891697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11022585787376239633188929 8266939340532179724891697)
                ·
                  refine ⟨6200204505399134793668773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8266939340532179724891697 6200204505399134793668773)
                  ·
                    refine ⟨1162538344762337773812895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6200204505399134793668773 1162538344762337773812895)
                    ·
                      rfl

theorem cell22_3396053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 1, 2, 2, 4].length) (baseStart_3396053 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3396053 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3396053 prefixEnd_3396053 := by exact prefixLift 3396053
  have htrace : WordTrace (prefixWord ++ tailWord_3396053) baseStart_3396053 baseEnd_3396053 := by
    simpa [prefixWord, tailWord_3396053, baseEnd_3396053] using wordTrace_append hprefix tailTrace_3396053
  have hstable : (prefixWord ++ tailWord_3396053).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3396053).length < 2 ^ (prefixWord ++ tailWord_3396053).sum := by decide
  have hdescent : baseEnd_3396053 < baseStart_3396053 := by decide
  rcases family_descends (prefixWord ++ tailWord_3396053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3396072 : List Nat := [2, 1, 4, 1, 1, 5, 2, 1, 2, 3]
def baseStart_3396072 : Nat := 118140960795 + 3396072 * 2 ^ 59
def prefixEnd_3396072 : Nat := 4983230072969 + 3 ^ 40 * 3396072 * 2
def baseEnd_3396072 : Nat := 1162544848850628057587837

theorem tailTrace_3396072 : CollatzResearch.WordTrace tailWord_3396072 prefixEnd_3396072 1162544848850628057587837 := by
  unfold tailWord_3396072
  simp only [CollatzResearch.WordTrace]
  refine ⟨61932460876309310883159235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82576614501745747844212313 61932460876309310883159235)
  ·
    refine ⟨92898691314463966324738853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61932460876309310883159235 92898691314463966324738853)
    ·
      refine ⟨17418504621461993685888535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 92898691314463966324738853 17418504621461993685888535)
      ·
        refine ⟨26127756932192990528832803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17418504621461993685888535 26127756932192990528832803)
        ·
          refine ⟨39191635398289485793249205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26127756932192990528832803 39191635398289485793249205)
          ·
            refine ⟨3674215818589639293117113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 39191635398289485793249205 3674215818589639293117113)
            ·
              refine ⟨2755661863942229469837835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3674215818589639293117113 2755661863942229469837835)
              ·
                refine ⟨4133492795913344204756753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2755661863942229469837835 4133492795913344204756753)
                ·
                  refine ⟨3100119596935008153567565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4133492795913344204756753 3100119596935008153567565)
                  ·
                    refine ⟨1162544848850628057587837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3100119596935008153567565 1162544848850628057587837)
                    ·
                      rfl

theorem cell22_3396072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 5, 2, 1, 2, 3].length) (baseStart_3396072 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3396072 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3396072 prefixEnd_3396072 := by exact prefixLift 3396072
  have htrace : WordTrace (prefixWord ++ tailWord_3396072) baseStart_3396072 baseEnd_3396072 := by
    simpa [prefixWord, tailWord_3396072, baseEnd_3396072] using wordTrace_append hprefix tailTrace_3396072
  have hstable : (prefixWord ++ tailWord_3396072).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3396072).length < 2 ^ (prefixWord ++ tailWord_3396072).sum := by decide
  have hdescent : baseEnd_3396072 < baseStart_3396072 := by decide
  rcases family_descends (prefixWord ++ tailWord_3396072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3396160 : List Nat := [2, 1, 1, 2, 2, 2, 6, 1, 1, 4]
def baseStart_3396160 : Nat := 118140960795 + 3396160 * 2 ^ 59
def prefixEnd_3396160 : Nat := 4983230072969 + 3 ^ 40 * 3396160 * 2
def baseEnd_3396160 : Nat := 1162574973049025161387567

theorem tailTrace_3396160 : CollatzResearch.WordTrace tailWord_3396160 prefixEnd_3396160 1162574973049025161387567 := by
  unfold tailWord_3396160
  simp only [CollatzResearch.WordTrace]
  refine ⟨61934065688149906397760967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82578754250866541863681289 61934065688149906397760967)
  ·
    refine ⟨92901098532224859596641451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61934065688149906397760967 92901098532224859596641451)
    ·
      refine ⟨139351647798337289394962177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92901098532224859596641451 139351647798337289394962177)
      ·
        refine ⟨104513735848752967046221633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139351647798337289394962177 104513735848752967046221633)
        ·
          refine ⟨78385301886564725284666225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104513735848752967046221633 78385301886564725284666225)
          ·
            refine ⟨58788976414923543963499669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78385301886564725284666225 58788976414923543963499669)
            ·
              refine ⟨2755733269449541123289047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 58788976414923543963499669 2755733269449541123289047)
              ·
                refine ⟨4133599904174311684933571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2755733269449541123289047 4133599904174311684933571)
                ·
                  refine ⟨6200399856261467527400357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4133599904174311684933571 6200399856261467527400357)
                  ·
                    refine ⟨1162574973049025161387567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6200399856261467527400357 1162574973049025161387567)
                    ·
                      rfl

theorem cell22_3396160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 6, 1, 1, 4].length) (baseStart_3396160 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3396160 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3396160 prefixEnd_3396160 := by exact prefixLift 3396160
  have htrace : WordTrace (prefixWord ++ tailWord_3396160) baseStart_3396160 baseEnd_3396160 := by
    simpa [prefixWord, tailWord_3396160, baseEnd_3396160] using wordTrace_append hprefix tailTrace_3396160
  have hstable : (prefixWord ++ tailWord_3396160).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3396160).length < 2 ^ (prefixWord ++ tailWord_3396160).sum := by decide
  have hdescent : baseEnd_3396160 < baseStart_3396160 := by decide
  rcases family_descends (prefixWord ++ tailWord_3396160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3396194 : List Nat := [3, 3, 2, 3, 1, 1, 2, 2, 1, 4]
def baseStart_3396194 : Nat := 118140960795 + 3396194 * 2 ^ 59
def prefixEnd_3396194 : Nat := 4983230072969 + 3 ^ 40 * 3396194 * 2
def baseEnd_3396194 : Nat := 1162586611943860406037463

theorem tailTrace_3396194 : CollatzResearch.WordTrace tailWord_3396194 prefixEnd_3396194 1162586611943860406037463 := by
  unfold tailWord_3396194
  simp only [CollatzResearch.WordTrace]
  refine ⟨30967342864544159150564909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82579580972117757734839757 30967342864544159150564909)
  ·
    refine ⟨11612753574204059681461841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30967342864544159150564909 11612753574204059681461841)
    ·
      refine ⟨8709565180653044761096381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11612753574204059681461841 8709565180653044761096381)
      ·
        refine ⟨3266086942744891785411143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8709565180653044761096381 3266086942744891785411143)
        ·
          refine ⟨4899130414117337678116715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3266086942744891785411143 4899130414117337678116715)
          ·
            refine ⟨7348695621176006517175073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4899130414117337678116715 7348695621176006517175073)
            ·
              refine ⟨5511521715882004887881305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7348695621176006517175073 5511521715882004887881305)
              ·
                refine ⟨4133641286911503665910979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5511521715882004887881305 4133641286911503665910979)
                ·
                  refine ⟨6200461930367255498866469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4133641286911503665910979 6200461930367255498866469)
                  ·
                    refine ⟨1162586611943860406037463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6200461930367255498866469 1162586611943860406037463)
                    ·
                      rfl

theorem cell22_3396194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 2, 2, 1, 4].length) (baseStart_3396194 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3396194 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3396194 prefixEnd_3396194 := by exact prefixLift 3396194
  have htrace : WordTrace (prefixWord ++ tailWord_3396194) baseStart_3396194 baseEnd_3396194 := by
    simpa [prefixWord, tailWord_3396194, baseEnd_3396194] using wordTrace_append hprefix tailTrace_3396194
  have hstable : (prefixWord ++ tailWord_3396194).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3396194).length < 2 ^ (prefixWord ++ tailWord_3396194).sum := by decide
  have hdescent : baseEnd_3396194 < baseStart_3396194 := by decide
  rcases family_descends (prefixWord ++ tailWord_3396194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3396201 : List Nat := [1, 2, 1, 1, 1, 4, 1, 1, 1, 9]
def baseStart_3396201 : Nat := 118140960795 + 3396201 * 2 ^ 59
def prefixEnd_3396201 : Nat := 4983230072969 + 3 ^ 40 * 3396201 * 2
def baseEnd_3396201 : Nat := 1162589008186914721112441

theorem tailTrace_3396201 : CollatzResearch.WordTrace tailWord_3396201 prefixEnd_3396201 1162589008186914721112441 := by
  unfold tailWord_3396201
  simp only [CollatzResearch.WordTrace]
  refine ⟨123869626769151276797764457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82579751179434184531842971 123869626769151276797764457)
  ·
    refine ⟨92902220076863457598323343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123869626769151276797764457 92902220076863457598323343)
    ·
      refine ⟨139353330115295186397485015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92902220076863457598323343 139353330115295186397485015)
      ·
        refine ⟨209029995172942779596227523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139353330115295186397485015 209029995172942779596227523)
        ·
          refine ⟨313544992759414169394341285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 209029995172942779596227523 313544992759414169394341285)
          ·
            refine ⟨58789686142390156761438991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 313544992759414169394341285 58789686142390156761438991)
            ·
              refine ⟨88184529213585235142158487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58789686142390156761438991 88184529213585235142158487)
              ·
                refine ⟨132276793820377852713237731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88184529213585235142158487 132276793820377852713237731)
                ·
                  refine ⟨198415190730566779069856597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 132276793820377852713237731 198415190730566779069856597)
                  ·
                    refine ⟨1162589008186914721112441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 198415190730566779069856597 1162589008186914721112441)
                    ·
                      rfl

theorem cell22_3396201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 1, 1, 9].length) (baseStart_3396201 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3396201 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3396201 prefixEnd_3396201 := by exact prefixLift 3396201
  have htrace : WordTrace (prefixWord ++ tailWord_3396201) baseStart_3396201 baseEnd_3396201 := by
    simpa [prefixWord, tailWord_3396201, baseEnd_3396201] using wordTrace_append hprefix tailTrace_3396201
  have hstable : (prefixWord ++ tailWord_3396201).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3396201).length < 2 ^ (prefixWord ++ tailWord_3396201).sum := by decide
  have hdescent : baseEnd_3396201 < baseStart_3396201 := by decide
  rcases family_descends (prefixWord ++ tailWord_3396201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3396226 : List Nat := [3, 4, 3, 1, 1, 2, 1, 1, 6]
def baseStart_3396226 : Nat := 118140960795 + 3396226 * 2 ^ 59
def prefixEnd_3396226 : Nat := 4983230072969 + 3 ^ 40 * 3396226 * 2
def baseEnd_3396226 : Nat := 387532522065940996412455

theorem tailTrace_3396226 : CollatzResearch.WordTrace tailWord_3396226 prefixEnd_3396226 387532522065940996412455 := by
  unfold tailWord_3396226
  simp only [CollatzResearch.WordTrace]
  refine ⟨30967634648515176516856133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82580359062707137378283021 30967634648515176516856133)
  ·
    refine ⟨5806431496596595596910525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30967634648515176516856133 5806431496596595596910525)
    ·
      refine ⟨2177411811223723348841447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5806431496596595596910525 2177411811223723348841447)
      ·
        refine ⟨3266117716835585023262171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2177411811223723348841447 3266117716835585023262171)
        ·
          refine ⟨4899176575253377534893257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3266117716835585023262171 4899176575253377534893257)
          ·
            refine ⟨3674382431440033151169943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4899176575253377534893257 3674382431440033151169943)
            ·
              refine ⟨5511573647160049726754915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3674382431440033151169943 5511573647160049726754915)
              ·
                refine ⟨8267360470740074590132373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5511573647160049726754915 8267360470740074590132373)
                ·
                  refine ⟨387532522065940996412455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8267360470740074590132373 387532522065940996412455)
                  ·
                    rfl

theorem cell22_3396226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 2, 1, 1, 6].length) (baseStart_3396226 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3396226 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3396226 prefixEnd_3396226 := by exact prefixLift 3396226
  have htrace : WordTrace (prefixWord ++ tailWord_3396226) baseStart_3396226 baseEnd_3396226 := by
    simpa [prefixWord, tailWord_3396226, baseEnd_3396226] using wordTrace_append hprefix tailTrace_3396226
  have hstable : (prefixWord ++ tailWord_3396226).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3396226).length < 2 ^ (prefixWord ++ tailWord_3396226).sum := by decide
  have hdescent : baseEnd_3396226 < baseStart_3396226 := by decide
  rcases family_descends (prefixWord ++ tailWord_3396226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3396325 : List Nat := [1, 3, 1, 4, 1, 2, 2, 2, 1, 5]
def baseStart_3396325 : Nat := 118140960795 + 3396325 * 2 ^ 59
def prefixEnd_3396325 : Nat := 4983230072969 + 3 ^ 40 * 3396325 * 2
def baseEnd_3396325 : Nat := 1162631455921019731012061

theorem tailTrace_3396325 : CollatzResearch.WordTrace tailWord_3396325 prefixEnd_3396325 1162631455921019731012061 := by
  unfold tailWord_3396325
  simp only [CollatzResearch.WordTrace]
  refine ⟨123874149420702045975278429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82582766280468030650185619 123874149420702045975278429)
  ·
    refine ⟨46452806032763267240729411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123874149420702045975278429 46452806032763267240729411)
    ·
      refine ⟨69679209049144900861094117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46452806032763267240729411 69679209049144900861094117)
      ·
        refine ⟨13064851696714668911455147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 69679209049144900861094117 13064851696714668911455147)
        ·
          refine ⟨19597277545072003367182721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13064851696714668911455147 19597277545072003367182721)
          ·
            refine ⟨14697958158804002525387041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19597277545072003367182721 14697958158804002525387041)
            ·
              refine ⟨11023468619103001894040281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14697958158804002525387041 11023468619103001894040281)
              ·
                refine ⟨8267601464327251420530211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11023468619103001894040281 8267601464327251420530211)
                ·
                  refine ⟨12401402196490877130795317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8267601464327251420530211 12401402196490877130795317)
                  ·
                    refine ⟨1162631455921019731012061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12401402196490877130795317 1162631455921019731012061)
                    ·
                      rfl

theorem cell22_3396325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 2, 2, 1, 5].length) (baseStart_3396325 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3396325 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3396325 prefixEnd_3396325 := by exact prefixLift 3396325
  have htrace : WordTrace (prefixWord ++ tailWord_3396325) baseStart_3396325 baseEnd_3396325 := by
    simpa [prefixWord, tailWord_3396325, baseEnd_3396325] using wordTrace_append hprefix tailTrace_3396325
  have hstable : (prefixWord ++ tailWord_3396325).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3396325).length < 2 ^ (prefixWord ++ tailWord_3396325).sum := by decide
  have hdescent : baseEnd_3396325 < baseStart_3396325 := by decide
  rcases family_descends (prefixWord ++ tailWord_3396325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3396342 : List Nat := [5, 1, 1, 1, 1, 2, 3, 1, 4, 3]
def baseStart_3396342 : Nat := 118140960795 + 3396342 * 2 ^ 59
def prefixEnd_3396342 : Nat := 4983230072969 + 3 ^ 40 * 3396342 * 2
def baseEnd_3396342 : Nat := 1162637275368437353337009

theorem tailTrace_3396342 : CollatzResearch.WordTrace tailWord_3396342 prefixEnd_3396342 1162637275368437353337009 := by
  unfold tailWord_3396342
  simp only [CollatzResearch.WordTrace]
  refine ⟨7742173091352528617415455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 82583179641093638585764853 7742173091352528617415455)
  ·
    refine ⟨11613259637028792926123183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7742173091352528617415455 11613259637028792926123183)
    ·
      refine ⟨17419889455543189389184775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11613259637028792926123183 17419889455543189389184775)
      ·
        refine ⟨26129834183314784083777163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17419889455543189389184775 26129834183314784083777163)
        ·
          refine ⟨39194751274972176125665745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26129834183314784083777163 39194751274972176125665745)
          ·
            refine ⟨29396063456229132094249309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39194751274972176125665745 29396063456229132094249309)
            ·
              refine ⟨11023523796085924535343491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29396063456229132094249309 11023523796085924535343491)
              ·
                refine ⟨16535285694128886803015237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11023523796085924535343491 16535285694128886803015237)
                ·
                  refine ⟨3100366067649166275565357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16535285694128886803015237 3100366067649166275565357)
                  ·
                    refine ⟨1162637275368437353337009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3100366067649166275565357 1162637275368437353337009)
                    ·
                      rfl

theorem cell22_3396342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 3, 1, 4, 3].length) (baseStart_3396342 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3396342 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3396342 prefixEnd_3396342 := by exact prefixLift 3396342
  have htrace : WordTrace (prefixWord ++ tailWord_3396342) baseStart_3396342 baseEnd_3396342 := by
    simpa [prefixWord, tailWord_3396342, baseEnd_3396342] using wordTrace_append hprefix tailTrace_3396342
  have hstable : (prefixWord ++ tailWord_3396342).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3396342).length < 2 ^ (prefixWord ++ tailWord_3396342).sum := by decide
  have hdescent : baseEnd_3396342 < baseStart_3396342 := by decide
  rcases family_descends (prefixWord ++ tailWord_3396342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3396460 : List Nat := [2, 2, 1, 1, 4, 1, 1, 2, 3, 5]
def baseStart_3396460 : Nat := 118140960795 + 3396460 * 2 ^ 59
def prefixEnd_3396460 : Nat := 4983230072969 + 3 ^ 40 * 3396460 * 2
def baseEnd_3396460 : Nat := 1162677669179924378886647

theorem tailTrace_3396460 : CollatzResearch.WordTrace tailWord_3396460 prefixEnd_3396460 1162677669179924378886647 := by
  unfold tailWord_3396460
  simp only [CollatzResearch.WordTrace]
  refine ⟨61939536637606482015721417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82586048850141976020961889 61939536637606482015721417)
  ·
    refine ⟨46454652478204861511791063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61939536637606482015721417 46454652478204861511791063)
    ·
      refine ⟨69681978717307292267686595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46454652478204861511791063 69681978717307292267686595)
      ·
        refine ⟨104522968075960938401529893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69681978717307292267686595 104522968075960938401529893)
        ·
          refine ⟨19598056514242675950286855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 104522968075960938401529893 19598056514242675950286855)
          ·
            refine ⟨29397084771364013925430283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19598056514242675950286855 29397084771364013925430283)
            ·
              refine ⟨44095627157046020888145425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29397084771364013925430283 44095627157046020888145425)
              ·
                refine ⟨33071720367784515666109069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44095627157046020888145425 33071720367784515666109069)
                ·
                  refine ⟨12401895137919193374790901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33071720367784515666109069 12401895137919193374790901)
                  ·
                    refine ⟨1162677669179924378886647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12401895137919193374790901 1162677669179924378886647)
                    ·
                      rfl

theorem cell22_3396460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 5].length) (baseStart_3396460 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3396460 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3396460 prefixEnd_3396460 := by exact prefixLift 3396460
  have htrace : WordTrace (prefixWord ++ tailWord_3396460) baseStart_3396460 baseEnd_3396460 := by
    simpa [prefixWord, tailWord_3396460, baseEnd_3396460] using wordTrace_append hprefix tailTrace_3396460
  have hstable : (prefixWord ++ tailWord_3396460).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3396460).length < 2 ^ (prefixWord ++ tailWord_3396460).sum := by decide
  have hdescent : baseEnd_3396460 < baseStart_3396460 := by decide
  rcases family_descends (prefixWord ++ tailWord_3396460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3396475 : List Nat := [1, 1, 1, 1, 1, 5, 2, 2, 4, 4]
def baseStart_3396475 : Nat := 118140960795 + 3396475 * 2 ^ 59
def prefixEnd_3396475 : Nat := 4983230072969 + 3 ^ 40 * 3396475 * 2
def baseEnd_3396475 : Nat := 1162682803986469339761601

theorem tailTrace_3396475 : CollatzResearch.WordTrace tailWord_3396475 prefixEnd_3396475 1162682803986469339761601 := by
  unfold tailWord_3396475
  simp only [CollatzResearch.WordTrace]
  refine ⟨123879620370158621593238879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82586413580105747728825919 123879620370158621593238879)
  ·
    refine ⟨185819430555237932389858319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123879620370158621593238879 185819430555237932389858319)
    ·
      refine ⟨278729145832856898584787479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185819430555237932389858319 278729145832856898584787479)
      ·
        refine ⟨418093718749285347877181219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 278729145832856898584787479 418093718749285347877181219)
        ·
          refine ⟨627140578123928021815771829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 418093718749285347877181219 627140578123928021815771829)
          ·
            refine ⟨58794429199118252045228609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 627140578123928021815771829 58794429199118252045228609)
            ·
              refine ⟨44095821899338689033921457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58794429199118252045228609 44095821899338689033921457)
              ·
                refine ⟨33071866424504016775441093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44095821899338689033921457 33071866424504016775441093)
                ·
                  refine ⟨6200974954594503145395205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33071866424504016775441093 6200974954594503145395205)
                  ·
                    refine ⟨1162682803986469339761601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6200974954594503145395205 1162682803986469339761601)
                    ·
                      rfl

theorem cell22_3396475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 2, 4, 4].length) (baseStart_3396475 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3396475 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3396475 prefixEnd_3396475 := by exact prefixLift 3396475
  have htrace : WordTrace (prefixWord ++ tailWord_3396475) baseStart_3396475 baseEnd_3396475 := by
    simpa [prefixWord, tailWord_3396475, baseEnd_3396475] using wordTrace_append hprefix tailTrace_3396475
  have hstable : (prefixWord ++ tailWord_3396475).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3396475).length < 2 ^ (prefixWord ++ tailWord_3396475).sum := by decide
  have hdescent : baseEnd_3396475 < baseStart_3396475 := by decide
  rcases family_descends (prefixWord ++ tailWord_3396475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3396492 : List Nat := [2, 2, 1, 2, 1, 2, 5, 1, 2, 4]
def baseStart_3396492 : Nat := 118140960795 + 3396492 * 2 ^ 59
def prefixEnd_3396492 : Nat := 4983230072969 + 3 ^ 40 * 3396492 * 2
def baseEnd_3396492 : Nat := 1162688623433886962086549

theorem tailTrace_3396492 : CollatzResearch.WordTrace tailWord_3396492 prefixEnd_3396492 1162688623433886962086549 := by
  unfold tailWord_3396492
  simp only [CollatzResearch.WordTrace]
  refine ⟨61940120205548516748303865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82586826940731355664405153 61940120205548516748303865)
  ·
    refine ⟨46455090154161387561227899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61940120205548516748303865 46455090154161387561227899)
    ·
      refine ⟨69682635231242081341841849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46455090154161387561227899 69682635231242081341841849)
      ·
        refine ⟨52261976423431561006381387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69682635231242081341841849 52261976423431561006381387)
        ·
          refine ⟨78392964635147341509572081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52261976423431561006381387 78392964635147341509572081)
          ·
            refine ⟨58794723476360506132179061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78392964635147341509572081 58794723476360506132179061)
            ·
              refine ⟨5512005325908797449891787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 58794723476360506132179061 5512005325908797449891787)
              ·
                refine ⟨8268007988863196174837681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5512005325908797449891787 8268007988863196174837681)
                ·
                  refine ⟨6201005991647397131128261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8268007988863196174837681 6201005991647397131128261)
                  ·
                    refine ⟨1162688623433886962086549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6201005991647397131128261 1162688623433886962086549)
                    ·
                      rfl

theorem cell22_3396492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 5, 1, 2, 4].length) (baseStart_3396492 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3396492 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3396492 prefixEnd_3396492 := by exact prefixLift 3396492
  have htrace : WordTrace (prefixWord ++ tailWord_3396492) baseStart_3396492 baseEnd_3396492 := by
    simpa [prefixWord, tailWord_3396492, baseEnd_3396492] using wordTrace_append hprefix tailTrace_3396492
  have hstable : (prefixWord ++ tailWord_3396492).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3396492).length < 2 ^ (prefixWord ++ tailWord_3396492).sum := by decide
  have hdescent : baseEnd_3396492 < baseStart_3396492 := by decide
  rcases family_descends (prefixWord ++ tailWord_3396492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3396498 : List Nat := [3, 2, 3, 2, 2, 2, 2, 1, 1, 4]
def baseStart_3396498 : Nat := 118140960795 + 3396498 * 2 ^ 59
def prefixEnd_3396498 : Nat := 4983230072969 + 3 ^ 40 * 3396498 * 2
def baseEnd_3396498 : Nat := 1162690677356504946436531

theorem tailTrace_3396498 : CollatzResearch.WordTrace tailWord_3396498 prefixEnd_3396498 1162690677356504946436531 := by
  unfold tailWord_3396498
  simp only [CollatzResearch.WordTrace]
  refine ⟨30970114812268824130331537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82586972832716864347550765 30970114812268824130331537)
  ·
    refine ⟨23227586109201618097748653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30970114812268824130331537 23227586109201618097748653)
    ·
      refine ⟨8710344790950606786655745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23227586109201618097748653 8710344790950606786655745)
      ·
        refine ⟨6532758593212955089991809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8710344790950606786655745 6532758593212955089991809)
        ·
          refine ⟨4899568944909716317493857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6532758593212955089991809 4899568944909716317493857)
          ·
            refine ⟨3674676708682287238120393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4899568944909716317493857 3674676708682287238120393)
            ·
              refine ⟨2756007531511715428590295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3674676708682287238120393 2756007531511715428590295)
              ·
                refine ⟨4134011297267573142885443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2756007531511715428590295 4134011297267573142885443)
                ·
                  refine ⟨6201016945901359714328165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4134011297267573142885443 6201016945901359714328165)
                  ·
                    refine ⟨1162690677356504946436531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6201016945901359714328165 1162690677356504946436531)
                    ·
                      rfl

theorem cell22_3396498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 2, 2, 1, 1, 4].length) (baseStart_3396498 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3396498 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3396498 prefixEnd_3396498 := by exact prefixLift 3396498
  have htrace : WordTrace (prefixWord ++ tailWord_3396498) baseStart_3396498 baseEnd_3396498 := by
    simpa [prefixWord, tailWord_3396498, baseEnd_3396498] using wordTrace_append hprefix tailTrace_3396498
  have hstable : (prefixWord ++ tailWord_3396498).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3396498).length < 2 ^ (prefixWord ++ tailWord_3396498).sum := by decide
  have hdescent : baseEnd_3396498 < baseStart_3396498 := by decide
  rcases family_descends (prefixWord ++ tailWord_3396498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3396511 : List Nat := [1, 1, 2, 5, 2, 3, 1, 2, 2, 3]
def baseStart_3396511 : Nat := 118140960795 + 3396511 * 2 ^ 59
def prefixEnd_3396511 : Nat := 4983230072969 + 3 ^ 40 * 3396511 * 2
def baseEnd_3396511 : Nat := 1162695127522177245861491

theorem tailTrace_3396511 : CollatzResearch.WordTrace tailWord_3396511 prefixEnd_3396511 1162695127522177245861491 := by
  unfold tailWord_3396511
  simp only [CollatzResearch.WordTrace]
  refine ⟨123880933398028199741549387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82587288932018799827699591 123880933398028199741549387)
  ·
    refine ⟨185821400097042299612324081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123880933398028199741549387 185821400097042299612324081)
    ·
      refine ⟨139366050072781724709243061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 185821400097042299612324081 139366050072781724709243061)
      ·
        refine ⟨13065567194323286691491537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 139366050072781724709243061 13065567194323286691491537)
        ·
          refine ⟨9799175395742465018618653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13065567194323286691491537 9799175395742465018618653)
          ·
            refine ⟨3674690773403424381981995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9799175395742465018618653 3674690773403424381981995)
            ·
              refine ⟨5512036160105136572972993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3674690773403424381981995 5512036160105136572972993)
              ·
                refine ⟨4134027120078852429729745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5512036160105136572972993 4134027120078852429729745)
                ·
                  refine ⟨3100520340059139322297309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4134027120078852429729745 3100520340059139322297309)
                  ·
                    refine ⟨1162695127522177245861491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3100520340059139322297309 1162695127522177245861491)
                    ·
                      rfl

theorem cell22_3396511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 3, 1, 2, 2, 3].length) (baseStart_3396511 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3396511 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3396511 prefixEnd_3396511 := by exact prefixLift 3396511
  have htrace : WordTrace (prefixWord ++ tailWord_3396511) baseStart_3396511 baseEnd_3396511 := by
    simpa [prefixWord, tailWord_3396511, baseEnd_3396511] using wordTrace_append hprefix tailTrace_3396511
  have hstable : (prefixWord ++ tailWord_3396511).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3396511).length < 2 ^ (prefixWord ++ tailWord_3396511).sum := by decide
  have hdescent : baseEnd_3396511 < baseStart_3396511 := by decide
  rcases family_descends (prefixWord ++ tailWord_3396511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3396541 : List Nat := [1, 4, 1, 2, 5, 1, 2, 6]
def baseStart_3396541 : Nat := 118140960795 + 3396541 * 2 ^ 59
def prefixEnd_3396541 : Nat := 4983230072969 + 3 ^ 40 * 3396541 * 2
def baseEnd_3396541 : Nat := 129189488570585240845711

theorem tailTrace_3396541 : CollatzResearch.WordTrace tailWord_3396541 prefixEnd_3396541 129189488570585240845711 := by
  unfold tailWord_3396541
  simp only [CollatzResearch.WordTrace]
  refine ⟨123882027587919514865141477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82588018391946343243427651 123882027587919514865141477)
  ·
    refine ⟨23227880172734909037214027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 123882027587919514865141477 23227880172734909037214027)
    ·
      refine ⟨34841820259102363555821041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23227880172734909037214027 34841820259102363555821041)
      ·
        refine ⟨26131365194326772666865781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34841820259102363555821041 26131365194326772666865781)
        ·
          refine ⟨2449815486968134937518667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 26131365194326772666865781 2449815486968134937518667)
          ·
            refine ⟨3674723230452202406278001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2449815486968134937518667 3674723230452202406278001)
            ·
              refine ⟨2756042422839151804708501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3674723230452202406278001 2756042422839151804708501)
              ·
                refine ⟨129189488570585240845711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2756042422839151804708501 129189488570585240845711)
                ·
                  rfl

theorem cell22_3396541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 5, 1, 2, 6].length) (baseStart_3396541 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3396541 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3396541 prefixEnd_3396541 := by exact prefixLift 3396541
  have htrace : WordTrace (prefixWord ++ tailWord_3396541) baseStart_3396541 baseEnd_3396541 := by
    simpa [prefixWord, tailWord_3396541, baseEnd_3396541] using wordTrace_append hprefix tailTrace_3396541
  have hstable : (prefixWord ++ tailWord_3396541).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3396541).length < 2 ^ (prefixWord ++ tailWord_3396541).sum := by decide
  have hdescent : baseEnd_3396541 < baseStart_3396541 := by decide
  rcases family_descends (prefixWord ++ tailWord_3396541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3396586 : List Nat := [3, 1, 3, 1, 2, 4, 2, 1, 5]
def baseStart_3396586 : Nat := 118140960795 + 3396586 * 2 ^ 59
def prefixEnd_3396586 : Nat := 4983230072969 + 3 ^ 40 * 3396586 * 2
def baseEnd_3396586 : Nat := 387573600518300683412087

theorem tailTrace_3396586 : CollatzResearch.WordTrace tailWord_3396586 prefixEnd_3396586 387573600518300683412087 := by
  unfold tailWord_3396586
  simp only [CollatzResearch.WordTrace]
  refine ⟨30970917218189121887632403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82589112581837658367019741 30970917218189121887632403)
  ·
    refine ⟨46456375827283682831448605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30970917218189121887632403 46456375827283682831448605)
    ·
      refine ⟨17421140935231381061793227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46456375827283682831448605 17421140935231381061793227)
      ·
        refine ⟨26131711402847071592689841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17421140935231381061793227 26131711402847071592689841)
        ·
          refine ⟨19598783552135303694517381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26131711402847071592689841 19598783552135303694517381)
          ·
            refine ⟨3674771916025369442722009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19598783552135303694517381 3674771916025369442722009)
            ·
              refine ⟨2756078937019027082041507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3674771916025369442722009 2756078937019027082041507)
              ·
                refine ⟨4134118405528540623062261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2756078937019027082041507 4134118405528540623062261)
                ·
                  refine ⟨387573600518300683412087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4134118405528540623062261 387573600518300683412087)
                  ·
                    rfl

theorem cell22_3396586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 4, 2, 1, 5].length) (baseStart_3396586 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3396586 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3396586 prefixEnd_3396586 := by exact prefixLift 3396586
  have htrace : WordTrace (prefixWord ++ tailWord_3396586) baseStart_3396586 baseEnd_3396586 := by
    simpa [prefixWord, tailWord_3396586, baseEnd_3396586] using wordTrace_append hprefix tailTrace_3396586
  have hstable : (prefixWord ++ tailWord_3396586).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3396586).length < 2 ^ (prefixWord ++ tailWord_3396586).sum := by decide
  have hdescent : baseEnd_3396586 < baseStart_3396586 := by decide
  rcases family_descends (prefixWord ++ tailWord_3396586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3396616 : List Nat := [2, 1, 3, 2, 1, 4, 3, 1, 1, 4]
def baseStart_3396616 : Nat := 118140960795 + 3396616 * 2 ^ 59
def prefixEnd_3396616 : Nat := 4983230072969 + 3 ^ 40 * 3396616 * 2
def baseEnd_3396616 : Nat := 1162731071167991971986169

theorem tailTrace_3396616 : CollatzResearch.WordTrace tailWord_3396616 prefixEnd_3396616 1162731071167991971986169 := by
  unfold tailWord_3396616
  simp only [CollatzResearch.WordTrace]
  refine ⟨61942381531323901337060851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82589842041765201782747801 61942381531323901337060851)
  ·
    refine ⟨92913572296985852005591277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61942381531323901337060851 92913572296985852005591277)
    ·
      refine ⟨34842589611369694502096729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92913572296985852005591277 34842589611369694502096729)
      ·
        refine ⟨26131942208527270876572547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34842589611369694502096729 26131942208527270876572547)
        ·
          refine ⟨39197913312790906314858821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26131942208527270876572547 39197913312790906314858821)
          ·
            refine ⟨7349608746148294934036029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39197913312790906314858821 7349608746148294934036029)
            ·
              refine ⟨2756103279805610600263511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7349608746148294934036029 2756103279805610600263511)
              ·
                refine ⟨4134154919708415900395267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2756103279805610600263511 4134154919708415900395267)
                ·
                  refine ⟨6201232379562623850592901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4134154919708415900395267 6201232379562623850592901)
                  ·
                    refine ⟨1162731071167991971986169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6201232379562623850592901 1162731071167991971986169)
                    ·
                      rfl

theorem cell22_3396616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 3, 1, 1, 4].length) (baseStart_3396616 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3396616 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3396616 prefixEnd_3396616 := by exact prefixLift 3396616
  have htrace : WordTrace (prefixWord ++ tailWord_3396616) baseStart_3396616 baseEnd_3396616 := by
    simpa [prefixWord, tailWord_3396616, baseEnd_3396616] using wordTrace_append hprefix tailTrace_3396616
  have hstable : (prefixWord ++ tailWord_3396616).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3396616).length < 2 ^ (prefixWord ++ tailWord_3396616).sum := by decide
  have hdescent : baseEnd_3396616 < baseStart_3396616 := by decide
  rcases family_descends (prefixWord ++ tailWord_3396616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3396631 : List Nat := [1, 1, 3, 5, 1, 2, 1, 4, 4]
def baseStart_3396631 : Nat := 118140960795 + 3396631 * 2 ^ 59
def prefixEnd_3396631 : Nat := 4983230072969 + 3 ^ 40 * 3396631 * 2
def baseEnd_3396631 : Nat := 387578735324845644287041

theorem tailTrace_3396631 : CollatzResearch.WordTrace tailWord_3396631 prefixEnd_3396631 387578735324845644287041 := by
  unfold tailWord_3396631
  simp only [CollatzResearch.WordTrace]
  refine ⟨123885310157593460235917747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82590206771728973490611831 123885310157593460235917747)
  ·
    refine ⟨185827965236390190353876621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123885310157593460235917747 185827965236390190353876621)
    ·
      refine ⟨69685486963646321382703733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 185827965236390190353876621 69685486963646321382703733)
      ·
        refine ⟨6533014402841842629628475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 69685486963646321382703733 6533014402841842629628475)
        ·
          refine ⟨9799521604262763944442713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6533014402841842629628475 9799521604262763944442713)
          ·
            refine ⟨7349641203197072958332035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9799521604262763944442713 7349641203197072958332035)
            ·
              refine ⟨11024461804795609437498053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7349641203197072958332035 11024461804795609437498053)
              ·
                refine ⟨2067086588399176769530885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11024461804795609437498053 2067086588399176769530885)
                ·
                  refine ⟨387578735324845644287041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2067086588399176769530885 387578735324845644287041)
                  ·
                    rfl

theorem cell22_3396631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 1, 4, 4].length) (baseStart_3396631 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3396631 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3396631 prefixEnd_3396631 := by exact prefixLift 3396631
  have htrace : WordTrace (prefixWord ++ tailWord_3396631) baseStart_3396631 baseEnd_3396631 := by
    simpa [prefixWord, tailWord_3396631, baseEnd_3396631] using wordTrace_append hprefix tailTrace_3396631
  have hstable : (prefixWord ++ tailWord_3396631).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3396631).length < 2 ^ (prefixWord ++ tailWord_3396631).sum := by decide
  have hdescent : baseEnd_3396631 < baseStart_3396631 := by decide
  rcases family_descends (prefixWord ++ tailWord_3396631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3396796 : List Nat := [2, 2, 2, 3, 2, 1, 2, 2, 2, 4]
def baseStart_3396796 : Nat := 118140960795 + 3396796 * 2 ^ 59
def prefixEnd_3396796 : Nat := 4983230072969 + 3 ^ 40 * 3396796 * 2
def baseEnd_3396796 : Nat := 1162792688846531502485617

theorem tailTrace_3396796 : CollatzResearch.WordTrace tailWord_3396796 prefixEnd_3396796 1162792688846531502485617 := by
  unfold tailWord_3396796
  simp only [CollatzResearch.WordTrace]
  refine ⟨61945664100997846707837121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82594218801330462277116161 61945664100997846707837121)
  ·
    refine ⟨46459248075748385030877841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61945664100997846707837121 46459248075748385030877841)
    ·
      refine ⟨34844436056811288773158381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46459248075748385030877841 34844436056811288773158381)
      ·
        refine ⟨13066663521304233289934393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34844436056811288773158381 13066663521304233289934393)
        ·
          refine ⟨9799997640978174967450795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13066663521304233289934393 9799997640978174967450795)
          ·
            refine ⟨14699996461467262451176193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9799997640978174967450795 14699996461467262451176193)
            ·
              refine ⟨11024997346100446838382145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14699996461467262451176193 11024997346100446838382145)
              ·
                refine ⟨8268748009575335128786609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11024997346100446838382145 8268748009575335128786609)
                ·
                  refine ⟨6201561007181501346589957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8268748009575335128786609 6201561007181501346589957)
                  ·
                    refine ⟨1162792688846531502485617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6201561007181501346589957 1162792688846531502485617)
                    ·
                      rfl

theorem cell22_3396796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 2, 2, 2, 4].length) (baseStart_3396796 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3396796 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3396796 prefixEnd_3396796 := by exact prefixLift 3396796
  have htrace : WordTrace (prefixWord ++ tailWord_3396796) baseStart_3396796 baseEnd_3396796 := by
    simpa [prefixWord, tailWord_3396796, baseEnd_3396796] using wordTrace_append hprefix tailTrace_3396796
  have hstable : (prefixWord ++ tailWord_3396796).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3396796).length < 2 ^ (prefixWord ++ tailWord_3396796).sum := by decide
  have hdescent : baseEnd_3396796 < baseStart_3396796 := by decide
  rcases family_descends (prefixWord ++ tailWord_3396796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3396798 : List Nat := [4, 2, 1, 1, 3, 1, 1, 4, 2, 3]
def baseStart_3396798 : Nat := 118140960795 + 3396798 * 2 ^ 59
def prefixEnd_3396798 : Nat := 4983230072969 + 3 ^ 40 * 3396798 * 2
def baseEnd_3396798 : Nat := 1162793373487404163935611

theorem tailTrace_3396798 : CollatzResearch.WordTrace tailWord_3396798 prefixEnd_3396798 1162793373487404163935611 := by
  unfold tailWord_3396798
  simp only [CollatzResearch.WordTrace]
  refine ⟨15486425143498555969655881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 82594267431992298504831365 15486425143498555969655881)
  ·
    refine ⟨11614818857623916977241911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15486425143498555969655881 11614818857623916977241911)
    ·
      refine ⟨17422228286435875465862867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11614818857623916977241911 17422228286435875465862867)
      ·
        refine ⟨26133342429653813198794301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17422228286435875465862867 26133342429653813198794301)
        ·
          refine ⟨9800003411120179949547863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26133342429653813198794301 9800003411120179949547863)
          ·
            refine ⟨14700005116680269924321795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9800003411120179949547863 14700005116680269924321795)
            ·
              refine ⟨22050007675020404886482693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14700005116680269924321795 22050007675020404886482693)
              ·
                refine ⟨4134376439066325916215505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22050007675020404886482693 4134376439066325916215505)
                ·
                  refine ⟨3100782329299744437161629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4134376439066325916215505 3100782329299744437161629)
                  ·
                    refine ⟨1162793373487404163935611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3100782329299744437161629 1162793373487404163935611)
                    ·
                      rfl

theorem cell22_3396798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 1, 4, 2, 3].length) (baseStart_3396798 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3396798 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3396798 prefixEnd_3396798 := by exact prefixLift 3396798
  have htrace : WordTrace (prefixWord ++ tailWord_3396798) baseStart_3396798 baseEnd_3396798 := by
    simpa [prefixWord, tailWord_3396798, baseEnd_3396798] using wordTrace_append hprefix tailTrace_3396798
  have hstable : (prefixWord ++ tailWord_3396798).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3396798).length < 2 ^ (prefixWord ++ tailWord_3396798).sum := by decide
  have hdescent : baseEnd_3396798 < baseStart_3396798 := by decide
  rcases family_descends (prefixWord ++ tailWord_3396798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3396800 : List Nat := [2, 1, 1, 2, 6, 2, 2, 2, 4]
def baseStart_3396800 : Nat := 118140960795 + 3396800 * 2 ^ 59
def prefixEnd_3396800 : Nat := 4983230072969 + 3 ^ 40 * 3396800 * 2
def baseEnd_3396800 : Nat := 387598019376092275128535

theorem tailTrace_3396800 : CollatzResearch.WordTrace tailWord_3396800 prefixEnd_3396800 387598019376092275128535 := by
  unfold tailWord_3396800
  simp only [CollatzResearch.WordTrace]
  refine ⟨61945737046990601049409927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82594316062654134732546569 61945737046990601049409927)
  ·
    refine ⟨92918605570485901574114891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61945737046990601049409927 92918605570485901574114891)
    ·
      refine ⟨139377908355728852361172337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92918605570485901574114891 139377908355728852361172337)
      ·
        refine ⟨104533431266796639270879253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139377908355728852361172337 104533431266796639270879253)
        ·
          refine ⟨4900004590631092465822465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 104533431266796639270879253 4900004590631092465822465)
          ·
            refine ⟨3675003442973319349366849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4900004590631092465822465 3675003442973319349366849)
            ·
              refine ⟨2756252582229989512025137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3675003442973319349366849 2756252582229989512025137)
              ·
                refine ⟨2067189436672492134018853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2756252582229989512025137 2067189436672492134018853)
                ·
                  refine ⟨387598019376092275128535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2067189436672492134018853 387598019376092275128535)
                  ·
                    rfl

theorem cell22_3396800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 2, 2, 2, 4].length) (baseStart_3396800 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3396800 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3396800 prefixEnd_3396800 := by exact prefixLift 3396800
  have htrace : WordTrace (prefixWord ++ tailWord_3396800) baseStart_3396800 baseEnd_3396800 := by
    simpa [prefixWord, tailWord_3396800, baseEnd_3396800] using wordTrace_append hprefix tailTrace_3396800
  have hstable : (prefixWord ++ tailWord_3396800).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3396800).length < 2 ^ (prefixWord ++ tailWord_3396800).sum := by decide
  have hdescent : baseEnd_3396800 < baseStart_3396800 := by decide
  rcases family_descends (prefixWord ++ tailWord_3396800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3396843 : List Nat := [1, 1, 1, 1, 2, 6, 1, 5, 1, 3]
def baseStart_3396843 : Nat := 118140960795 + 3396843 * 2 ^ 59
def prefixEnd_3396843 : Nat := 4983230072969 + 3 ^ 40 * 3396843 * 2
def baseEnd_3396843 : Nat := 1162808777907039046560473

theorem tailTrace_3396843 : CollatzResearch.WordTrace tailWord_3396843 prefixEnd_3396843 1162808777907039046560473 := by
  unfold tailWord_3396843
  simp only [CollatzResearch.WordTrace]
  refine ⟨123893042432825420442635183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82595361621883613628423455 123893042432825420442635183)
  ·
    refine ⟨185839563649238130663952775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123893042432825420442635183 185839563649238130663952775)
    ·
      refine ⟨278759345473857195995929163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185839563649238130663952775 278759345473857195995929163)
      ·
        refine ⟨418139018210785793993893745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 278759345473857195995929163 418139018210785793993893745)
        ·
          refine ⟨313604263658089345495420309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 418139018210785793993893745 313604263658089345495420309)
          ·
            refine ⟨14700199858972938070097827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 313604263658089345495420309 14700199858972938070097827)
            ·
              refine ⟨22050299788459407105146741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14700199858972938070097827 22050299788459407105146741)
              ·
                refine ⟨2067215605168069416107507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22050299788459407105146741 2067215605168069416107507)
                ·
                  refine ⟨3100823407752104124161261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2067215605168069416107507 3100823407752104124161261)
                  ·
                    refine ⟨1162808777907039046560473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3100823407752104124161261 1162808777907039046560473)
                    ·
                      rfl

theorem cell22_3396843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 1, 5, 1, 3].length) (baseStart_3396843 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3396843 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3396843 prefixEnd_3396843 := by exact prefixLift 3396843
  have htrace : WordTrace (prefixWord ++ tailWord_3396843) baseStart_3396843 baseEnd_3396843 := by
    simpa [prefixWord, tailWord_3396843, baseEnd_3396843] using wordTrace_append hprefix tailTrace_3396843
  have hstable : (prefixWord ++ tailWord_3396843).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3396843).length < 2 ^ (prefixWord ++ tailWord_3396843).sum := by decide
  have hdescent : baseEnd_3396843 < baseStart_3396843 := by decide
  rcases family_descends (prefixWord ++ tailWord_3396843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3396948 : List Nat := [2, 4, 1, 1, 2, 1, 4, 1, 2, 4]
def baseStart_3396948 : Nat := 118140960795 + 3396948 * 2 ^ 59
def prefixEnd_3396948 : Nat := 4983230072969 + 3 ^ 40 * 3396948 * 2
def baseEnd_3396948 : Nat := 1162844721552853772685151

theorem tailTrace_3396948 : CollatzResearch.WordTrace tailWord_3396948 prefixEnd_3396948 1162844721552853772685151 := by
  unfold tailWord_3396948
  simp only [CollatzResearch.WordTrace]
  refine ⟨61948436048722511687603749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82597914731630015583471665 61948436048722511687603749)
  ·
    refine ⟨11615331759135470941425703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 61948436048722511687603749 11615331759135470941425703)
    ·
      refine ⟨17422997638703206412138555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11615331759135470941425703 17422997638703206412138555)
      ·
        refine ⟨26134496458054809618207833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17422997638703206412138555 26134496458054809618207833)
        ·
          refine ⟨19600872343541107213655875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26134496458054809618207833 19600872343541107213655875)
          ·
            refine ⟨29401308515311660820483813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19600872343541107213655875 29401308515311660820483813)
            ·
              refine ⟨5512745346620936403840715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29401308515311660820483813 5512745346620936403840715)
              ·
                refine ⟨8269118019931404605761073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5512745346620936403840715 8269118019931404605761073)
                ·
                  refine ⟨6201838514948553454320805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8269118019931404605761073 6201838514948553454320805)
                  ·
                    refine ⟨1162844721552853772685151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6201838514948553454320805 1162844721552853772685151)
                    ·
                      rfl

theorem cell22_3396948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 4, 1, 2, 4].length) (baseStart_3396948 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3396948 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3396948 prefixEnd_3396948 := by exact prefixLift 3396948
  have htrace : WordTrace (prefixWord ++ tailWord_3396948) baseStart_3396948 baseEnd_3396948 := by
    simpa [prefixWord, tailWord_3396948, baseEnd_3396948] using wordTrace_append hprefix tailTrace_3396948
  have hstable : (prefixWord ++ tailWord_3396948).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3396948).length < 2 ^ (prefixWord ++ tailWord_3396948).sum := by decide
  have hdescent : baseEnd_3396948 < baseStart_3396948 := by decide
  rcases family_descends (prefixWord ++ tailWord_3396948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3396978 : List Nat := [3, 2, 1, 2, 1, 2, 2, 3, 3, 3]
def baseStart_3396978 : Nat := 118140960795 + 3396978 * 2 ^ 59
def prefixEnd_3396978 : Nat := 4983230072969 + 3 ^ 40 * 3396978 * 2
def baseEnd_3396978 : Nat := 1162854991165943694435059

theorem tailTrace_3396978 : CollatzResearch.WordTrace tailWord_3396978 prefixEnd_3396978 1162854991165943694435059 := by
  unfold tailWord_3396978
  simp only [CollatzResearch.WordTrace]
  refine ⟨30974491571834084624699897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82598644191557558999199725 30974491571834084624699897)
  ·
    refine ⟨23230868678875563468524923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30974491571834084624699897 23230868678875563468524923)
    ·
      refine ⟨34846303018313345202787385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23230868678875563468524923 34846303018313345202787385)
      ·
        refine ⟨26134727263735008902090539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34846303018313345202787385 26134727263735008902090539)
        ·
          refine ⟨39202090895602513353135809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26134727263735008902090539 39202090895602513353135809)
          ·
            refine ⟨29401568171701885014851857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39202090895602513353135809 29401568171701885014851857)
            ·
              refine ⟨22051176128776413761138893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29401568171701885014851857 22051176128776413761138893)
              ·
                refine ⟨8269191048291155160427085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22051176128776413761138893 8269191048291155160427085)
                ·
                  refine ⟨3100946643109183185160157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8269191048291155160427085 3100946643109183185160157)
                  ·
                    refine ⟨1162854991165943694435059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3100946643109183185160157 1162854991165943694435059)
                    ·
                      rfl

theorem cell22_3396978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 2, 3, 3, 3].length) (baseStart_3396978 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3396978 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3396978 prefixEnd_3396978 := by exact prefixLift 3396978
  have htrace : WordTrace (prefixWord ++ tailWord_3396978) baseStart_3396978 baseEnd_3396978 := by
    simpa [prefixWord, tailWord_3396978, baseEnd_3396978] using wordTrace_append hprefix tailTrace_3396978
  have hstable : (prefixWord ++ tailWord_3396978).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3396978).length < 2 ^ (prefixWord ++ tailWord_3396978).sum := by decide
  have hdescent : baseEnd_3396978 < baseStart_3396978 := by decide
  rcases family_descends (prefixWord ++ tailWord_3396978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3397012 : List Nat := [2, 4, 2, 1, 2, 1, 1, 5, 1, 3]
def baseStart_3397012 : Nat := 118140960795 + 3397012 * 2 ^ 59
def prefixEnd_3397012 : Nat := 4983230072969 + 3 ^ 40 * 3397012 * 2
def baseEnd_3397012 : Nat := 1162866630060778939084955

theorem tailTrace_3397012 : CollatzResearch.WordTrace tailWord_3397012 prefixEnd_3397012 1162866630060778939084955 := by
  unfold tailWord_3397012
  simp only [CollatzResearch.WordTrace]
  refine ⟨61949603184606581152768645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82599470912808774870358193 61949603184606581152768645)
  ·
    refine ⟨11615550597113733966144121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 61949603184606581152768645 11615550597113733966144121)
    ·
      refine ⟨8711662947835300474608091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11615550597113733966144121 8711662947835300474608091)
      ·
        refine ⟨13067494421752950711912137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8711662947835300474608091 13067494421752950711912137)
        ·
          refine ⟨9800620816314713033934103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13067494421752950711912137 9800620816314713033934103)
          ·
            refine ⟨14700931224472069550901155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9800620816314713033934103 14700931224472069550901155)
            ·
              refine ⟨22051396836708104326351733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14700931224472069550901155 22051396836708104326351733)
              ·
                refine ⟨2067318453441384780595475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22051396836708104326351733 2067318453441384780595475)
                ·
                  refine ⟨3100977680162077170893213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2067318453441384780595475 3100977680162077170893213)
                  ·
                    refine ⟨1162866630060778939084955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3100977680162077170893213 1162866630060778939084955)
                    ·
                      rfl

theorem cell22_3397012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 1, 5, 1, 3].length) (baseStart_3397012 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3397012 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3397012 prefixEnd_3397012 := by exact prefixLift 3397012
  have htrace : WordTrace (prefixWord ++ tailWord_3397012) baseStart_3397012 baseEnd_3397012 := by
    simpa [prefixWord, tailWord_3397012, baseEnd_3397012] using wordTrace_append hprefix tailTrace_3397012
  have hstable : (prefixWord ++ tailWord_3397012).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3397012).length < 2 ^ (prefixWord ++ tailWord_3397012).sum := by decide
  have hdescent : baseEnd_3397012 < baseStart_3397012 := by decide
  rcases family_descends (prefixWord ++ tailWord_3397012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3397036 : List Nat := [2, 2, 1, 1, 1, 1, 5, 3, 6]
def baseStart_3397036 : Nat := 118140960795 + 3397036 * 2 ^ 59
def prefixEnd_3397036 : Nat := 4983230072969 + 3 ^ 40 * 3397036 * 2
def baseEnd_3397036 : Nat := 387624948583750292161627

theorem tailTrace_3397036 : CollatzResearch.WordTrace tailWord_3397036 prefixEnd_3397036 387624948583750292161627 := by
  unfold tailWord_3397036
  simp only [CollatzResearch.WordTrace]
  refine ⟨61950040860563107202205481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82600054480750809602940641 61950040860563107202205481)
  ·
    refine ⟨46462530645422330401654111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61950040860563107202205481 46462530645422330401654111)
    ·
      refine ⟨69693795968133495602481167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46462530645422330401654111 69693795968133495602481167)
      ·
        refine ⟨104540693952200243403721751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69693795968133495602481167 104540693952200243403721751)
        ·
          refine ⟨156811040928300365105582627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104540693952200243403721751 156811040928300365105582627)
          ·
            refine ⟨235216561392450547658373941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 156811040928300365105582627 235216561392450547658373941)
            ·
              refine ⟨22051552630542238842972557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 235216561392450547658373941 22051552630542238842972557)
              ·
                refine ⟨8269332236453339566114709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22051552630542238842972557 8269332236453339566114709)
                ·
                  refine ⟨387624948583750292161627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8269332236453339566114709 387624948583750292161627)
                  ·
                    rfl

theorem cell22_3397036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 6].length) (baseStart_3397036 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3397036 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3397036 prefixEnd_3397036 := by exact prefixLift 3397036
  have htrace : WordTrace (prefixWord ++ tailWord_3397036) baseStart_3397036 baseEnd_3397036 := by
    simpa [prefixWord, tailWord_3397036, baseEnd_3397036] using wordTrace_append hprefix tailTrace_3397036
  have hstable : (prefixWord ++ tailWord_3397036).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3397036).length < 2 ^ (prefixWord ++ tailWord_3397036).sum := by decide
  have hdescent : baseEnd_3397036 < baseStart_3397036 := by decide
  rcases family_descends (prefixWord ++ tailWord_3397036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3397070 : List Nat := [4, 1, 1, 1, 2, 1, 5, 3, 4]
def baseStart_3397070 : Nat := 118140960795 + 3397070 * 2 ^ 59
def prefixEnd_3397070 : Nat := 4983230072969 + 3 ^ 40 * 3397070 * 2
def baseEnd_3397070 : Nat := 387628828215362040378259

theorem tailTrace_3397070 : CollatzResearch.WordTrace tailWord_3397070 prefixEnd_3397070 387628828215362040378259 := by
  unfold tailWord_3397070
  simp only [CollatzResearch.WordTrace]
  refine ⟨15487665225375379776393583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 82600881202002025474099109 15487665225375379776393583)
  ·
    refine ⟨23231497838063069664590375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15487665225375379776393583 23231497838063069664590375)
    ·
      refine ⟨34847246757094604496885563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23231497838063069664590375 34847246757094604496885563)
      ·
        refine ⟨52270870135641906745328345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34847246757094604496885563 52270870135641906745328345)
        ·
          refine ⟨39203152601731430058996259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52270870135641906745328345 39203152601731430058996259)
          ·
            refine ⟨58804728902597145088494389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39203152601731430058996259 58804728902597145088494389)
            ·
              refine ⟨5512943334618482352046349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 58804728902597145088494389 5512943334618482352046349)
              ·
                refine ⟨2067353750481930882017381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5512943334618482352046349 2067353750481930882017381)
                ·
                  refine ⟨387628828215362040378259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2067353750481930882017381 387628828215362040378259)
                  ·
                    rfl

theorem cell22_3397070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 5, 3, 4].length) (baseStart_3397070 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3397070 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3397070 prefixEnd_3397070 := by exact prefixLift 3397070
  have htrace : WordTrace (prefixWord ++ tailWord_3397070) baseStart_3397070 baseEnd_3397070 := by
    simpa [prefixWord, tailWord_3397070, baseEnd_3397070] using wordTrace_append hprefix tailTrace_3397070
  have hstable : (prefixWord ++ tailWord_3397070).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3397070).length < 2 ^ (prefixWord ++ tailWord_3397070).sum := by decide
  have hdescent : baseEnd_3397070 < baseStart_3397070 := by decide
  rcases family_descends (prefixWord ++ tailWord_3397070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3397081 : List Nat := [1, 2, 1, 2, 4, 2, 10]
def baseStart_3397081 : Nat := 118140960795 + 3397081 * 2 ^ 59
def prefixEnd_3397081 : Nat := 4983230072969 + 3 ^ 40 * 3397081 * 2
def baseEnd_3397081 : Nat := 43070009265588361448509

theorem tailTrace_3397081 : CollatzResearch.WordTrace tailWord_3397081 prefixEnd_3397081 43070009265588361448509 := by
  unfold tailWord_3397081
  simp only [CollatzResearch.WordTrace]
  refine ⟨123901723005963187089799097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82601148670642124726532731 123901723005963187089799097)
  ·
    refine ⟨92926292254472390317349323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123901723005963187089799097 92926292254472390317349323)
    ·
      refine ⟨139389438381708585476023985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92926292254472390317349323 139389438381708585476023985)
      ·
        refine ⟨104542078786281439107017989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139389438381708585476023985 104542078786281439107017989)
        ·
          refine ⟨19601639772427769832565873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 104542078786281439107017989 19601639772427769832565873)
          ·
            refine ⟨14701229829320827374424405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19601639772427769832565873 14701229829320827374424405)
            ·
              refine ⟨43070009265588361448509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 14701229829320827374424405 43070009265588361448509)
              ·
                rfl

theorem cell22_3397081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 10].length) (baseStart_3397081 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3397081 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3397081 prefixEnd_3397081 := by exact prefixLift 3397081
  have htrace : WordTrace (prefixWord ++ tailWord_3397081) baseStart_3397081 baseEnd_3397081 := by
    simpa [prefixWord, tailWord_3397081, baseEnd_3397081] using wordTrace_append hprefix tailTrace_3397081
  have hstable : (prefixWord ++ tailWord_3397081).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3397081).length < 2 ^ (prefixWord ++ tailWord_3397081).sum := by decide
  have hdescent : baseEnd_3397081 < baseStart_3397081 := by decide
  rcases family_descends (prefixWord ++ tailWord_3397081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3397085 : List Nat := [1, 4, 3, 1, 1, 2, 2, 1, 4, 3]
def baseStart_3397085 : Nat := 118140960795 + 3397085 * 2 ^ 59
def prefixEnd_3397085 : Nat := 4983230072969 + 3 ^ 40 * 3397085 * 2
def baseEnd_3397085 : Nat := 1162891619452631082009731

theorem tailTrace_3397085 : CollatzResearch.WordTrace tailWord_3397085 prefixEnd_3397085 1162891619452631082009731 := by
  unfold tailWord_3397085
  simp only [CollatzResearch.WordTrace]
  refine ⟨123901868897948695772944709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82601245931965797181963139 123901868897948695772944709)
  ·
    refine ⟨23231600418365380457427133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 123901868897948695772944709 23231600418365380457427133)
    ·
      refine ⟨8711850156887017671535175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23231600418365380457427133 8711850156887017671535175)
      ·
        refine ⟨13067775235330526507302763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8711850156887017671535175 13067775235330526507302763)
        ·
          refine ⟨19601662852995789760954145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13067775235330526507302763 19601662852995789760954145)
          ·
            refine ⟨14701247139746842320715609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19601662852995789760954145 14701247139746842320715609)
            ·
              refine ⟨11025935354810131740536707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14701247139746842320715609 11025935354810131740536707)
              ·
                refine ⟨16538903032215197610805061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11025935354810131740536707 16538903032215197610805061)
                ·
                  refine ⟨3101044318540349552025949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16538903032215197610805061 3101044318540349552025949)
                  ·
                    refine ⟨1162891619452631082009731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3101044318540349552025949 1162891619452631082009731)
                    ·
                      rfl

theorem cell22_3397085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 2, 1, 4, 3].length) (baseStart_3397085 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3397085 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3397085 prefixEnd_3397085 := by exact prefixLift 3397085
  have htrace : WordTrace (prefixWord ++ tailWord_3397085) baseStart_3397085 baseEnd_3397085 := by
    simpa [prefixWord, tailWord_3397085, baseEnd_3397085] using wordTrace_append hprefix tailTrace_3397085
  have hstable : (prefixWord ++ tailWord_3397085).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3397085).length < 2 ^ (prefixWord ++ tailWord_3397085).sum := by decide
  have hdescent : baseEnd_3397085 < baseStart_3397085 := by decide
  rcases family_descends (prefixWord ++ tailWord_3397085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3397111 : List Nat := [1, 1, 3, 1, 1, 1, 1, 3, 4, 6]
def baseStart_3397111 : Nat := 118140960795 + 3397111 * 2 ^ 59
def prefixEnd_3397111 : Nat := 4983230072969 + 3 ^ 40 * 3397111 * 2
def baseEnd_3397111 : Nat := 1162900519783975680859651

theorem tailTrace_3397111 : CollatzResearch.WordTrace tailWord_3397111 prefixEnd_3397111 1162900519783975680859651 := by
  unfold tailWord_3397111
  simp only [CollatzResearch.WordTrace]
  refine ⟨123902817195854502213391187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82601878130569668142260791 123902817195854502213391187)
  ·
    refine ⟨185854225793781753320086781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123902817195854502213391187 185854225793781753320086781)
    ·
      refine ⟨69695334672668157495032543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 185854225793781753320086781 69695334672668157495032543)
      ·
        refine ⟨104543002009002236242548815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69695334672668157495032543 104543002009002236242548815)
        ·
          refine ⟨156814503013503354363823223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104543002009002236242548815 156814503013503354363823223)
          ·
            refine ⟨235221754520255031545734835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 156814503013503354363823223 235221754520255031545734835)
            ·
              refine ⟨352832631780382547318602253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 235221754520255031545734835 352832631780382547318602253)
              ·
                refine ⟨132312236917643455244475845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 352832631780382547318602253 132312236917643455244475845)
                ·
                  refine ⟨24808544422058147858339221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 132312236917643455244475845 24808544422058147858339221)
                  ·
                    refine ⟨1162900519783975680859651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24808544422058147858339221 1162900519783975680859651)
                    ·
                      rfl

theorem cell22_3397111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 3, 4, 6].length) (baseStart_3397111 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3397111 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3397111 prefixEnd_3397111 := by exact prefixLift 3397111
  have htrace : WordTrace (prefixWord ++ tailWord_3397111) baseStart_3397111 baseEnd_3397111 := by
    simpa [prefixWord, tailWord_3397111, baseEnd_3397111] using wordTrace_append hprefix tailTrace_3397111
  have hstable : (prefixWord ++ tailWord_3397111).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3397111).length < 2 ^ (prefixWord ++ tailWord_3397111).sum := by decide
  have hdescent : baseEnd_3397111 < baseStart_3397111 := by decide
  rcases family_descends (prefixWord ++ tailWord_3397111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3397113 : List Nat := [1, 2, 1, 3, 1, 2, 1, 3, 5, 3]
def baseStart_3397113 : Nat := 118140960795 + 3397113 * 2 ^ 59
def prefixEnd_3397113 : Nat := 4983230072969 + 3 ^ 40 * 3397113 * 2
def baseEnd_3397113 : Nat := 1162901204424848342309645

theorem tailTrace_3397113 : CollatzResearch.WordTrace tailWord_3397113 prefixEnd_3397113 1162901204424848342309645 := by
  unfold tailWord_3397113
  simp only [CollatzResearch.WordTrace]
  refine ⟨123902890141847256554963993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82601926761231504369975995 123902890141847256554963993)
  ·
    refine ⟨92927167606385442416222995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123902890141847256554963993 92927167606385442416222995)
    ·
      refine ⟨139390751409578163624334493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92927167606385442416222995 139390751409578163624334493)
      ·
        refine ⟨52271531778591811359125435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 139390751409578163624334493 52271531778591811359125435)
        ·
          refine ⟨78407297667887717038688153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52271531778591811359125435 78407297667887717038688153)
          ·
            refine ⟨58805473250915787779016115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78407297667887717038688153 58805473250915787779016115)
            ·
              refine ⟨88208209876373681668524173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58805473250915787779016115 88208209876373681668524173)
              ·
                refine ⟨33078078703640130625696565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 88208209876373681668524173 33078078703640130625696565)
                ·
                  refine ⟨3101069878466262246159053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 33078078703640130625696565 3101069878466262246159053)
                  ·
                    refine ⟨1162901204424848342309645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3101069878466262246159053 1162901204424848342309645)
                    ·
                      rfl

theorem cell22_3397113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 3, 5, 3].length) (baseStart_3397113 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3397113 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3397113 prefixEnd_3397113 := by exact prefixLift 3397113
  have htrace : WordTrace (prefixWord ++ tailWord_3397113) baseStart_3397113 baseEnd_3397113 := by
    simpa [prefixWord, tailWord_3397113, baseEnd_3397113] using wordTrace_append hprefix tailTrace_3397113
  have hstable : (prefixWord ++ tailWord_3397113).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3397113).length < 2 ^ (prefixWord ++ tailWord_3397113).sum := by decide
  have hdescent : baseEnd_3397113 < baseStart_3397113 := by decide
  rcases family_descends (prefixWord ++ tailWord_3397113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3397220 : List Nat := [2, 3, 1, 1, 2, 3, 3, 1, 1, 5]
def baseStart_3397220 : Nat := 118140960795 + 3397220 * 2 ^ 59
def prefixEnd_3397220 : Nat := 4983230072969 + 3 ^ 40 * 3397220 * 2
def baseEnd_3397220 : Nat := 1162937832711535729884317

theorem tailTrace_3397220 : CollatzResearch.WordTrace tailWord_3397220 prefixEnd_3397220 1162937832711535729884317 := by
  unfold tailWord_3397220
  simp only [CollatzResearch.WordTrace]
  refine ⟨61953396376229806914554557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82604528501639742552739409 61953396376229806914554557)
  ·
    refine ⟨23232523641086177592957959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61953396376229806914554557 23232523641086177592957959)
    ·
      refine ⟨34848785461629266389436939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23232523641086177592957959 34848785461629266389436939)
      ·
        refine ⟨52273178192443899584155409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34848785461629266389436939 52273178192443899584155409)
        ·
          refine ⟨39204883644332924688116557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52273178192443899584155409 39204883644332924688116557)
          ·
            refine ⟨14701831366624846758043709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39204883644332924688116557 14701831366624846758043709)
            ·
              refine ⟨5513186762484317534266391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14701831366624846758043709 5513186762484317534266391)
              ·
                refine ⟨8269780143726476301399587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5513186762484317534266391 8269780143726476301399587)
                ·
                  refine ⟨12404670215589714452099381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8269780143726476301399587 12404670215589714452099381)
                  ·
                    refine ⟨1162937832711535729884317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12404670215589714452099381 1162937832711535729884317)
                    ·
                      rfl

theorem cell22_3397220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 3, 1, 1, 5].length) (baseStart_3397220 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3397220 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3397220 prefixEnd_3397220 := by exact prefixLift 3397220
  have htrace : WordTrace (prefixWord ++ tailWord_3397220) baseStart_3397220 baseEnd_3397220 := by
    simpa [prefixWord, tailWord_3397220, baseEnd_3397220] using wordTrace_append hprefix tailTrace_3397220
  have hstable : (prefixWord ++ tailWord_3397220).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3397220).length < 2 ^ (prefixWord ++ tailWord_3397220).sum := by decide
  have hdescent : baseEnd_3397220 < baseStart_3397220 := by decide
  rcases family_descends (prefixWord ++ tailWord_3397220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3397237 : List Nat := [1, 3, 4, 2, 1, 1, 1, 2, 4, 3]
def baseStart_3397237 : Nat := 118140960795 + 3397237 * 2 ^ 59
def prefixEnd_3397237 : Nat := 4983230072969 + 3 ^ 40 * 3397237 * 2
def baseEnd_3397237 : Nat := 1162943652158953352209265

theorem tailTrace_3397237 : CollatzResearch.WordTrace tailWord_3397237 prefixEnd_3397237 1162943652158953352209265 := by
  unfold tailWord_3397237
  simp only [CollatzResearch.WordTrace]
  refine ⟨123907412793398025732477965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82604941862265350488318643 123907412793398025732477965)
  ·
    refine ⟨46465279797524259649679237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123907412793398025732477965 46465279797524259649679237)
    ·
      refine ⟨8712239962035798684314857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46465279797524259649679237 8712239962035798684314857)
      ·
        refine ⟨6534179971526849013236143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8712239962035798684314857 6534179971526849013236143)
        ·
          refine ⟨9801269957290273519854215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6534179971526849013236143 9801269957290273519854215)
          ·
            refine ⟨14701904935935410279781323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9801269957290273519854215 14701904935935410279781323)
            ·
              refine ⟨22052857403903115419671985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14701904935935410279781323 22052857403903115419671985)
              ·
                refine ⟨16539643052927336564753989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22052857403903115419671985 16539643052927336564753989)
                ·
                  refine ⟨3101183072423875605891373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16539643052927336564753989 3101183072423875605891373)
                  ·
                    refine ⟨1162943652158953352209265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3101183072423875605891373 1162943652158953352209265)
                    ·
                      rfl

theorem cell22_3397237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 1, 2, 4, 3].length) (baseStart_3397237 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3397237 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3397237 prefixEnd_3397237 := by exact prefixLift 3397237
  have htrace : WordTrace (prefixWord ++ tailWord_3397237) baseStart_3397237 baseEnd_3397237 := by
    simpa [prefixWord, tailWord_3397237, baseEnd_3397237] using wordTrace_append hprefix tailTrace_3397237
  have hstable : (prefixWord ++ tailWord_3397237).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3397237).length < 2 ^ (prefixWord ++ tailWord_3397237).sum := by decide
  have hdescent : baseEnd_3397237 < baseStart_3397237 := by decide
  rcases family_descends (prefixWord ++ tailWord_3397237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3397252 : List Nat := [2, 3, 2, 1, 4, 1, 1, 2, 2, 4]
def baseStart_3397252 : Nat := 118140960795 + 3397252 * 2 ^ 59
def prefixEnd_3397252 : Nat := 4983230072969 + 3 ^ 40 * 3397252 * 2
def baseEnd_3397252 : Nat := 1162948786965498313084219

theorem tailTrace_3397252 : CollatzResearch.WordTrace tailWord_3397252 prefixEnd_3397252 1162948786965498313084219 := by
  unfold tailWord_3397252
  simp only [CollatzResearch.WordTrace]
  refine ⟨61953979944171841647137005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82605306592229122196182673 61953979944171841647137005)
  ·
    refine ⟨23232742479064440617676377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61953979944171841647137005 23232742479064440617676377)
    ·
      refine ⟨17424556859298330463257283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23232742479064440617676377 17424556859298330463257283)
      ·
        refine ⟨26136835288947495694885925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17424556859298330463257283 26136835288947495694885925)
        ·
          refine ⟨4900656616677655442791111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26136835288947495694885925 4900656616677655442791111)
          ·
            refine ⟨7350984925016483164186667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4900656616677655442791111 7350984925016483164186667)
            ·
              refine ⟨11026477387524724746280001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7350984925016483164186667 11026477387524724746280001)
              ·
                refine ⟨8269858040643543559710001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11026477387524724746280001 8269858040643543559710001)
                ·
                  refine ⟨6202393530482657669782501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8269858040643543559710001 6202393530482657669782501)
                  ·
                    refine ⟨1162948786965498313084219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6202393530482657669782501 1162948786965498313084219)
                    ·
                      rfl

theorem cell22_3397252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 1, 2, 2, 4].length) (baseStart_3397252 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3397252 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3397252 prefixEnd_3397252 := by exact prefixLift 3397252
  have htrace : WordTrace (prefixWord ++ tailWord_3397252) baseStart_3397252 baseEnd_3397252 := by
    simpa [prefixWord, tailWord_3397252, baseEnd_3397252] using wordTrace_append hprefix tailTrace_3397252
  have hstable : (prefixWord ++ tailWord_3397252).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3397252).length < 2 ^ (prefixWord ++ tailWord_3397252).sum := by decide
  have hdescent : baseEnd_3397252 < baseStart_3397252 := by decide
  rcases family_descends (prefixWord ++ tailWord_3397252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3397256 : List Nat := [2, 1, 3, 5, 1, 1, 3, 2, 4]
def baseStart_3397256 : Nat := 118140960795 + 3397256 * 2 ^ 59
def prefixEnd_3397256 : Nat := 4983230072969 + 3 ^ 40 * 3397256 * 2
def baseEnd_3397256 : Nat := 387650052082414545328069

theorem tailTrace_3397256 : CollatzResearch.WordTrace tailWord_3397256 prefixEnd_3397256 387650052082414545328069 := by
  unfold tailWord_3397256
  simp only [CollatzResearch.WordTrace]
  refine ⟨61954052890164595988709811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82605403853552794651613081 61954052890164595988709811)
  ·
    refine ⟨92931079335246893983064717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61954052890164595988709811 92931079335246893983064717)
    ·
      refine ⟨34849154750717585243649269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92931079335246893983064717 34849154750717585243649269)
      ·
        refine ⟨3267108257879773616592119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 34849154750717585243649269 3267108257879773616592119)
        ·
          refine ⟨4900662386819660424888179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3267108257879773616592119 4900662386819660424888179)
          ·
            refine ⟨7350993580229490637332269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4900662386819660424888179 7350993580229490637332269)
            ·
              refine ⟨2756622592586058988999601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7350993580229490637332269 2756622592586058988999601)
              ·
                refine ⟨2067466944439544241749701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2756622592586058988999601 2067466944439544241749701)
                ·
                  refine ⟨387650052082414545328069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2067466944439544241749701 387650052082414545328069)
                  ·
                    rfl

theorem cell22_3397256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 3, 2, 4].length) (baseStart_3397256 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3397256 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3397256 prefixEnd_3397256 := by exact prefixLift 3397256
  have htrace : WordTrace (prefixWord ++ tailWord_3397256) baseStart_3397256 baseEnd_3397256 := by
    simpa [prefixWord, tailWord_3397256, baseEnd_3397256] using wordTrace_append hprefix tailTrace_3397256
  have hstable : (prefixWord ++ tailWord_3397256).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3397256).length < 2 ^ (prefixWord ++ tailWord_3397256).sum := by decide
  have hdescent : baseEnd_3397256 < baseStart_3397256 := by decide
  rcases family_descends (prefixWord ++ tailWord_3397256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
