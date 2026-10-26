import V185TrunkScan22Chunk069

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_630409 : List Nat := [1, 2, 1, 1, 4, 1, 4, 1, 1, 6]
def baseStart_630409 : Nat := 118140960795 + 630409 * 2 ^ 59
def prefixEnd_630409 : Nat := 4983230072969 + 3 ^ 40 * 630409 * 2
def baseEnd_630409 : Nat := 215801883946886170392205

theorem tailTrace_630409 : CollatzResearch.WordTrace tailWord_630409 prefixEnd_630409 215801883946886170392205 := by
  unfold tailWord_630409
  simp only [CollatzResearch.WordTrace]
  refine ⟨22992905173143333130638281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15328603448762222087092187 22992905173143333130638281)
  ·
    refine ⟨17244678879857499847978711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22992905173143333130638281 17244678879857499847978711)
    ·
      refine ⟨25867018319786249771968067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17244678879857499847978711 25867018319786249771968067)
      ·
        refine ⟨38800527479679374657952101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25867018319786249771968067 38800527479679374657952101)
        ·
          refine ⟨7275098902439882748366019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 38800527479679374657952101 7275098902439882748366019)
          ·
            refine ⟨10912648353659824122549029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7275098902439882748366019 10912648353659824122549029)
            ·
              refine ⟨2046121566311217022977943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10912648353659824122549029 2046121566311217022977943)
              ·
                refine ⟨3069182349466825534466915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2046121566311217022977943 3069182349466825534466915)
                ·
                  refine ⟨4603773524200238301700373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3069182349466825534466915 4603773524200238301700373)
                  ·
                    refine ⟨215801883946886170392205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4603773524200238301700373 215801883946886170392205)
                    ·
                      rfl

theorem cell22_630409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 4, 1, 1, 6].length) (baseStart_630409 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_630409 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_630409 prefixEnd_630409 := by exact prefixLift 630409
  have htrace : WordTrace (prefixWord ++ tailWord_630409) baseStart_630409 baseEnd_630409 := by
    simpa [prefixWord, tailWord_630409, baseEnd_630409] using wordTrace_append hprefix tailTrace_630409
  have hstable : (prefixWord ++ tailWord_630409).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_630409).length < 2 ^ (prefixWord ++ tailWord_630409).sum := by decide
  have hdescent : baseEnd_630409 < baseStart_630409 := by decide
  rcases family_descends (prefixWord ++ tailWord_630409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_630424 : List Nat := [2, 1, 2, 4, 1, 2, 10]
def baseStart_630424 : Nat := 118140960795 + 630424 * 2 ^ 59
def prefixEnd_630424 : Nat := 4983230072969 + 3 ^ 40 * 630424 * 2
def baseEnd_630424 : Nat := 7992852546423375232117

theorem tailTrace_630424 : CollatzResearch.WordTrace tailWord_630424 prefixEnd_630424 7992852546423375232117 := by
  unfold tailWord_630424
  simp only [CollatzResearch.WordTrace]
  refine ⟨11496726134044495346217163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15328968178725993794956217 11496726134044495346217163)
  ·
    refine ⟨17245089201066743019325745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11496726134044495346217163 17245089201066743019325745)
    ·
      refine ⟨12933816900800057264494309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17245089201066743019325745 12933816900800057264494309)
      ·
        refine ⟨2425090668900010737092683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12933816900800057264494309 2425090668900010737092683)
        ·
          refine ⟨3637636003350016105639025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2425090668900010737092683 3637636003350016105639025)
          ·
            refine ⟨2728227002512512079229269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3637636003350016105639025 2728227002512512079229269)
            ·
              refine ⟨7992852546423375232117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 2728227002512512079229269 7992852546423375232117)
              ·
                rfl

theorem cell22_630424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 10].length) (baseStart_630424 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_630424 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_630424 prefixEnd_630424 := by exact prefixLift 630424
  have htrace : WordTrace (prefixWord ++ tailWord_630424) baseStart_630424 baseEnd_630424 := by
    simpa [prefixWord, tailWord_630424, baseEnd_630424] using wordTrace_append hprefix tailTrace_630424
  have hstable : (prefixWord ++ tailWord_630424).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_630424).length < 2 ^ (prefixWord ++ tailWord_630424).sum := by decide
  have hdescent : baseEnd_630424 < baseStart_630424 := by decide
  rcases family_descends (prefixWord ++ tailWord_630424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_630456 : List Nat := [2, 1, 2, 1, 2, 1, 1, 6, 3, 3]
def baseStart_630456 : Nat := 118140960795 + 630456 * 2 ^ 59
def prefixEnd_630456 : Nat := 4983230072969 + 3 ^ 40 * 630456 * 2
def baseEnd_630456 : Nat := 215817973007393714467061

theorem tailTrace_630456 : CollatzResearch.WordTrace tailWord_630456 prefixEnd_630456 215817973007393714467061 := by
  unfold tailWord_630456
  simp only [CollatzResearch.WordTrace]
  refine ⟨11497309701986530078799611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15329746269315373438399481 11497309701986530078799611)
  ·
    refine ⟨17245964552979795118199417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11497309701986530078799611 17245964552979795118199417)
    ·
      refine ⟨12934473414734846338649563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17245964552979795118199417 12934473414734846338649563)
      ·
        refine ⟨19401710122102269507974345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12934473414734846338649563 19401710122102269507974345)
        ·
          refine ⟨14551282591576702130980759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19401710122102269507974345 14551282591576702130980759)
          ·
            refine ⟨21826923887365053196471139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14551282591576702130980759 21826923887365053196471139)
            ·
              refine ⟨32740385831047579794706709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21826923887365053196471139 32740385831047579794706709)
              ·
                refine ⟨1534705585830355302876877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 32740385831047579794706709 1534705585830355302876877)
                ·
                  refine ⟨575514594686383238578829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1534705585830355302876877 575514594686383238578829)
                  ·
                    refine ⟨215817973007393714467061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 575514594686383238578829 215817973007393714467061)
                    ·
                      rfl

theorem cell22_630456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 6, 3, 3].length) (baseStart_630456 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_630456 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_630456 prefixEnd_630456 := by exact prefixLift 630456
  have htrace : WordTrace (prefixWord ++ tailWord_630456) baseStart_630456 baseEnd_630456 := by
    simpa [prefixWord, tailWord_630456, baseEnd_630456] using wordTrace_append hprefix tailTrace_630456
  have hstable : (prefixWord ++ tailWord_630456).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_630456).length < 2 ^ (prefixWord ++ tailWord_630456).sum := by decide
  have hdescent : baseEnd_630456 < baseStart_630456 := by decide
  rcases family_descends (prefixWord ++ tailWord_630456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_630490 : List Nat := [3, 1, 1, 2, 2, 4, 1, 4, 1, 3]
def baseStart_630490 : Nat := 118140960795 + 630490 * 2 ^ 59
def prefixEnd_630490 : Nat := 4983230072969 + 3 ^ 40 * 630490 * 2
def baseEnd_630490 : Nat := 215829611902228959116957

theorem tailTrace_630490 : CollatzResearch.WordTrace tailWord_630490 prefixEnd_630490 215829611902228959116957 := by
  unfold tailWord_630490
  simp only [CollatzResearch.WordTrace]
  refine ⟨5748964871462470991084231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15330572990566589309557949 5748964871462470991084231)
  ·
    refine ⟨8623447307193706486626347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5748964871462470991084231 8623447307193706486626347)
    ·
      refine ⟨12935170960790559729939521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8623447307193706486626347 12935170960790559729939521)
      ·
        refine ⟨9701378220592919797454641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12935170960790559729939521 9701378220592919797454641)
        ·
          refine ⟨7276033665444689848090981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9701378220592919797454641 7276033665444689848090981)
          ·
            refine ⟨1364256312270879346517059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7276033665444689848090981 1364256312270879346517059)
            ·
              refine ⟨2046384468406319019775589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1364256312270879346517059 2046384468406319019775589)
              ·
                refine ⟨383697087826184816207923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2046384468406319019775589 383697087826184816207923)
                ·
                  refine ⟨575545631739277224311885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 383697087826184816207923 575545631739277224311885)
                  ·
                    refine ⟨215829611902228959116957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 575545631739277224311885 215829611902228959116957)
                    ·
                      rfl

theorem cell22_630490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 1, 4, 1, 3].length) (baseStart_630490 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_630490 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_630490 prefixEnd_630490 := by exact prefixLift 630490
  have htrace : WordTrace (prefixWord ++ tailWord_630490) baseStart_630490 baseEnd_630490 := by
    simpa [prefixWord, tailWord_630490, baseEnd_630490] using wordTrace_append hprefix tailTrace_630490
  have hstable : (prefixWord ++ tailWord_630490).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_630490).length < 2 ^ (prefixWord ++ tailWord_630490).sum := by decide
  have hdescent : baseEnd_630490 < baseStart_630490 := by decide
  rcases family_descends (prefixWord ++ tailWord_630490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_630501 : List Nat := [1, 3, 1, 4, 1, 1, 3, 1, 2, 5]
def baseStart_630501 : Nat := 118140960795 + 630501 * 2 ^ 59
def prefixEnd_630501 : Nat := 4983230072969 + 3 ^ 40 * 630501 * 2
def baseEnd_630501 : Nat := 215833377427028597091923

theorem tailTrace_630501 : CollatzResearch.WordTrace tailWord_630501 prefixEnd_630501 215833377427028597091923 := by
  unfold tailWord_630501
  simp only [CollatzResearch.WordTrace]
  refine ⟨22996260688810032842987357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15330840459206688561991571 22996260688810032842987357)
  ·
    refine ⟨8623597758303762316120259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22996260688810032842987357 8623597758303762316120259)
    ·
      refine ⟨12935396637455643474180389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8623597758303762316120259 12935396637455643474180389)
      ·
        refine ⟨2425386869522933151408823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12935396637455643474180389 2425386869522933151408823)
        ·
          refine ⟨3638080304284399727113235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2425386869522933151408823 3638080304284399727113235)
          ·
            refine ⟨5457120456426599590669853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3638080304284399727113235 5457120456426599590669853)
            ·
              refine ⟨2046420171159974846501195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5457120456426599590669853 2046420171159974846501195)
              ·
                refine ⟨3069630256739962269751793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2046420171159974846501195 3069630256739962269751793)
                ·
                  refine ⟨2302222692554971702313845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3069630256739962269751793 2302222692554971702313845)
                  ·
                    refine ⟨215833377427028597091923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2302222692554971702313845 215833377427028597091923)
                    ·
                      rfl

theorem cell22_630501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 3, 1, 2, 5].length) (baseStart_630501 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_630501 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_630501 prefixEnd_630501 := by exact prefixLift 630501
  have htrace : WordTrace (prefixWord ++ tailWord_630501) baseStart_630501 baseEnd_630501 := by
    simpa [prefixWord, tailWord_630501, baseEnd_630501] using wordTrace_append hprefix tailTrace_630501
  have hstable : (prefixWord ++ tailWord_630501).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_630501).length < 2 ^ (prefixWord ++ tailWord_630501).sum := by decide
  have hdescent : baseEnd_630501 < baseStart_630501 := by decide
  rcases family_descends (prefixWord ++ tailWord_630501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_630541 : List Nat := [1, 7, 2, 1, 1, 1, 2, 1, 3, 3]
def baseStart_630541 : Nat := 118140960795 + 630541 * 2 ^ 59
def prefixEnd_630541 : Nat := 4983230072969 + 3 ^ 40 * 630541 * 2
def baseEnd_630541 : Nat := 215847070244481826091801

theorem tailTrace_630541 : CollatzResearch.WordTrace tailWord_630541 prefixEnd_630541 215847070244481826091801 := by
  unfold tailWord_630541
  simp only [CollatzResearch.WordTrace]
  refine ⟨22997719608665119674443477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15331813072443413116295651 22997719608665119674443477)
  ·
    refine ⟨539009053328088742369769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 22997719608665119674443477 539009053328088742369769)
    ·
      refine ⟨404256789996066556777327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 539009053328088742369769 404256789996066556777327)
      ·
        refine ⟨606385184994099835165991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 404256789996066556777327 606385184994099835165991)
        ·
          refine ⟨909577777491149752748987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 606385184994099835165991 909577777491149752748987)
          ·
            refine ⟨1364366666236724629123481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 909577777491149752748987 1364366666236724629123481)
            ·
              refine ⟨1023274999677543471842611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1364366666236724629123481 1023274999677543471842611)
              ·
                refine ⟨1534912499516315207763917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1023274999677543471842611 1534912499516315207763917)
                ·
                  refine ⟨575592187318618202911469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1534912499516315207763917 575592187318618202911469)
                  ·
                    refine ⟨215847070244481826091801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 575592187318618202911469 215847070244481826091801)
                    ·
                      rfl

theorem cell22_630541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 2, 1, 3, 3].length) (baseStart_630541 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_630541 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_630541 prefixEnd_630541 := by exact prefixLift 630541
  have htrace : WordTrace (prefixWord ++ tailWord_630541) baseStart_630541 baseEnd_630541 := by
    simpa [prefixWord, tailWord_630541, baseEnd_630541] using wordTrace_append hprefix tailTrace_630541
  have hstable : (prefixWord ++ tailWord_630541).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_630541).length < 2 ^ (prefixWord ++ tailWord_630541).sum := by decide
  have hdescent : baseEnd_630541 < baseStart_630541 := by decide
  rcases family_descends (prefixWord ++ tailWord_630541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_630561 : List Nat := [1, 2, 3, 2, 1, 3, 1, 2, 1, 6]
def baseStart_630561 : Nat := 118140960795 + 630561 * 2 ^ 59
def prefixEnd_630561 : Nat := 4983230072969 + 3 ^ 40 * 630561 * 2
def baseEnd_630561 : Nat := 215853916653208440591739

theorem tailTrace_630561 : CollatzResearch.WordTrace tailWord_630561 prefixEnd_630561 215853916653208440591739 := by
  unfold tailWord_630561
  simp only [CollatzResearch.WordTrace]
  refine ⟨22998449068592663090171537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15332299379061775393447691 22998449068592663090171537)
  ·
    refine ⟨17248836801444497317628653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22998449068592663090171537 17248836801444497317628653)
    ·
      refine ⟨6468313800541686494110745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17248836801444497317628653 6468313800541686494110745)
      ·
        refine ⟨4851235350406264870583059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6468313800541686494110745 4851235350406264870583059)
        ·
          refine ⟨7276853025609397305874589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4851235350406264870583059 7276853025609397305874589)
          ·
            refine ⟨2728819884603523989702971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7276853025609397305874589 2728819884603523989702971)
            ·
              refine ⟨4093229826905285984554457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2728819884603523989702971 4093229826905285984554457)
              ·
                refine ⟨3069922370178964488415843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4093229826905285984554457 3069922370178964488415843)
                ·
                  refine ⟨4604883555268446732623765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3069922370178964488415843 4604883555268446732623765)
                  ·
                    refine ⟨215853916653208440591739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4604883555268446732623765 215853916653208440591739)
                    ·
                      rfl

theorem cell22_630561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 1, 2, 1, 6].length) (baseStart_630561 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_630561 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_630561 prefixEnd_630561 := by exact prefixLift 630561
  have htrace : WordTrace (prefixWord ++ tailWord_630561) baseStart_630561 baseEnd_630561 := by
    simpa [prefixWord, tailWord_630561, baseEnd_630561] using wordTrace_append hprefix tailTrace_630561
  have hstable : (prefixWord ++ tailWord_630561).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_630561).length < 2 ^ (prefixWord ++ tailWord_630561).sum := by decide
  have hdescent : baseEnd_630561 < baseStart_630561 := by decide
  rcases family_descends (prefixWord ++ tailWord_630561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_630563 : List Nat := [1, 1, 1, 4, 2, 1, 2, 5, 2, 3]
def baseStart_630563 : Nat := 118140960795 + 630563 * 2 ^ 59
def prefixEnd_630563 : Nat := 4983230072969 + 3 ^ 40 * 630563 * 2
def baseEnd_630563 : Nat := 215854601294081102041733

theorem tailTrace_630563 : CollatzResearch.WordTrace tailWord_630563 prefixEnd_630563 215854601294081102041733 := by
  unfold tailWord_630563
  simp only [CollatzResearch.WordTrace]
  refine ⟨22998522014585417431744343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15332348009723611621162895 22998522014585417431744343)
  ·
    refine ⟨34497783021878126147616515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22998522014585417431744343 34497783021878126147616515)
    ·
      refine ⟨51746674532817189221424773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34497783021878126147616515 51746674532817189221424773)
      ·
        refine ⟨9702501474903222979017145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 51746674532817189221424773 9702501474903222979017145)
        ·
          refine ⟨7276876106177417234262859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9702501474903222979017145 7276876106177417234262859)
          ·
            refine ⟨10915314159266125851394289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7276876106177417234262859 10915314159266125851394289)
            ·
              refine ⟨8186485619449594388545717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10915314159266125851394289 8186485619449594388545717)
              ·
                refine ⟨767483026823399473926161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8186485619449594388545717 767483026823399473926161)
                ·
                  refine ⟨575612270117549605444621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 767483026823399473926161 575612270117549605444621)
                  ·
                    refine ⟨215854601294081102041733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 575612270117549605444621 215854601294081102041733)
                    ·
                      rfl

theorem cell22_630563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 5, 2, 3].length) (baseStart_630563 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_630563 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_630563 prefixEnd_630563 := by exact prefixLift 630563
  have htrace : WordTrace (prefixWord ++ tailWord_630563) baseStart_630563 baseEnd_630563 := by
    simpa [prefixWord, tailWord_630563, baseEnd_630563] using wordTrace_append hprefix tailTrace_630563
  have hstable : (prefixWord ++ tailWord_630563).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_630563).length < 2 ^ (prefixWord ++ tailWord_630563).sum := by decide
  have hdescent : baseEnd_630563 < baseStart_630563 := by decide
  rcases family_descends (prefixWord ++ tailWord_630563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_630580 : List Nat := [2, 5, 1, 1, 2, 1, 1, 2, 4, 3]
def baseStart_630580 : Nat := 118140960795 + 630580 * 2 ^ 59
def prefixEnd_630580 : Nat := 4983230072969 + 3 ^ 40 * 630580 * 2
def baseEnd_630580 : Nat := 215860420741498724366681

theorem tailTrace_630580 : CollatzResearch.WordTrace tailWord_630580 prefixEnd_630580 215860420741498724366681 := by
  unfold tailWord_630580
  simp only [CollatzResearch.WordTrace]
  refine ⟨11499571027761914667556597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15332761370349219556742129 11499571027761914667556597)
  ·
    refine ⟨1078084783852679500083431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 11499571027761914667556597 1078084783852679500083431)
    ·
      refine ⟨1617127175779019250125147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1078084783852679500083431 1617127175779019250125147)
      ·
        refine ⟨2425690763668528875187721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1617127175779019250125147 2425690763668528875187721)
        ·
          refine ⟨1819268072751396656390791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2425690763668528875187721 1819268072751396656390791)
          ·
            refine ⟨2728902109127094984586187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1819268072751396656390791 2728902109127094984586187)
            ·
              refine ⟨4093353163690642476879281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2728902109127094984586187 4093353163690642476879281)
              ·
                refine ⟨3070014872767981857659461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4093353163690642476879281 3070014872767981857659461)
                ·
                  refine ⟨575627788643996598311149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3070014872767981857659461 575627788643996598311149)
                  ·
                    refine ⟨215860420741498724366681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 575627788643996598311149 215860420741498724366681)
                    ·
                      rfl

theorem cell22_630580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 1, 2, 4, 3].length) (baseStart_630580 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_630580 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_630580 prefixEnd_630580 := by exact prefixLift 630580
  have htrace : WordTrace (prefixWord ++ tailWord_630580) baseStart_630580 baseEnd_630580 := by
    simpa [prefixWord, tailWord_630580, baseEnd_630580] using wordTrace_append hprefix tailTrace_630580
  have hstable : (prefixWord ++ tailWord_630580).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_630580).length < 2 ^ (prefixWord ++ tailWord_630580).sum := by decide
  have hdescent : baseEnd_630580 < baseStart_630580 := by decide
  rcases family_descends (prefixWord ++ tailWord_630580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_630582 : List Nat := [5, 1, 2, 2, 1, 1, 3, 3, 4]
def baseStart_630582 : Nat := 118140960795 + 630582 * 2 ^ 59
def prefixEnd_630582 : Nat := 4983230072969 + 3 ^ 40 * 630582 * 2
def baseEnd_630582 : Nat := 71953701794123795272225

theorem tailTrace_630582 : CollatzResearch.WordTrace tailWord_630582 prefixEnd_630582 71953701794123795272225 := by
  unfold tailWord_630582
  simp only [CollatzResearch.WordTrace]
  refine ⟨1437450937594786479792875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 15332810001011055784457333 1437450937594786479792875)
  ·
    refine ⟨2156176406392179719689313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1437450937594786479792875 2156176406392179719689313)
    ·
      refine ⟨1617132304794134789766985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2156176406392179719689313 1617132304794134789766985)
      ·
        refine ⟨1212849228595601092325239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1617132304794134789766985 1212849228595601092325239)
        ·
          refine ⟨1819273842893401638487859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1212849228595601092325239 1819273842893401638487859)
          ·
            refine ⟨2728910764340102457731789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1819273842893401638487859 2728910764340102457731789)
            ·
              refine ⟨1023341536627538421649421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2728910764340102457731789 1023341536627538421649421)
              ·
                refine ⟨383753076235326908118533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1023341536627538421649421 383753076235326908118533)
                ·
                  refine ⟨71953701794123795272225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 383753076235326908118533 71953701794123795272225)
                  ·
                    rfl

theorem cell22_630582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 3, 3, 4].length) (baseStart_630582 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_630582 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_630582 prefixEnd_630582 := by exact prefixLift 630582
  have htrace : WordTrace (prefixWord ++ tailWord_630582) baseStart_630582 baseEnd_630582 := by
    simpa [prefixWord, tailWord_630582, baseEnd_630582] using wordTrace_append hprefix tailTrace_630582
  have hstable : (prefixWord ++ tailWord_630582).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_630582).length < 2 ^ (prefixWord ++ tailWord_630582).sum := by decide
  have hdescent : baseEnd_630582 < baseStart_630582 := by decide
  rcases family_descends (prefixWord ++ tailWord_630582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_630659 : List Nat := [1, 1, 1, 3, 4, 4, 2, 2, 1, 3]
def baseStart_630659 : Nat := 118140960795 + 630659 * 2 ^ 59
def prefixEnd_630659 : Nat := 4983230072969 + 3 ^ 40 * 630659 * 2
def baseEnd_630659 : Nat := 215887464055968851641439

theorem tailTrace_630659 : CollatzResearch.WordTrace tailWord_630659 prefixEnd_630659 215887464055968851641439 := by
  unfold tailWord_630659
  simp only [CollatzResearch.WordTrace]
  refine ⟨23002023422237625827239031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15334682281491750551492687 23002023422237625827239031)
  ·
    refine ⟨34503035133356438740858547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23002023422237625827239031 34503035133356438740858547)
    ·
      refine ⟨51754552700034658111287821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34503035133356438740858547 51754552700034658111287821)
      ·
        refine ⟨19407957262512996791732933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51754552700034658111287821 19407957262512996791732933)
        ·
          refine ⟨3638991986721186898449925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19407957262512996791732933 3638991986721186898449925)
          ·
            refine ⟨682310997510222543459361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3638991986721186898449925 682310997510222543459361)
            ·
              refine ⟨511733248132666907594521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 682310997510222543459361 511733248132666907594521)
              ·
                refine ⟨383799936099500180695891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 511733248132666907594521 383799936099500180695891)
                ·
                  refine ⟨575699904149250271043837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 383799936099500180695891 575699904149250271043837)
                  ·
                    refine ⟨215887464055968851641439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 575699904149250271043837 215887464055968851641439)
                    ·
                      rfl

theorem cell22_630659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 4, 2, 2, 1, 3].length) (baseStart_630659 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_630659 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_630659 prefixEnd_630659 := by exact prefixLift 630659
  have htrace : WordTrace (prefixWord ++ tailWord_630659) baseStart_630659 baseEnd_630659 := by
    simpa [prefixWord, tailWord_630659, baseEnd_630659] using wordTrace_append hprefix tailTrace_630659
  have hstable : (prefixWord ++ tailWord_630659).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_630659).length < 2 ^ (prefixWord ++ tailWord_630659).sum := by decide
  have hdescent : baseEnd_630659 < baseStart_630659 := by decide
  rcases family_descends (prefixWord ++ tailWord_630659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_630713 : List Nat := [1, 2, 1, 4, 2, 1, 2, 1, 4, 4]
def baseStart_630713 : Nat := 118140960795 + 630713 * 2 ^ 59
def prefixEnd_630713 : Nat := 4983230072969 + 3 ^ 40 * 630713 * 2
def baseEnd_630713 : Nat := 215905949359530710791273

theorem tailTrace_630713 : CollatzResearch.WordTrace tailWord_630713 prefixEnd_630713 215905949359530710791273 := by
  unfold tailWord_630713
  simp only [CollatzResearch.WordTrace]
  refine ⟨23003992964041993049704793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15335995309361328699803195 23003992964041993049704793)
  ·
    refine ⟨17252994723031494787278595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23003992964041993049704793 17252994723031494787278595)
    ·
      refine ⟨25879492084547242180917893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17252994723031494787278595 25879492084547242180917893)
      ·
        refine ⟨4852404765852607908922105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25879492084547242180917893 4852404765852607908922105)
        ·
          refine ⟨3639303574389455931691579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4852404765852607908922105 3639303574389455931691579)
          ·
            refine ⟨5458955361584183897537369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3639303574389455931691579 5458955361584183897537369)
            ·
              refine ⟨4094216521188137923153027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5458955361584183897537369 4094216521188137923153027)
              ·
                refine ⟨6141324781782206884729541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4094216521188137923153027 6141324781782206884729541)
                ·
                  refine ⟨1151498396584163790886789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6141324781782206884729541 1151498396584163790886789)
                  ·
                    refine ⟨215905949359530710791273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1151498396584163790886789 215905949359530710791273)
                    ·
                      rfl

theorem cell22_630713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 2, 1, 4, 4].length) (baseStart_630713 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_630713 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_630713 prefixEnd_630713 := by exact prefixLift 630713
  have htrace : WordTrace (prefixWord ++ tailWord_630713) baseStart_630713 baseEnd_630713 := by
    simpa [prefixWord, tailWord_630713, baseEnd_630713] using wordTrace_append hprefix tailTrace_630713
  have hstable : (prefixWord ++ tailWord_630713).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_630713).length < 2 ^ (prefixWord ++ tailWord_630713).sum := by decide
  have hdescent : baseEnd_630713 < baseStart_630713 := by decide
  rcases family_descends (prefixWord ++ tailWord_630713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_630777 : List Nat := [1, 2, 1, 3, 1, 6, 1, 1, 3, 3]
def baseStart_630777 : Nat := 118140960795 + 630777 * 2 ^ 59
def prefixEnd_630777 : Nat := 4983230072969 + 3 ^ 40 * 630777 * 2
def baseEnd_630777 : Nat := 215927857867455877191077

theorem tailTrace_630777 : CollatzResearch.WordTrace tailWord_630777 prefixEnd_630777 215927857867455877191077 := by
  unfold tailWord_630777
  simp only [CollatzResearch.WordTrace]
  refine ⟨23006327235810131980034585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15337551490540087986689723 23006327235810131980034585)
  ·
    refine ⟨17254745426857598985025939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23006327235810131980034585 17254745426857598985025939)
    ·
      refine ⟨25882118140286398477538909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17254745426857598985025939 25882118140286398477538909)
      ·
        refine ⟨9705794302607399429077091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25882118140286398477538909 9705794302607399429077091)
        ·
          refine ⟨14558691453911099143615637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9705794302607399429077091 14558691453911099143615637)
          ·
            refine ⟨682438661902082772356983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 14558691453911099143615637 682438661902082772356983)
            ·
              refine ⟨1023657992853124158535475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 682438661902082772356983 1023657992853124158535475)
              ·
                refine ⟨1535486989279686237803213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1023657992853124158535475 1535486989279686237803213)
                ·
                  refine ⟨575807620979882339176205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1535486989279686237803213 575807620979882339176205)
                  ·
                    refine ⟨215927857867455877191077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 575807620979882339176205 215927857867455877191077)
                    ·
                      rfl

theorem cell22_630777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 6, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 6, 1, 1, 3, 3].length) (baseStart_630777 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_630777 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_630777 prefixEnd_630777 := by exact prefixLift 630777
  have htrace : WordTrace (prefixWord ++ tailWord_630777) baseStart_630777 baseEnd_630777 := by
    simpa [prefixWord, tailWord_630777, baseEnd_630777] using wordTrace_append hprefix tailTrace_630777
  have hstable : (prefixWord ++ tailWord_630777).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_630777).length < 2 ^ (prefixWord ++ tailWord_630777).sum := by decide
  have hdescent : baseEnd_630777 < baseStart_630777 := by decide
  rcases family_descends (prefixWord ++ tailWord_630777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_630824 : List Nat := [2, 1, 5, 3, 1, 1, 2, 2, 5]
def baseStart_630824 : Nat := 118140960795 + 630824 * 2 ^ 59
def prefixEnd_630824 : Nat := 4983230072969 + 3 ^ 40 * 630824 * 2
def baseEnd_630824 : Nat := 71981315642654473755311

theorem tailTrace_630824 : CollatzResearch.WordTrace tailWord_630824 prefixEnd_630824 71981315642654473755311 := by
  unfold tailWord_630824
  simp only [CollatzResearch.WordTrace]
  refine ⟨11504020733319929503497763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15338694311093239337997017 11504020733319929503497763)
  ·
    refine ⟨17256031099979894255246645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11504020733319929503497763 17256031099979894255246645)
    ·
      refine ⟨1617752915623115086429373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 17256031099979894255246645 1617752915623115086429373)
      ·
        refine ⟨606657343358668157411015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1617752915623115086429373 606657343358668157411015)
        ·
          refine ⟨909986015038002236116523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 606657343358668157411015 909986015038002236116523)
          ·
            refine ⟨1364979022557003354174785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 909986015038002236116523 1364979022557003354174785)
            ·
              refine ⟨1023734266917752515631089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1364979022557003354174785 1023734266917752515631089)
              ·
                refine ⟨767800700188314386723317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1023734266917752515631089 767800700188314386723317)
                ·
                  refine ⟨71981315642654473755311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 767800700188314386723317 71981315642654473755311)
                  ·
                    rfl

theorem cell22_630824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 2, 2, 5].length) (baseStart_630824 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_630824 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_630824 prefixEnd_630824 := by exact prefixLift 630824
  have htrace : WordTrace (prefixWord ++ tailWord_630824) baseStart_630824 baseEnd_630824 := by
    simpa [prefixWord, tailWord_630824, baseEnd_630824] using wordTrace_append hprefix tailTrace_630824
  have hstable : (prefixWord ++ tailWord_630824).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_630824).length < 2 ^ (prefixWord ++ tailWord_630824).sum := by decide
  have hdescent : baseEnd_630824 < baseStart_630824 := by decide
  rcases family_descends (prefixWord ++ tailWord_630824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_630854 : List Nat := [6, 1, 1, 1, 1, 1, 2, 4, 1, 4]
def baseStart_630854 : Nat := 118140960795 + 630854 * 2 ^ 59
def prefixEnd_630854 : Nat := 4983230072969 + 3 ^ 40 * 630854 * 2
def baseEnd_630854 : Nat := 215954216541053343015841

theorem tailTrace_630854 : CollatzResearch.WordTrace tailWord_630854 prefixEnd_630854 215954216541053343015841 := by
  unfold tailWord_630854
  simp only [CollatzResearch.WordTrace]
  refine ⟨719035489266599191580863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 15339423771020782753725077 719035489266599191580863)
  ·
    refine ⟨1078553233899898787371295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 719035489266599191580863 1078553233899898787371295)
    ·
      refine ⟨1617829850849848181056943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1078553233899898787371295 1617829850849848181056943)
      ·
        refine ⟨2426744776274772271585415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1617829850849848181056943 2426744776274772271585415)
        ·
          refine ⟨3640117164412158407378123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2426744776274772271585415 3640117164412158407378123)
          ·
            refine ⟨5460175746618237611067185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3640117164412158407378123 5460175746618237611067185)
            ·
              refine ⟨4095131809963678208300389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5460175746618237611067185 4095131809963678208300389)
              ·
                refine ⟨767837214368189664056323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4095131809963678208300389 767837214368189664056323)
                ·
                  refine ⟨1151755821552284496084485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 767837214368189664056323 1151755821552284496084485)
                  ·
                    refine ⟨215954216541053343015841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1151755821552284496084485 215954216541053343015841)
                    ·
                      rfl

theorem cell22_630854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 2, 4, 1, 4].length) (baseStart_630854 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_630854 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_630854 prefixEnd_630854 := by exact prefixLift 630854
  have htrace : WordTrace (prefixWord ++ tailWord_630854) baseStart_630854 baseEnd_630854 := by
    simpa [prefixWord, tailWord_630854, baseEnd_630854] using wordTrace_append hprefix tailTrace_630854
  have hstable : (prefixWord ++ tailWord_630854).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_630854).length < 2 ^ (prefixWord ++ tailWord_630854).sum := by decide
  have hdescent : baseEnd_630854 < baseStart_630854 := by decide
  rcases family_descends (prefixWord ++ tailWord_630854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_630946 : List Nat := [3, 3, 1, 3, 1, 3, 1, 1, 3, 3]
def baseStart_630946 : Nat := 118140960795 + 630946 * 2 ^ 59
def prefixEnd_630946 : Nat := 4983230072969 + 3 ^ 40 * 630946 * 2
def baseEnd_630946 : Nat := 215985710021195769715559

theorem tailTrace_630946 : CollatzResearch.WordTrace tailWord_630946 prefixEnd_630946 215985710021195769715559 := by
  unfold tailWord_630946
  simp only [CollatzResearch.WordTrace]
  refine ⟨5753122793049468460734173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15341660781465249228624461 5753122793049468460734173)
  ·
    refine ⟨2157421047393550672775315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5753122793049468460734173 2157421047393550672775315)
    ·
      refine ⟨3236131571090326009162973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2157421047393550672775315 3236131571090326009162973)
      ·
        refine ⟨1213549339158872253436115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3236131571090326009162973 1213549339158872253436115)
        ·
          refine ⟨1820324008738308380154173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1213549339158872253436115 1820324008738308380154173)
          ·
            refine ⟨682621503276865642557815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1820324008738308380154173 682621503276865642557815)
            ·
              refine ⟨1023932254915298463836723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 682621503276865642557815 1023932254915298463836723)
              ·
                refine ⟨1535898382372947695755085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1023932254915298463836723 1535898382372947695755085)
                ·
                  refine ⟨575961893389855385908157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1535898382372947695755085 575961893389855385908157)
                  ·
                    refine ⟨215985710021195769715559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 575961893389855385908157 215985710021195769715559)
                    ·
                      rfl

theorem cell22_630946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 3, 1, 1, 3, 3].length) (baseStart_630946 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_630946 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_630946 prefixEnd_630946 := by exact prefixLift 630946
  have htrace : WordTrace (prefixWord ++ tailWord_630946) baseStart_630946 baseEnd_630946 := by
    simpa [prefixWord, tailWord_630946, baseEnd_630946] using wordTrace_append hprefix tailTrace_630946
  have hstable : (prefixWord ++ tailWord_630946).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_630946).length < 2 ^ (prefixWord ++ tailWord_630946).sum := by decide
  have hdescent : baseEnd_630946 < baseStart_630946 := by decide
  rcases family_descends (prefixWord ++ tailWord_630946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_630970 : List Nat := [3, 1, 1, 1, 2, 2, 2, 4, 6]
def baseStart_630970 : Nat := 118140960795 + 630970 * 2 ^ 59
def prefixEnd_630970 : Nat := 4983230072969 + 3 ^ 40 * 630970 * 2
def baseEnd_630970 : Nat := 71997975237222569038495

theorem tailTrace_630970 : CollatzResearch.WordTrace tailWord_630970 prefixEnd_630970 71997975237222569038495 := by
  unfold tailWord_630970
  simp only [CollatzResearch.WordTrace]
  refine ⟨5753341631027731485452591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15342244349407283961206909 5753341631027731485452591)
  ·
    refine ⟨8630012446541597228178887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5753341631027731485452591 8630012446541597228178887)
    ·
      refine ⟨12945018669812395842268331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8630012446541597228178887 12945018669812395842268331)
      ·
        refine ⟨19417528004718593763402497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12945018669812395842268331 19417528004718593763402497)
        ·
          refine ⟨14563146003538945322551873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19417528004718593763402497 14563146003538945322551873)
          ·
            refine ⟨10922359502654208991913905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14563146003538945322551873 10922359502654208991913905)
            ·
              refine ⟨8191769626990656743935429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10922359502654208991913905 8191769626990656743935429)
              ·
                refine ⟨1535956805060748139487893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8191769626990656743935429 1535956805060748139487893)
                ·
                  refine ⟨71997975237222569038495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1535956805060748139487893 71997975237222569038495)
                  ·
                    rfl

theorem cell22_630970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 4, 6].length) (baseStart_630970 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_630970 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_630970 prefixEnd_630970 := by exact prefixLift 630970
  have htrace : WordTrace (prefixWord ++ tailWord_630970) baseStart_630970 baseEnd_630970 := by
    simpa [prefixWord, tailWord_630970, baseEnd_630970] using wordTrace_append hprefix tailTrace_630970
  have hstable : (prefixWord ++ tailWord_630970).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_630970).length < 2 ^ (prefixWord ++ tailWord_630970).sum := by decide
  have hdescent : baseEnd_630970 < baseStart_630970 := by decide
  rcases family_descends (prefixWord ++ tailWord_630970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_630987 : List Nat := [1, 1, 1, 1, 3, 2, 4, 5, 4]
def baseStart_630987 : Nat := 118140960795 + 630987 * 2 ^ 59
def prefixEnd_630987 : Nat := 4983230072969 + 3 ^ 40 * 630987 * 2
def baseEnd_630987 : Nat := 71999915053028443146811

theorem tailTrace_630987 : CollatzResearch.WordTrace tailWord_630987 prefixEnd_630987 71999915053028443146811 := by
  unfold tailWord_630987
  simp only [CollatzResearch.WordTrace]
  refine ⟨23013986565049337845179215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15342657710032891896786143 23013986565049337845179215)
  ·
    refine ⟨34520979847574006767768823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23013986565049337845179215 34520979847574006767768823)
    ·
      refine ⟨51781469771361010151653235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34520979847574006767768823 51781469771361010151653235)
      ·
        refine ⟨77672204657041515227479853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51781469771361010151653235 77672204657041515227479853)
        ·
          refine ⟨29127076746390568210304945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 77672204657041515227479853 29127076746390568210304945)
          ·
            refine ⟨21845307559792926157728709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29127076746390568210304945 21845307559792926157728709)
            ·
              refine ⟨4095995167461173654574133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21845307559792926157728709 4095995167461173654574133)
              ·
                refine ⟨383999546949485030116325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4095995167461173654574133 383999546949485030116325)
                ·
                  refine ⟨71999915053028443146811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 383999546949485030116325 71999915053028443146811)
                  ·
                    rfl

theorem cell22_630987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 4, 5, 4].length) (baseStart_630987 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_630987 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_630987 prefixEnd_630987 := by exact prefixLift 630987
  have htrace : WordTrace (prefixWord ++ tailWord_630987) baseStart_630987 baseEnd_630987 := by
    simpa [prefixWord, tailWord_630987, baseEnd_630987] using wordTrace_append hprefix tailTrace_630987
  have hstable : (prefixWord ++ tailWord_630987).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_630987).length < 2 ^ (prefixWord ++ tailWord_630987).sum := by decide
  have hdescent : baseEnd_630987 < baseStart_630987 := by decide
  rcases family_descends (prefixWord ++ tailWord_630987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_631002 : List Nat := [3, 1, 1, 2, 2, 1, 2, 3, 4, 3]
def baseStart_631002 : Nat := 118140960795 + 631002 * 2 ^ 59
def prefixEnd_631002 : Nat := 4983230072969 + 3 ^ 40 * 631002 * 2
def baseEnd_631002 : Nat := 216004879965630290315387

theorem tailTrace_631002 : CollatzResearch.WordTrace tailWord_631002 prefixEnd_631002 216004879965630290315387 := by
  unfold tailWord_631002
  simp only [CollatzResearch.WordTrace]
  refine ⟨5753633414998748851743815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15343022439996663604650173 5753633414998748851743815)
  ·
    refine ⟨8630450122498123277615723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5753633414998748851743815 8630450122498123277615723)
    ·
      refine ⟨12945675183747184916423585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8630450122498123277615723 12945675183747184916423585)
      ·
        refine ⟨9709256387810388687317689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12945675183747184916423585 9709256387810388687317689)
        ·
          refine ⟨7281942290857791515488267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9709256387810388687317689 7281942290857791515488267)
          ·
            refine ⟨10922913436286687273232401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7281942290857791515488267 10922913436286687273232401)
            ·
              refine ⟨8192185077215015454924301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10922913436286687273232401 8192185077215015454924301)
              ·
                refine ⟨3072069403955630795596613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8192185077215015454924301 3072069403955630795596613)
                ·
                  refine ⟨576013013241680774174365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3072069403955630795596613 576013013241680774174365)
                  ·
                    refine ⟨216004879965630290315387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 576013013241680774174365 216004879965630290315387)
                    ·
                      rfl

theorem cell22_631002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 3, 4, 3].length) (baseStart_631002 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_631002 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_631002 prefixEnd_631002 := by exact prefixLift 631002
  have htrace : WordTrace (prefixWord ++ tailWord_631002) baseStart_631002 baseEnd_631002 := by
    simpa [prefixWord, tailWord_631002, baseEnd_631002] using wordTrace_append hprefix tailTrace_631002
  have hstable : (prefixWord ++ tailWord_631002).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_631002).length < 2 ^ (prefixWord ++ tailWord_631002).sum := by decide
  have hdescent : baseEnd_631002 < baseStart_631002 := by decide
  rcases family_descends (prefixWord ++ tailWord_631002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_631034 : List Nat := [3, 1, 1, 1, 1, 7, 1, 1, 2, 4]
def baseStart_631034 : Nat := 118140960795 + 631034 * 2 ^ 59
def prefixEnd_631034 : Nat := 4983230072969 + 3 ^ 40 * 631034 * 2
def baseEnd_631034 : Nat := 216015834219592873515289

theorem tailTrace_631034 : CollatzResearch.WordTrace tailWord_631034 prefixEnd_631034 216015834219592873515289 := by
  unfold tailWord_631034
  simp only [CollatzResearch.WordTrace]
  refine ⟨5753925198969766218035039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15343800530586043248093437 5753925198969766218035039)
  ·
    refine ⟨8630887798454649327052559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5753925198969766218035039 8630887798454649327052559)
    ·
      refine ⟨12946331697681973990578839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8630887798454649327052559 12946331697681973990578839)
      ·
        refine ⟨19419497546522960985868259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12946331697681973990578839 19419497546522960985868259)
        ·
          refine ⟨29129246319784441478802389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19419497546522960985868259 29129246319784441478802389)
          ·
            refine ⟨682716710619947847159431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 29129246319784441478802389 682716710619947847159431)
            ·
              refine ⟨1024075065929921770739147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 682716710619947847159431 1024075065929921770739147)
              ·
                refine ⟨1536112598894882656108721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1024075065929921770739147 1536112598894882656108721)
                ·
                  refine ⟨1152084449171161992081541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1536112598894882656108721 1152084449171161992081541)
                  ·
                    refine ⟨216015834219592873515289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1152084449171161992081541 216015834219592873515289)
                    ·
                      rfl

theorem cell22_631034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 7, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 7, 1, 1, 2, 4].length) (baseStart_631034 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_631034 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_631034 prefixEnd_631034 := by exact prefixLift 631034
  have htrace : WordTrace (prefixWord ++ tailWord_631034) baseStart_631034 baseEnd_631034 := by
    simpa [prefixWord, tailWord_631034, baseEnd_631034] using wordTrace_append hprefix tailTrace_631034
  have hstable : (prefixWord ++ tailWord_631034).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_631034).length < 2 ^ (prefixWord ++ tailWord_631034).sum := by decide
  have hdescent : baseEnd_631034 < baseStart_631034 := by decide
  rcases family_descends (prefixWord ++ tailWord_631034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_631045 : List Nat := [1, 3, 1, 1, 2, 1, 2, 2, 1, 8]
def baseStart_631045 : Nat := 118140960795 + 631045 * 2 ^ 59
def prefixEnd_631045 : Nat := 4983230072969 + 3 ^ 40 * 631045 * 2
def baseEnd_631045 : Nat := 216019599744392511490255

theorem tailTrace_631045 : CollatzResearch.WordTrace tailWord_631045 prefixEnd_631045 216019599744392511490255 := by
  unfold tailWord_631045
  simp only [CollatzResearch.WordTrace]
  refine ⟨23016101998839213750790589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15344067999226142500527059 23016101998839213750790589)
  ·
    refine ⟨8631038249564705156546471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23016101998839213750790589 8631038249564705156546471)
    ·
      refine ⟨12946557374347057734819707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8631038249564705156546471 12946557374347057734819707)
      ·
        refine ⟨19419836061520586602229561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12946557374347057734819707 19419836061520586602229561)
        ·
          refine ⟨14564877046140439951672171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19419836061520586602229561 14564877046140439951672171)
          ·
            refine ⟨21847315569210659927508257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14564877046140439951672171 21847315569210659927508257)
            ·
              refine ⟨16385486676907994945631193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21847315569210659927508257 16385486676907994945631193)
              ·
                refine ⟨12289115007680996209223395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16385486676907994945631193 12289115007680996209223395)
                ·
                  refine ⟨18433672511521494313835093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12289115007680996209223395 18433672511521494313835093)
                  ·
                    refine ⟨216019599744392511490255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 18433672511521494313835093 216019599744392511490255)
                    ·
                      rfl

theorem cell22_631045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 2, 1, 8].length) (baseStart_631045 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_631045 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_631045 prefixEnd_631045 := by exact prefixLift 631045
  have htrace : WordTrace (prefixWord ++ tailWord_631045) baseStart_631045 baseEnd_631045 := by
    simpa [prefixWord, tailWord_631045, baseEnd_631045] using wordTrace_append hprefix tailTrace_631045
  have hstable : (prefixWord ++ tailWord_631045).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_631045).length < 2 ^ (prefixWord ++ tailWord_631045).sum := by decide
  have hdescent : baseEnd_631045 < baseStart_631045 := by decide
  rcases family_descends (prefixWord ++ tailWord_631045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_631064 : List Nat := [2, 1, 2, 3, 1, 2, 4, 1, 3, 3]
def baseStart_631064 : Nat := 118140960795 + 631064 * 2 ^ 59
def prefixEnd_631064 : Nat := 4983230072969 + 3 ^ 40 * 631064 * 2
def baseEnd_631064 : Nat := 216026103832682795265197

theorem tailTrace_631064 : CollatzResearch.WordTrace tailWord_631064 prefixEnd_631064 216026103832682795265197 := by
  unfold tailWord_631064
  simp only [CollatzResearch.WordTrace]
  refine ⟨11508397492885189997866123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15344529990513586663821497 11508397492885189997866123)
  ·
    refine ⟨17262596239327784996799185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11508397492885189997866123 17262596239327784996799185)
    ·
      refine ⟨12946947179495838747599389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17262596239327784996799185 12946947179495838747599389)
      ·
        refine ⟨4855105192310939530349771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12946947179495838747599389 4855105192310939530349771)
        ·
          refine ⟨7282657788466409295524657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4855105192310939530349771 7282657788466409295524657)
          ·
            refine ⟨5461993341349806971643493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7282657788466409295524657 5461993341349806971643493)
            ·
              refine ⟨1024123751503088807183155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5461993341349806971643493 1024123751503088807183155)
              ·
                refine ⟨1536185627254633210774733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1024123751503088807183155 1536185627254633210774733)
                ·
                  refine ⟨576069610220487454040525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1536185627254633210774733 576069610220487454040525)
                  ·
                    refine ⟨216026103832682795265197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 576069610220487454040525 216026103832682795265197)
                    ·
                      rfl

theorem cell22_631064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 4, 1, 3, 3].length) (baseStart_631064 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_631064 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_631064 prefixEnd_631064 := by exact prefixLift 631064
  have htrace : WordTrace (prefixWord ++ tailWord_631064) baseStart_631064 baseEnd_631064 := by
    simpa [prefixWord, tailWord_631064, baseEnd_631064] using wordTrace_append hprefix tailTrace_631064
  have hstable : (prefixWord ++ tailWord_631064).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_631064).length < 2 ^ (prefixWord ++ tailWord_631064).sum := by decide
  have hdescent : baseEnd_631064 < baseStart_631064 := by decide
  rcases family_descends (prefixWord ++ tailWord_631064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_631070 : List Nat := [4, 3, 2, 1, 1, 2, 3, 1, 2, 3]
def baseStart_631070 : Nat := 118140960795 + 631070 * 2 ^ 59
def prefixEnd_631070 : Nat := 4983230072969 + 3 ^ 40 * 631070 * 2
def baseEnd_631070 : Nat := 216028157755300779615179

theorem tailTrace_631070 : CollatzResearch.WordTrace tailWord_631070 prefixEnd_631070 216028157755300779615179 := by
  unfold tailWord_631070
  simp only [CollatzResearch.WordTrace]
  refine ⟨2877126727968580377556333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15344675882499095346967109 2877126727968580377556333)
  ·
    refine ⟨1078922522988217641583625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2877126727968580377556333 1078922522988217641583625)
    ·
      refine ⟨809191892241163231187719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1078922522988217641583625 809191892241163231187719)
      ·
        refine ⟨1213787838361744846781579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 809191892241163231187719 1213787838361744846781579)
        ·
          refine ⟨1820681757542617270172369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1213787838361744846781579 1820681757542617270172369)
          ·
            refine ⟨1365511318156962952629277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1820681757542617270172369 1365511318156962952629277)
            ·
              refine ⟨512066744308861107235979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1365511318156962952629277 512066744308861107235979)
              ·
                refine ⟨768100116463291660853969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 512066744308861107235979 768100116463291660853969)
                ·
                  refine ⟨576075087347468745640477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 768100116463291660853969 576075087347468745640477)
                  ·
                    refine ⟨216028157755300779615179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 576075087347468745640477 216028157755300779615179)
                    ·
                      rfl

theorem cell22_631070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 3, 1, 2, 3].length) (baseStart_631070 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_631070 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_631070 prefixEnd_631070 := by exact prefixLift 631070
  have htrace : WordTrace (prefixWord ++ tailWord_631070) baseStart_631070 baseEnd_631070 := by
    simpa [prefixWord, tailWord_631070, baseEnd_631070] using wordTrace_append hprefix tailTrace_631070
  have hstable : (prefixWord ++ tailWord_631070).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_631070).length < 2 ^ (prefixWord ++ tailWord_631070).sum := by decide
  have hdescent : baseEnd_631070 < baseStart_631070 := by decide
  rcases family_descends (prefixWord ++ tailWord_631070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_631098 : List Nat := [3, 1, 1, 1, 4, 4, 1, 3, 1, 3]
def baseStart_631098 : Nat := 118140960795 + 631098 * 2 ^ 59
def prefixEnd_631098 : Nat := 4983230072969 + 3 ^ 40 * 631098 * 2
def baseEnd_631098 : Nat := 216037742727518039915093

theorem tailTrace_631098 : CollatzResearch.WordTrace tailWord_631098 prefixEnd_631098 216037742727518039915093 := by
  unfold tailWord_631098
  simp only [CollatzResearch.WordTrace]
  refine ⟨5754508766911800950617487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15345356711764802534979965 5754508766911800950617487)
  ·
    refine ⟨8631763150367701425926231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5754508766911800950617487 8631763150367701425926231)
    ·
      refine ⟨12947644725551552138889347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8631763150367701425926231 12947644725551552138889347)
      ·
        refine ⟨19421467088327328208334021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12947644725551552138889347 19421467088327328208334021)
        ·
          refine ⟨3641525079061374039062629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19421467088327328208334021 3641525079061374039062629)
          ·
            refine ⟨682785952324007632324243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3641525079061374039062629 682785952324007632324243)
            ·
              refine ⟨1024178928486011448486365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 682785952324007632324243 1024178928486011448486365)
              ·
                refine ⟨384067098182254293182387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1024178928486011448486365 384067098182254293182387)
                ·
                  refine ⟨576100647273381439773581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 384067098182254293182387 576100647273381439773581)
                  ·
                    refine ⟨216037742727518039915093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 576100647273381439773581 216037742727518039915093)
                    ·
                      rfl

theorem cell22_631098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 4, 1, 3, 1, 3].length) (baseStart_631098 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_631098 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_631098 prefixEnd_631098 := by exact prefixLift 631098
  have htrace : WordTrace (prefixWord ++ tailWord_631098) baseStart_631098 baseEnd_631098 := by
    simpa [prefixWord, tailWord_631098, baseEnd_631098] using wordTrace_append hprefix tailTrace_631098
  have hstable : (prefixWord ++ tailWord_631098).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_631098).length < 2 ^ (prefixWord ++ tailWord_631098).sum := by decide
  have hdescent : baseEnd_631098 < baseStart_631098 := by decide
  rcases family_descends (prefixWord ++ tailWord_631098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_631141 : List Nat := [1, 3, 1, 3, 1, 5, 1, 2, 1, 4]
def baseStart_631141 : Nat := 118140960795 + 631141 * 2 ^ 59
def prefixEnd_631141 : Nat := 4983230072969 + 3 ^ 40 * 631141 * 2
def baseEnd_631141 : Nat := 216052462506280261089961

theorem tailTrace_631141 : CollatzResearch.WordTrace tailWord_631141 prefixEnd_631141 216052462506280261089961 := by
  unfold tailWord_631141
  simp only [CollatzResearch.WordTrace]
  refine ⟨23019603406491422146285277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15346402270994281430856851 23019603406491422146285277)
  ·
    refine ⟨8632351277434283304856979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23019603406491422146285277 8632351277434283304856979)
    ·
      refine ⟨12948526916151424957285469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8632351277434283304856979 12948526916151424957285469)
      ·
        refine ⟨4855697593556784358982051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12948526916151424957285469 4855697593556784358982051)
        ·
          refine ⟨7283546390335176538473077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4855697593556784358982051 7283546390335176538473077)
          ·
            refine ⟨682832474093922800481851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 7283546390335176538473077 682832474093922800481851)
            ·
              refine ⟨1024248711140884200722777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 682832474093922800481851 1024248711140884200722777)
              ·
                refine ⟨768186533355663150542083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1024248711140884200722777 768186533355663150542083)
                ·
                  refine ⟨1152279800033494725813125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 768186533355663150542083 1152279800033494725813125)
                  ·
                    refine ⟨216052462506280261089961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1152279800033494725813125 216052462506280261089961)
                    ·
                      rfl

theorem cell22_631141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 5, 1, 2, 1, 4].length) (baseStart_631141 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_631141 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_631141 prefixEnd_631141 := by exact prefixLift 631141
  have htrace : WordTrace (prefixWord ++ tailWord_631141) baseStart_631141 baseEnd_631141 := by
    simpa [prefixWord, tailWord_631141, baseEnd_631141] using wordTrace_append hprefix tailTrace_631141
  have hstable : (prefixWord ++ tailWord_631141).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_631141).length < 2 ^ (prefixWord ++ tailWord_631141).sum := by decide
  have hdescent : baseEnd_631141 < baseStart_631141 := by decide
  rcases family_descends (prefixWord ++ tailWord_631141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_631154 : List Nat := [3, 2, 1, 2, 1, 4, 1, 2, 1, 5]
def baseStart_631154 : Nat := 118140960795 + 631154 * 2 ^ 59
def prefixEnd_631154 : Nat := 4983230072969 + 3 ^ 40 * 631154 * 2
def baseEnd_631154 : Nat := 216056912671952560514921

theorem tailTrace_631154 : CollatzResearch.WordTrace tailWord_631154 prefixEnd_631154 216056912671952560514921 := by
  unfold tailWord_631154
  simp only [CollatzResearch.WordTrace]
  refine ⟨5755019388861081341627129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15346718370296216911005677 5755019388861081341627129)
  ·
    refine ⟨4316264541645811006220347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5755019388861081341627129 4316264541645811006220347)
    ·
      refine ⟨6474396812468716509330521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4316264541645811006220347 6474396812468716509330521)
      ·
        refine ⟨4855797609351537381997891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6474396812468716509330521 4855797609351537381997891)
        ·
          refine ⟨7283696414027306072996837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4855797609351537381997891 7283696414027306072996837)
          ·
            refine ⟨1365693077630119888686907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7283696414027306072996837 1365693077630119888686907)
            ·
              refine ⟨2048539616445179833030361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1365693077630119888686907 2048539616445179833030361)
              ·
                refine ⟨1536404712333884874772771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2048539616445179833030361 1536404712333884874772771)
                ·
                  refine ⟨2304607068500827312159157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1536404712333884874772771 2304607068500827312159157)
                  ·
                    refine ⟨216056912671952560514921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2304607068500827312159157 216056912671952560514921)
                    ·
                      rfl

theorem cell22_631154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 1, 2, 1, 5].length) (baseStart_631154 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_631154 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_631154 prefixEnd_631154 := by exact prefixLift 631154
  have htrace : WordTrace (prefixWord ++ tailWord_631154) baseStart_631154 baseEnd_631154 := by
    simpa [prefixWord, tailWord_631154, baseEnd_631154] using wordTrace_append hprefix tailTrace_631154
  have hstable : (prefixWord ++ tailWord_631154).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_631154).length < 2 ^ (prefixWord ++ tailWord_631154).sum := by decide
  have hdescent : baseEnd_631154 < baseStart_631154 := by decide
  rcases family_descends (prefixWord ++ tailWord_631154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_631190 : List Nat := [5, 3, 1, 2, 1, 1, 1, 2, 6]
def baseStart_631190 : Nat := 118140960795 + 631190 * 2 ^ 59
def prefixEnd_631190 : Nat := 4983230072969 + 3 ^ 40 * 631190 * 2
def baseEnd_631190 : Nat := 72023078735886822204937

theorem tailTrace_631190 : CollatzResearch.WordTrace tailWord_631190 prefixEnd_631190 72023078735886822204937 := by
  unfold tailWord_631190
  simp only [CollatzResearch.WordTrace]
  refine ⟨1438836911457118969676189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 15347593722209269009879349 1438836911457118969676189)
  ·
    refine ⟨539563841796419613628571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1438836911457118969676189 539563841796419613628571)
    ·
      refine ⟨809345762694629420442857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 539563841796419613628571 809345762694629420442857)
      ·
        refine ⟨607009322020972065332143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 809345762694629420442857 607009322020972065332143)
        ·
          refine ⟨910513983031458097998215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 607009322020972065332143 910513983031458097998215)
          ·
            refine ⟨1365770974547187146997323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 910513983031458097998215 1365770974547187146997323)
            ·
              refine ⟨2048656461820780720495985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1365770974547187146997323 2048656461820780720495985)
              ·
                refine ⟨1536492346365585540371989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2048656461820780720495985 1536492346365585540371989)
                ·
                  refine ⟨72023078735886822204937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1536492346365585540371989 72023078735886822204937)
                  ·
                    rfl

theorem cell22_631190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 1, 2, 6].length) (baseStart_631190 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_631190 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_631190 prefixEnd_631190 := by exact prefixLift 631190
  have htrace : WordTrace (prefixWord ++ tailWord_631190) baseStart_631190 baseEnd_631190 := by
    simpa [prefixWord, tailWord_631190, baseEnd_631190] using wordTrace_append hprefix tailTrace_631190
  have hstable : (prefixWord ++ tailWord_631190).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_631190).length < 2 ^ (prefixWord ++ tailWord_631190).sum := by decide
  have hdescent : baseEnd_631190 < baseStart_631190 := by decide
  rcases family_descends (prefixWord ++ tailWord_631190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_631212 : List Nat := [2, 2, 1, 1, 1, 1, 3, 4, 7]
def baseStart_631212 : Nat := 118140960795 + 631212 * 2 ^ 59
def prefixEnd_631212 : Nat := 4983230072969 + 3 ^ 40 * 631212 * 2
def baseEnd_631212 : Nat := 72025589085753247521581

theorem tailTrace_631212 : CollatzResearch.WordTrace tailWord_631212 prefixEnd_631212 72025589085753247521581 := by
  unfold tailWord_631212
  simp only [CollatzResearch.WordTrace]
  refine ⟨11511096494617100636059945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15348128659489467514746593 11511096494617100636059945)
  ·
    refine ⟨8633322370962825477044959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11511096494617100636059945 8633322370962825477044959)
    ·
      refine ⟨12949983556444238215567439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8633322370962825477044959 12949983556444238215567439)
      ·
        refine ⟨19424975334666357323351159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12949983556444238215567439 19424975334666357323351159)
        ·
          refine ⟨29137463001999535985026739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19424975334666357323351159 29137463001999535985026739)
          ·
            refine ⟨43706194502999303977540109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29137463001999535985026739 43706194502999303977540109)
            ·
              refine ⟨16389822938624738991577541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43706194502999303977540109 16389822938624738991577541)
              ·
                refine ⟨3073091800992138560920789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16389822938624738991577541 3073091800992138560920789)
                ·
                  refine ⟨72025589085753247521581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3073091800992138560920789 72025589085753247521581)
                  ·
                    rfl

theorem cell22_631212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 7].length) (baseStart_631212 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_631212 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_631212 prefixEnd_631212 := by exact prefixLift 631212
  have htrace : WordTrace (prefixWord ++ tailWord_631212) baseStart_631212 baseEnd_631212 := by
    simpa [prefixWord, tailWord_631212, baseEnd_631212] using wordTrace_append hprefix tailTrace_631212
  have hstable : (prefixWord ++ tailWord_631212).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_631212).length < 2 ^ (prefixWord ++ tailWord_631212).sum := by decide
  have hdescent : baseEnd_631212 < baseStart_631212 := by decide
  rcases family_descends (prefixWord ++ tailWord_631212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_631229 : List Nat := [1, 4, 1, 2, 2, 3, 1, 1, 7]
def baseStart_631229 : Nat := 118140960795 + 631229 * 2 ^ 59
def prefixEnd_631229 : Nat := 4983230072969 + 3 ^ 40 * 631229 * 2
def baseEnd_631229 : Nat := 72027528901559121629897

theorem tailTrace_631229 : CollatzResearch.WordTrace tailWord_631229 prefixEnd_631229 72027528901559121629897 := by
  unfold tailWord_631229
  simp only [CollatzResearch.WordTrace]
  refine ⟨23022813030172613175488741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15348542020115075450325827 23022813030172613175488741)
  ·
    refine ⟨4316777443157364970404139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23022813030172613175488741 4316777443157364970404139)
    ·
      refine ⟨6475166164736047455606209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4316777443157364970404139 6475166164736047455606209)
      ·
        refine ⟨4856374623552035591704657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6475166164736047455606209 4856374623552035591704657)
        ·
          refine ⟨3642280967664026693778493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4856374623552035591704657 3642280967664026693778493)
          ·
            refine ⟨1365855362874010010166935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3642280967664026693778493 1365855362874010010166935)
            ·
              refine ⟨2048783044311015015250403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1365855362874010010166935 2048783044311015015250403)
              ·
                refine ⟨3073174566466522522875605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2048783044311015015250403 3073174566466522522875605)
                ·
                  refine ⟨72027528901559121629897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3073174566466522522875605 72027528901559121629897)
                  ·
                    rfl

theorem cell22_631229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 1, 1, 7].length) (baseStart_631229 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_631229 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_631229 prefixEnd_631229 := by exact prefixLift 631229
  have htrace : WordTrace (prefixWord ++ tailWord_631229) baseStart_631229 baseEnd_631229 := by
    simpa [prefixWord, tailWord_631229, baseEnd_631229] using wordTrace_append hprefix tailTrace_631229
  have hstable : (prefixWord ++ tailWord_631229).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_631229).length < 2 ^ (prefixWord ++ tailWord_631229).sum := by decide
  have hdescent : baseEnd_631229 < baseStart_631229 := by decide
  rcases family_descends (prefixWord ++ tailWord_631229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_631267 : List Nat := [1, 1, 1, 6, 4, 1, 1, 3, 1, 3]
def baseStart_631267 : Nat := 118140960795 + 631267 * 2 ^ 59
def prefixEnd_631267 : Nat := 4983230072969 + 3 ^ 40 * 631267 * 2
def baseEnd_631267 : Nat := 216095594881257932439575

theorem tailTrace_631267 : CollatzResearch.WordTrace tailWord_631267 prefixEnd_631267 216095594881257932439575 := by
  unfold tailWord_631267
  simp only [CollatzResearch.WordTrace]
  refine ⟨23024199004034945665372055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15349466002689963776914703 23024199004034945665372055)
  ·
    refine ⟨34536298506052418498058083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23024199004034945665372055 34536298506052418498058083)
    ·
      refine ⟨51804447759078627747087125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34536298506052418498058083 51804447759078627747087125)
      ·
        refine ⟨2428333488706810675644709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 51804447759078627747087125 2428333488706810675644709)
        ·
          refine ⟨455312529132527001683383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2428333488706810675644709 455312529132527001683383)
          ·
            refine ⟨682968793698790502525075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 455312529132527001683383 682968793698790502525075)
            ·
              refine ⟨1024453190548185753787613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 682968793698790502525075 1024453190548185753787613)
              ·
                refine ⟨384169946455569657670355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1024453190548185753787613 384169946455569657670355)
                ·
                  refine ⟨576254919683354486505533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 384169946455569657670355 576254919683354486505533)
                  ·
                    refine ⟨216095594881257932439575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 576254919683354486505533 216095594881257932439575)
                    ·
                      rfl

theorem cell22_631267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 4, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 4, 1, 1, 3, 1, 3].length) (baseStart_631267 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_631267 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_631267 prefixEnd_631267 := by exact prefixLift 631267
  have htrace : WordTrace (prefixWord ++ tailWord_631267) baseStart_631267 baseEnd_631267 := by
    simpa [prefixWord, tailWord_631267, baseEnd_631267] using wordTrace_append hprefix tailTrace_631267
  have hstable : (prefixWord ++ tailWord_631267).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_631267).length < 2 ^ (prefixWord ++ tailWord_631267).sum := by decide
  have hdescent : baseEnd_631267 < baseStart_631267 := by decide
  rcases family_descends (prefixWord ++ tailWord_631267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_631304 : List Nat := [2, 1, 3, 2, 1, 1, 1, 1, 6, 4]
def baseStart_631304 : Nat := 118140960795 + 631304 * 2 ^ 59
def prefixEnd_631304 : Nat := 4983230072969 + 3 ^ 40 * 631304 * 2
def baseEnd_631304 : Nat := 216108260737402169264461

theorem tailTrace_631304 : CollatzResearch.WordTrace tailWord_631304 prefixEnd_631304 216108260737402169264461 := by
  unfold tailWord_631304
  simp only [CollatzResearch.WordTrace]
  refine ⟨11512774252450450492234483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15350365669933933989645977 11512774252450450492234483)
  ·
    refine ⟨17269161378675675738351725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11512774252450450492234483 17269161378675675738351725)
    ·
      refine ⟨6475935517003378401881897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17269161378675675738351725 6475935517003378401881897)
      ·
        refine ⟨4856951637752533801411423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6475935517003378401881897 4856951637752533801411423)
        ·
          refine ⟨7285427456628800702117135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4856951637752533801411423 7285427456628800702117135)
          ·
            refine ⟨10928141184943201053175703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7285427456628800702117135 10928141184943201053175703)
            ·
              refine ⟨16392211777414801579763555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10928141184943201053175703 16392211777414801579763555)
              ·
                refine ⟨24588317666122202369645333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16392211777414801579763555 24588317666122202369645333)
                ·
                  refine ⟨1152577390599478236077125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 24588317666122202369645333 1152577390599478236077125)
                  ·
                    refine ⟨216108260737402169264461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1152577390599478236077125 216108260737402169264461)
                    ·
                      rfl

theorem cell22_631304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 1, 6, 4].length) (baseStart_631304 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_631304 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_631304 prefixEnd_631304 := by exact prefixLift 631304
  have htrace : WordTrace (prefixWord ++ tailWord_631304) baseStart_631304 baseEnd_631304 := by
    simpa [prefixWord, tailWord_631304, baseEnd_631304] using wordTrace_append hprefix tailTrace_631304
  have hstable : (prefixWord ++ tailWord_631304).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_631304).length < 2 ^ (prefixWord ++ tailWord_631304).sum := by decide
  have hdescent : baseEnd_631304 < baseStart_631304 := by decide
  rcases family_descends (prefixWord ++ tailWord_631304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_631342 : List Nat := [4, 1, 3, 1, 3, 2, 2, 2, 4]
def baseStart_631342 : Nat := 118140960795 + 631342 * 2 ^ 59
def prefixEnd_631342 : Nat := 4983230072969 + 3 ^ 40 * 631342 * 2
def baseEnd_631342 : Nat := 72040422971327578938115

theorem tailTrace_631342 : CollatzResearch.WordTrace tailWord_631342 prefixEnd_631342 72040422971327578938115 := by
  unfold tailWord_631342
  simp only [CollatzResearch.WordTrace]
  refine ⟨2878366809845404184294035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15351289652508822316234853 2878366809845404184294035)
  ·
    refine ⟨4317550214768106276441053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2878366809845404184294035 4317550214768106276441053)
    ·
      refine ⟨1619081330538039853665395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4317550214768106276441053 1619081330538039853665395)
      ·
        refine ⟨2428621995807059780498093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1619081330538039853665395 2428621995807059780498093)
        ·
          refine ⟨910733248427647417686785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2428621995807059780498093 910733248427647417686785)
          ·
            refine ⟨683049936320735563265089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 910733248427647417686785 683049936320735563265089)
            ·
              refine ⟨512287452240551672448817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 683049936320735563265089 512287452240551672448817)
              ·
                refine ⟨384215589180413754336613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 512287452240551672448817 384215589180413754336613)
                ·
                  refine ⟨72040422971327578938115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 384215589180413754336613 72040422971327578938115)
                  ·
                    rfl

theorem cell22_631342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 2, 2, 2, 4].length) (baseStart_631342 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_631342 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_631342 prefixEnd_631342 := by exact prefixLift 631342
  have htrace : WordTrace (prefixWord ++ tailWord_631342) baseStart_631342 baseEnd_631342 := by
    simpa [prefixWord, tailWord_631342, baseEnd_631342] using wordTrace_append hprefix tailTrace_631342
  have hstable : (prefixWord ++ tailWord_631342).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_631342).length < 2 ^ (prefixWord ++ tailWord_631342).sum := by decide
  have hdescent : baseEnd_631342 < baseStart_631342 := by decide
  rcases family_descends (prefixWord ++ tailWord_631342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_631349 : List Nat := [1, 3, 3, 1, 1, 2, 1, 1, 1, 8]
def baseStart_631349 : Nat := 118140960795 + 631349 * 2 ^ 59
def prefixEnd_631349 : Nat := 4983230072969 + 3 ^ 40 * 631349 * 2
def baseEnd_631349 : Nat := 216123665157037051889323

theorem tailTrace_631349 : CollatzResearch.WordTrace tailWord_631349 prefixEnd_631349 216123665157037051889323 := by
  unfold tailWord_631349
  simp only [CollatzResearch.WordTrace]
  refine ⟨23027189789737873669857101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15351459859825249113238067 23027189789737873669857101)
  ·
    refine ⟨8635196171151702626196413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23027189789737873669857101 8635196171151702626196413)
    ·
      refine ⟨3238198564181888484823655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8635196171151702626196413 3238198564181888484823655)
      ·
        refine ⟨4857297846272832727235483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3238198564181888484823655 4857297846272832727235483)
        ·
          refine ⟨7285946769409249090853225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4857297846272832727235483 7285946769409249090853225)
          ·
            refine ⟨5464460077056936818139919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7285946769409249090853225 5464460077056936818139919)
            ·
              refine ⟨8196690115585405227209879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5464460077056936818139919 8196690115585405227209879)
              ·
                refine ⟨12295035173378107840814819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8196690115585405227209879 12295035173378107840814819)
                ·
                  refine ⟨18442552760067161761222229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12295035173378107840814819 18442552760067161761222229)
                  ·
                    refine ⟨216123665157037051889323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 18442552760067161761222229 216123665157037051889323)
                    ·
                      rfl

theorem cell22_631349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 1, 1, 8].length) (baseStart_631349 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_631349 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_631349 prefixEnd_631349 := by exact prefixLift 631349
  have htrace : WordTrace (prefixWord ++ tailWord_631349) baseStart_631349 baseEnd_631349 := by
    simpa [prefixWord, tailWord_631349, baseEnd_631349] using wordTrace_append hprefix tailTrace_631349
  have hstable : (prefixWord ++ tailWord_631349).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_631349).length < 2 ^ (prefixWord ++ tailWord_631349).sum := by decide
  have hdescent : baseEnd_631349 < baseStart_631349 := by decide
  rcases family_descends (prefixWord ++ tailWord_631349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_631351 : List Nat := [1, 1, 3, 1, 2, 3, 2, 3, 3, 3]
def baseStart_631351 : Nat := 118140960795 + 631351 * 2 ^ 59
def prefixEnd_631351 : Nat := 4983230072969 + 3 ^ 40 * 631351 * 2
def baseEnd_631351 : Nat := 216124349797909713339317

theorem tailTrace_631351 : CollatzResearch.WordTrace tailWord_631351 prefixEnd_631351 216124349797909713339317 := by
  unfold tailWord_631351
  simp only [CollatzResearch.WordTrace]
  refine ⟨23027262735730628011429907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15351508490487085340953271 23027262735730628011429907)
  ·
    refine ⟨34540894103595942017144861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23027262735730628011429907 34540894103595942017144861)
    ·
      refine ⟨12952835288848478256429323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34540894103595942017144861 12952835288848478256429323)
      ·
        refine ⟨19429252933272717384643985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12952835288848478256429323 19429252933272717384643985)
        ·
          refine ⟨14571939699954538038482989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19429252933272717384643985 14571939699954538038482989)
          ·
            refine ⟨5464477387482951764431121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14571939699954538038482989 5464477387482951764431121)
            ·
              refine ⟨4098358040612213823323341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5464477387482951764431121 4098358040612213823323341)
              ·
                refine ⟨1536884265229580183746253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4098358040612213823323341 1536884265229580183746253)
                ·
                  refine ⟨576331599461092568904845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1536884265229580183746253 576331599461092568904845)
                  ·
                    refine ⟨216124349797909713339317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 576331599461092568904845 216124349797909713339317)
                    ·
                      rfl

theorem cell22_631351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 2, 3, 3, 3].length) (baseStart_631351 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_631351 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_631351 prefixEnd_631351 := by exact prefixLift 631351
  have htrace : WordTrace (prefixWord ++ tailWord_631351) baseStart_631351 baseEnd_631351 := by
    simpa [prefixWord, tailWord_631351, baseEnd_631351] using wordTrace_append hprefix tailTrace_631351
  have hstable : (prefixWord ++ tailWord_631351).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_631351).length < 2 ^ (prefixWord ++ tailWord_631351).sum := by decide
  have hdescent : baseEnd_631351 < baseStart_631351 := by decide
  rcases family_descends (prefixWord ++ tailWord_631351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_631428 : List Nat := [2, 3, 2, 1, 3, 1, 1, 4, 1, 4]
def baseStart_631428 : Nat := 118140960795 + 631428 * 2 ^ 59
def prefixEnd_631428 : Nat := 4983230072969 + 3 ^ 40 * 631428 * 2
def baseEnd_631428 : Nat := 216150708471507179164081

theorem tailTrace_631428 : CollatzResearch.WordTrace tailWord_631428 prefixEnd_631428 216150708471507179164081 := by
  unfold tailWord_631428
  simp only [CollatzResearch.WordTrace]
  refine ⟨11515035578225835080991469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15353380770967780107988625 11515035578225835080991469)
  ·
    refine ⟨4318138341834688155371801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11515035578225835080991469 4318138341834688155371801)
    ·
      refine ⟨3238603756376016116528851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4318138341834688155371801 3238603756376016116528851)
      ·
        refine ⟨4857905634564024174793277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3238603756376016116528851 4857905634564024174793277)
        ·
          refine ⟨1821714612961509065547479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4857905634564024174793277 1821714612961509065547479)
          ·
            refine ⟨2732571919442263598321219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1821714612961509065547479 2732571919442263598321219)
            ·
              refine ⟨4098857879163395397481829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2732571919442263598321219 4098857879163395397481829)
              ·
                refine ⟨768535852343136637027843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4098857879163395397481829 768535852343136637027843)
                ·
                  refine ⟨1152803778514704955541765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 768535852343136637027843 1152803778514704955541765)
                  ·
                    refine ⟨216150708471507179164081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1152803778514704955541765 216150708471507179164081)
                    ·
                      rfl

theorem cell22_631428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 1, 4, 1, 4].length) (baseStart_631428 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_631428 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_631428 prefixEnd_631428 := by exact prefixLift 631428
  have htrace : WordTrace (prefixWord ++ tailWord_631428) baseStart_631428 baseEnd_631428 := by
    simpa [prefixWord, tailWord_631428, baseEnd_631428] using wordTrace_append hprefix tailTrace_631428
  have hstable : (prefixWord ++ tailWord_631428).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_631428).length < 2 ^ (prefixWord ++ tailWord_631428).sum := by decide
  have hdescent : baseEnd_631428 < baseStart_631428 := by decide
  rcases family_descends (prefixWord ++ tailWord_631428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_631460 : List Nat := [2, 3, 1, 2, 2, 1, 5, 2, 4]
def baseStart_631460 : Nat := 118140960795 + 631460 * 2 ^ 59
def prefixEnd_631460 : Nat := 4983230072969 + 3 ^ 40 * 631460 * 2
def baseEnd_631460 : Nat := 72053887575156587454661

theorem tailTrace_631460 : CollatzResearch.WordTrace tailWord_631460 prefixEnd_631460 72053887575156587454661 := by
  unfold tailWord_631460
  simp only [CollatzResearch.WordTrace]
  refine ⟨11515619146167869813573917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15354158861557159751431889 11515619146167869813573917)
  ·
    refine ⟨4318357179812951180090219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11515619146167869813573917 4318357179812951180090219)
    ·
      refine ⟨6477535769719426770135329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4318357179812951180090219 6477535769719426770135329)
      ·
        refine ⟨4858151827289570077601497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6477535769719426770135329 4858151827289570077601497)
        ·
          refine ⟨3643613870467177558201123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4858151827289570077601497 3643613870467177558201123)
          ·
            refine ⟨5465420805700766337301685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3643613870467177558201123 5465420805700766337301685)
            ·
              refine ⟨512383200534446844122033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5465420805700766337301685 512383200534446844122033)
              ·
                refine ⟨384287400400835133091525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 512383200534446844122033 384287400400835133091525)
                ·
                  refine ⟨72053887575156587454661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 384287400400835133091525 72053887575156587454661)
                  ·
                    rfl

theorem cell22_631460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 5, 2, 4].length) (baseStart_631460 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_631460 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_631460 prefixEnd_631460 := by exact prefixLift 631460
  have htrace : WordTrace (prefixWord ++ tailWord_631460) baseStart_631460 baseEnd_631460 := by
    simpa [prefixWord, tailWord_631460, baseEnd_631460] using wordTrace_append hprefix tailTrace_631460
  have hstable : (prefixWord ++ tailWord_631460).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_631460).length < 2 ^ (prefixWord ++ tailWord_631460).sum := by decide
  have hdescent : baseEnd_631460 < baseStart_631460 := by decide
  rcases family_descends (prefixWord ++ tailWord_631460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_631471 : List Nat := [1, 1, 2, 1, 2, 6, 2, 7]
def baseStart_631471 : Nat := 118140960795 + 631471 * 2 ^ 59
def prefixEnd_631471 : Nat := 4983230072969 + 3 ^ 40 * 631471 * 2
def baseEnd_631471 : Nat := 24018380916696600037661

theorem tailTrace_631471 : CollatzResearch.WordTrace tailWord_631471 prefixEnd_631471 24018380916696600037661 := by
  unfold tailWord_631471
  simp only [CollatzResearch.WordTrace]
  refine ⟨23031639495295888505798267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15354426330197259003865511 23031639495295888505798267)
  ·
    refine ⟨34547459242943832758697401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23031639495295888505798267 34547459242943832758697401)
    ·
      refine ⟨25910594432207874569023051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34547459242943832758697401 25910594432207874569023051)
      ·
        refine ⟨38865891648311811853534577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25910594432207874569023051 38865891648311811853534577)
        ·
          refine ⟨29149418736233858890150933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38865891648311811853534577 29149418736233858890150933)
          ·
            refine ⟨1366379003260962135475825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 29149418736233858890150933 1366379003260962135475825)
            ·
              refine ⟨1024784252445721601606869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1366379003260962135475825 1024784252445721601606869)
              ·
                refine ⟨24018380916696600037661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1024784252445721601606869 24018380916696600037661)
                ·
                  rfl

theorem cell22_631471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 2, 7].length) (baseStart_631471 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_631471 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_631471 prefixEnd_631471 := by exact prefixLift 631471
  have htrace : WordTrace (prefixWord ++ tailWord_631471) baseStart_631471 baseEnd_631471 := by
    simpa [prefixWord, tailWord_631471, baseEnd_631471] using wordTrace_append hprefix tailTrace_631471
  have hstable : (prefixWord ++ tailWord_631471).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_631471).length < 2 ^ (prefixWord ++ tailWord_631471).sum := by decide
  have hdescent : baseEnd_631471 < baseStart_631471 := by decide
  rcases family_descends (prefixWord ++ tailWord_631471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_631475 : List Nat := [1, 1, 1, 2, 3, 4, 4, 1, 2, 3]
def baseStart_631475 : Nat := 118140960795 + 631475 * 2 ^ 59
def prefixEnd_631475 : Nat := 4983230072969 + 3 ^ 40 * 631475 * 2
def baseEnd_631475 : Nat := 216166797532014723238937

theorem tailTrace_631475 : CollatzResearch.WordTrace tailWord_631475 prefixEnd_631475 216166797532014723238937 := by
  unfold tailWord_631475
  simp only [CollatzResearch.WordTrace]
  refine ⟨23031785387281397188943879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15354523591520931459295919 23031785387281397188943879)
  ·
    refine ⟨34547678080922095783415819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23031785387281397188943879 34547678080922095783415819)
    ·
      refine ⟨51821517121383143675123729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34547678080922095783415819 51821517121383143675123729)
      ·
        refine ⟨38866137841037357756342797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51821517121383143675123729 38866137841037357756342797)
        ·
          refine ⟨14574801690389009158628549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38866137841037357756342797 14574801690389009158628549)
          ·
            refine ⟨2732775316947939217242853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14574801690389009158628549 2732775316947939217242853)
            ·
              refine ⟨512395371927738603233035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2732775316947939217242853 512395371927738603233035)
              ·
                refine ⟨768593057891607904849553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 512395371927738603233035 768593057891607904849553)
                ·
                  refine ⟨576444793418705928637165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 768593057891607904849553 576444793418705928637165)
                  ·
                    refine ⟨216166797532014723238937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 576444793418705928637165 216166797532014723238937)
                    ·
                      rfl

theorem cell22_631475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 4, 1, 2, 3].length) (baseStart_631475 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_631475 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_631475 prefixEnd_631475 := by exact prefixLift 631475
  have htrace : WordTrace (prefixWord ++ tailWord_631475) baseStart_631475 baseEnd_631475 := by
    simpa [prefixWord, tailWord_631475, baseEnd_631475] using wordTrace_append hprefix tailTrace_631475
  have hstable : (prefixWord ++ tailWord_631475).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_631475).length < 2 ^ (prefixWord ++ tailWord_631475).sum := by decide
  have hdescent : baseEnd_631475 < baseStart_631475 := by decide
  rcases family_descends (prefixWord ++ tailWord_631475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_631533 : List Nat := [1, 5, 1, 2, 1, 1, 1, 5, 5]
def baseStart_631533 : Nat := 118140960795 + 631533 * 2 ^ 59
def prefixEnd_631533 : Nat := 4983230072969 + 3 ^ 40 * 631533 * 2
def baseEnd_631533 : Nat := 72062217372440635096253

theorem tailTrace_631533 : CollatzResearch.WordTrace tailWord_631533 prefixEnd_631533 72062217372440635096253 := by
  unfold tailWord_631533
  simp only [CollatzResearch.WordTrace]
  refine ⟨23033900821071273094555253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15355933880714182063036835 23033900821071273094555253)
  ·
    refine ⟨2159428201975431852614555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 23033900821071273094555253 2159428201975431852614555)
    ·
      refine ⟨3239142302963147778921833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2159428201975431852614555 3239142302963147778921833)
      ·
        refine ⟨2429356727222360834191375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3239142302963147778921833 2429356727222360834191375)
        ·
          refine ⟨3644035090833541251287063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2429356727222360834191375 3644035090833541251287063)
          ·
            refine ⟨5466052636250311876930595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3644035090833541251287063 5466052636250311876930595)
            ·
              refine ⟨8199078954375467815395893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5466052636250311876930595 8199078954375467815395893)
              ·
                refine ⟨768663651972700107693365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8199078954375467815395893 768663651972700107693365)
                ·
                  refine ⟨72062217372440635096253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 768663651972700107693365 72062217372440635096253)
                  ·
                    rfl

theorem cell22_631533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 5, 5].length) (baseStart_631533 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_631533 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_631533 prefixEnd_631533 := by exact prefixLift 631533
  have htrace : WordTrace (prefixWord ++ tailWord_631533) baseStart_631533 baseEnd_631533 := by
    simpa [prefixWord, tailWord_631533, baseEnd_631533] using wordTrace_append hprefix tailTrace_631533
  have hstable : (prefixWord ++ tailWord_631533).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_631533).length < 2 ^ (prefixWord ++ tailWord_631533).sum := by decide
  have hdescent : baseEnd_631533 < baseStart_631533 := by decide
  rcases family_descends (prefixWord ++ tailWord_631533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_631541 : List Nat := [1, 3, 6, 1, 2, 1, 1, 1, 2, 4]
def baseStart_631541 : Nat := 118140960795 + 631541 * 2 ^ 59
def prefixEnd_631541 : Nat := 4983230072969 + 3 ^ 40 * 631541 * 2
def baseEnd_631541 : Nat := 216189390680812551088735

theorem tailTrace_631541 : CollatzResearch.WordTrace tailWord_631541 prefixEnd_631541 216189390680812551088735 := by
  unfold tailWord_631541
  simp only [CollatzResearch.WordTrace]
  refine ⟨23034192605042290460846477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15356128403361526973897651 23034192605042290460846477)
  ·
    refine ⟨8637822226890858922817429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23034192605042290460846477 8637822226890858922817429)
    ·
      refine ⟨404897916885509012007067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 8637822226890858922817429 404897916885509012007067)
      ·
        refine ⟨607346875328263518010601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 404897916885509012007067 607346875328263518010601)
        ·
          refine ⟨455510156496197638507951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 607346875328263518010601 455510156496197638507951)
          ·
            refine ⟨683265234744296457761927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 455510156496197638507951 683265234744296457761927)
            ·
              refine ⟨1024897852116444686642891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 683265234744296457761927 1024897852116444686642891)
              ·
                refine ⟨1537346778174667029964337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1024897852116444686642891 1537346778174667029964337)
                ·
                  refine ⟨1153010083631000272473253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1537346778174667029964337 1153010083631000272473253)
                  ·
                    refine ⟨216189390680812551088735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1153010083631000272473253 216189390680812551088735)
                    ·
                      rfl

theorem cell22_631541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 2, 1, 1, 1, 2, 4].length) (baseStart_631541 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_631541 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_631541 prefixEnd_631541 := by exact prefixLift 631541
  have htrace : WordTrace (prefixWord ++ tailWord_631541) baseStart_631541 baseEnd_631541 := by
    simpa [prefixWord, tailWord_631541, baseEnd_631541] using wordTrace_append hprefix tailTrace_631541
  have hstable : (prefixWord ++ tailWord_631541).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_631541).length < 2 ^ (prefixWord ++ tailWord_631541).sum := by decide
  have hdescent : baseEnd_631541 < baseStart_631541 := by decide
  rcases family_descends (prefixWord ++ tailWord_631541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_631554 : List Nat := [3, 4, 1, 1, 1, 3, 2, 3, 1, 3]
def baseStart_631554 : Nat := 118140960795 + 631554 * 2 ^ 59
def prefixEnd_631554 : Nat := 4983230072969 + 3 ^ 40 * 631554 * 2
def baseEnd_631554 : Nat := 216193840846484850513695

theorem tailTrace_631554 : CollatzResearch.WordTrace tailWord_631554 prefixEnd_631554 216193840846484850513695 := by
  unfold tailWord_631554
  simp only [CollatzResearch.WordTrace]
  refine ⟨5758666688498798420267429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15356444502663462454046477 5758666688498798420267429)
  ·
    refine ⟨1079750004093524703800143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5758666688498798420267429 1079750004093524703800143)
    ·
      refine ⟨1619625006140287055700215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1079750004093524703800143 1619625006140287055700215)
      ·
        refine ⟨2429437509210430583550323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1619625006140287055700215 2429437509210430583550323)
        ·
          refine ⟨3644156263815645875325485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2429437509210430583550323 3644156263815645875325485)
          ·
            refine ⟨1366558598930867203247057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3644156263815645875325485 1366558598930867203247057)
            ·
              refine ⟨1024918949198150402435293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1366558598930867203247057 1024918949198150402435293)
              ·
                refine ⟨384344605949306400913235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1024918949198150402435293 384344605949306400913235)
                ·
                  refine ⟨576516908923959601369853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 384344605949306400913235 576516908923959601369853)
                  ·
                    refine ⟨216193840846484850513695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 576516908923959601369853 216193840846484850513695)
                    ·
                      rfl

theorem cell22_631554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 2, 3, 1, 3].length) (baseStart_631554 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_631554 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_631554 prefixEnd_631554 := by exact prefixLift 631554
  have htrace : WordTrace (prefixWord ++ tailWord_631554) baseStart_631554 baseEnd_631554 := by
    simpa [prefixWord, tailWord_631554, baseEnd_631554] using wordTrace_append hprefix tailTrace_631554
  have hstable : (prefixWord ++ tailWord_631554).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_631554).length < 2 ^ (prefixWord ++ tailWord_631554).sum := by decide
  have hdescent : baseEnd_631554 < baseStart_631554 := by decide
  rcases family_descends (prefixWord ++ tailWord_631554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_631578 : List Nat := [3, 1, 1, 3, 2, 1, 4, 1, 6]
def baseStart_631578 : Nat := 118140960795 + 631578 * 2 ^ 59
def prefixEnd_631578 : Nat := 4983230072969 + 3 ^ 40 * 631578 * 2
def baseEnd_631578 : Nat := 72067352178985595971207

theorem tailTrace_631578 : CollatzResearch.WordTrace tailWord_631578 prefixEnd_631578 72067352178985595971207 := by
  unfold tailWord_631578
  simp only [CollatzResearch.WordTrace]
  refine ⟨5758885526477061444985847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15357028070605497186628925 5758885526477061444985847)
  ·
    refine ⟨8638328289715592167478771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5758885526477061444985847 8638328289715592167478771)
    ·
      refine ⟨12957492434573388251218157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8638328289715592167478771 12957492434573388251218157)
      ·
        refine ⟨4859059662965020594206809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12957492434573388251218157 4859059662965020594206809)
        ·
          refine ⟨3644294747223765445655107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4859059662965020594206809 3644294747223765445655107)
          ·
            refine ⟨5466442120835648168482661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3644294747223765445655107 5466442120835648168482661)
            ·
              refine ⟨1024957897656684031590499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5466442120835648168482661 1024957897656684031590499)
              ·
                refine ⟨1537436846485026047385749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1024957897656684031590499 1537436846485026047385749)
                ·
                  refine ⟨72067352178985595971207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1537436846485026047385749 72067352178985595971207)
                  ·
                    rfl

theorem cell22_631578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 4, 1, 6].length) (baseStart_631578 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_631578 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_631578 prefixEnd_631578 := by exact prefixLift 631578
  have htrace : WordTrace (prefixWord ++ tailWord_631578) baseStart_631578 baseEnd_631578 := by
    simpa [prefixWord, tailWord_631578, baseEnd_631578] using wordTrace_append hprefix tailTrace_631578
  have hstable : (prefixWord ++ tailWord_631578).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_631578).length < 2 ^ (prefixWord ++ tailWord_631578).sum := by decide
  have hdescent : baseEnd_631578 < baseStart_631578 := by decide
  rcases family_descends (prefixWord ++ tailWord_631578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_631608 : List Nat := [2, 1, 2, 1, 3, 2, 2, 3, 2, 4]
def baseStart_631608 : Nat := 118140960795 + 631608 * 2 ^ 59
def prefixEnd_631608 : Nat := 4983230072969 + 3 ^ 40 * 631608 * 2
def baseEnd_631608 : Nat := 216212326150046709663529

theorem tailTrace_631608 : CollatzResearch.WordTrace tailWord_631608 prefixEnd_631608 216212326150046709663529 := by
  unfold tailWord_631608
  simp only [CollatzResearch.WordTrace]
  refine ⟨11518318147899780451767739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15357757530533040602356985 11518318147899780451767739)
  ·
    refine ⟨17277477221849670677651609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11518318147899780451767739 17277477221849670677651609)
    ·
      refine ⟨12958107916387253008238707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17277477221849670677651609 12958107916387253008238707)
      ·
        refine ⟨19437161874580879512358061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12958107916387253008238707 19437161874580879512358061)
        ·
          refine ⟨7288935702967829817134273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19437161874580879512358061 7288935702967829817134273)
          ·
            refine ⟨5466701777225872362850705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7288935702967829817134273 5466701777225872362850705)
            ·
              refine ⟨4100026332919404272138029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5466701777225872362850705 4100026332919404272138029)
              ·
                refine ⟨1537509874844776602051761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4100026332919404272138029 1537509874844776602051761)
                ·
                  refine ⟨1153132406133582451538821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1537509874844776602051761 1153132406133582451538821)
                  ·
                    refine ⟨216212326150046709663529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1153132406133582451538821 216212326150046709663529)
                    ·
                      rfl

theorem cell22_631608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 2, 3, 2, 4].length) (baseStart_631608 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_631608 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_631608 prefixEnd_631608 := by exact prefixLift 631608
  have htrace : WordTrace (prefixWord ++ tailWord_631608) baseStart_631608 baseEnd_631608 := by
    simpa [prefixWord, tailWord_631608, baseEnd_631608] using wordTrace_append hprefix tailTrace_631608
  have hstable : (prefixWord ++ tailWord_631608).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_631608).length < 2 ^ (prefixWord ++ tailWord_631608).sum := by decide
  have hdescent : baseEnd_631608 < baseStart_631608 := by decide
  rcases family_descends (prefixWord ++ tailWord_631608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_631629 : List Nat := [1, 6, 1, 2, 3, 1, 1, 1, 6]
def baseStart_631629 : Nat := 118140960795 + 631629 * 2 ^ 59
def prefixEnd_631629 : Nat := 4983230072969 + 3 ^ 40 * 631629 * 2
def baseEnd_631629 : Nat := 72073171626403218296155

theorem tailTrace_631629 : CollatzResearch.WordTrace tailWord_631629 prefixEnd_631629 72073171626403218296155 := by
  unfold tailWord_631629
  simp only [CollatzResearch.WordTrace]
  refine ⟨23037402228723481490049941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15358268152482320993366627 23037402228723481490049941)
  ·
    refine ⟨1079878229471413194846091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 23037402228723481490049941 1079878229471413194846091)
    ·
      refine ⟨1619817344207119792269137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1079878229471413194846091 1619817344207119792269137)
      ·
        refine ⟨1214863008155339844201853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1619817344207119792269137 1214863008155339844201853)
        ·
          refine ⟨455573628058252441575695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1214863008155339844201853 455573628058252441575695)
          ·
            refine ⟨683360442087378662363543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 455573628058252441575695 683360442087378662363543)
            ·
              refine ⟨1025040663131067993545315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 683360442087378662363543 1025040663131067993545315)
              ·
                refine ⟨1537560994696601990317973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1025040663131067993545315 1537560994696601990317973)
                ·
                  refine ⟨72073171626403218296155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1537560994696601990317973 72073171626403218296155)
                  ·
                    rfl

theorem cell22_631629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 3, 1, 1, 1, 6].length) (baseStart_631629 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_631629 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_631629 prefixEnd_631629 := by exact prefixLift 631629
  have htrace : WordTrace (prefixWord ++ tailWord_631629) baseStart_631629 baseEnd_631629 := by
    simpa [prefixWord, tailWord_631629, baseEnd_631629] using wordTrace_append hprefix tailTrace_631629
  have hstable : (prefixWord ++ tailWord_631629).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_631629).length < 2 ^ (prefixWord ++ tailWord_631629).sum := by decide
  have hdescent : baseEnd_631629 < baseStart_631629 := by decide
  rcases family_descends (prefixWord ++ tailWord_631629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_631644 : List Nat := [2, 2, 4, 2, 1, 1, 4, 1, 2, 3]
def baseStart_631644 : Nat := 118140960795 + 631644 * 2 ^ 59
def prefixEnd_631644 : Nat := 4983230072969 + 3 ^ 40 * 631644 * 2
def baseEnd_631644 : Nat := 216224649685754615763419

theorem tailTrace_631644 : CollatzResearch.WordTrace tailWord_631644 prefixEnd_631644 216224649685754615763419 := by
  unfold tailWord_631644
  simp only [CollatzResearch.WordTrace]
  refine ⟨11518974661834569525922993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15358632882446092701230657 11518974661834569525922993)
  ·
    refine ⟨8639230996375927144442245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11518974661834569525922993 8639230996375927144442245)
    ·
      refine ⟨1619855811820486339582921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8639230996375927144442245 1619855811820486339582921)
      ·
        refine ⟨1214891858865364754687191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1619855811820486339582921 1214891858865364754687191)
        ·
          refine ⟨1822337788298047132030787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1214891858865364754687191 1822337788298047132030787)
          ·
            refine ⟨2733506682447070698046181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1822337788298047132030787 2733506682447070698046181)
            ·
              refine ⟨512532502958825755883659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2733506682447070698046181 512532502958825755883659)
              ·
                refine ⟨768798754438238633825489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 512532502958825755883659 768798754438238633825489)
                ·
                  refine ⟨576599065828678975369117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 768798754438238633825489 576599065828678975369117)
                  ·
                    refine ⟨216224649685754615763419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 576599065828678975369117 216224649685754615763419)
                    ·
                      rfl

theorem cell22_631644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 4, 1, 2, 3].length) (baseStart_631644 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_631644 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_631644 prefixEnd_631644 := by exact prefixLift 631644
  have htrace : WordTrace (prefixWord ++ tailWord_631644) baseStart_631644 baseEnd_631644 := by
    simpa [prefixWord, tailWord_631644, baseEnd_631644] using wordTrace_append hprefix tailTrace_631644
  have hstable : (prefixWord ++ tailWord_631644).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_631644).length < 2 ^ (prefixWord ++ tailWord_631644).sum := by decide
  have hdescent : baseEnd_631644 < baseStart_631644 := by decide
  rcases family_descends (prefixWord ++ tailWord_631644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_631683 : List Nat := [1, 1, 1, 3, 4, 1, 2, 2, 2, 5]
def baseStart_631683 : Nat := 118140960795 + 631683 * 2 ^ 59
def prefixEnd_631683 : Nat := 4983230072969 + 3 ^ 40 * 631683 * 2
def baseEnd_631683 : Nat := 216238000182771514038299

theorem tailTrace_631683 : CollatzResearch.WordTrace tailWord_631683 prefixEnd_631683 216238000182771514038299 := by
  unfold tailWord_631683
  simp only [CollatzResearch.WordTrace]
  refine ⟨23039371770527848712515703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15359581180351899141677135 23039371770527848712515703)
  ·
    refine ⟨34559057655791773068773555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23039371770527848712515703 34559057655791773068773555)
    ·
      refine ⟨51838586483687659603160333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34559057655791773068773555 51838586483687659603160333)
      ·
        refine ⟨19439469931382872351185125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51838586483687659603160333 19439469931382872351185125)
        ·
          refine ⟨3644900612134288565847211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19439469931382872351185125 3644900612134288565847211)
          ·
            refine ⟨5467350918201432848770817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3644900612134288565847211 5467350918201432848770817)
            ·
              refine ⟨4100513188651074636578113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5467350918201432848770817 4100513188651074636578113)
              ·
                refine ⟨3075384891488305977433585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4100513188651074636578113 3075384891488305977433585)
                ·
                  refine ⟨2306538668616229483075189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3075384891488305977433585 2306538668616229483075189)
                  ·
                    refine ⟨216238000182771514038299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2306538668616229483075189 216238000182771514038299)
                    ·
                      rfl

theorem cell22_631683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 2, 2, 2, 5].length) (baseStart_631683 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_631683 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_631683 prefixEnd_631683 := by exact prefixLift 631683
  have htrace : WordTrace (prefixWord ++ tailWord_631683) baseStart_631683 baseEnd_631683 := by
    simpa [prefixWord, tailWord_631683, baseEnd_631683] using wordTrace_append hprefix tailTrace_631683
  have hstable : (prefixWord ++ tailWord_631683).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_631683).length < 2 ^ (prefixWord ++ tailWord_631683).sum := by decide
  have hdescent : baseEnd_631683 < baseStart_631683 := by decide
  rcases family_descends (prefixWord ++ tailWord_631683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_631685 : List Nat := [1, 3, 1, 1, 3, 4, 2, 2, 5]
def baseStart_631685 : Nat := 118140960795 + 631685 * 2 ^ 59
def prefixEnd_631685 : Nat := 4983230072969 + 3 ^ 40 * 631685 * 2
def baseEnd_631685 : Nat := 72079561607881391829431

theorem tailTrace_631685 : CollatzResearch.WordTrace tailWord_631685 prefixEnd_631685 72079561607881391829431 := by
  unfold tailWord_631685
  simp only [CollatzResearch.WordTrace]
  refine ⟨23039444716520603054088509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15359629811013735369392339 23039444716520603054088509)
  ·
    refine ⟨8639791768695226145283191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23039444716520603054088509 8639791768695226145283191)
    ·
      refine ⟨12959687653042839217924787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8639791768695226145283191 12959687653042839217924787)
      ·
        refine ⟨19439531479564258826887181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12959687653042839217924787 19439531479564258826887181)
        ·
          refine ⟨7289824304836597060082693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19439531479564258826887181 7289824304836597060082693)
          ·
            refine ⟨1366842057156861948765505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7289824304836597060082693 1366842057156861948765505)
            ·
              refine ⟨1025131542867646461574129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1366842057156861948765505 1025131542867646461574129)
              ·
                refine ⟨768848657150734846180597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1025131542867646461574129 768848657150734846180597)
                ·
                  refine ⟨72079561607881391829431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 768848657150734846180597 72079561607881391829431)
                  ·
                    rfl

theorem cell22_631685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 2, 2, 5].length) (baseStart_631685 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_631685 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_631685 prefixEnd_631685 := by exact prefixLift 631685
  have htrace : WordTrace (prefixWord ++ tailWord_631685) baseStart_631685 baseEnd_631685 := by
    simpa [prefixWord, tailWord_631685, baseEnd_631685] using wordTrace_append hprefix tailTrace_631685
  have hstable : (prefixWord ++ tailWord_631685).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_631685).length < 2 ^ (prefixWord ++ tailWord_631685).sum := by decide
  have hdescent : baseEnd_631685 < baseStart_631685 := by decide
  rcases family_descends (prefixWord ++ tailWord_631685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_631689 : List Nat := [1, 2, 1, 1, 5, 2, 4, 2, 1, 3]
def baseStart_631689 : Nat := 118140960795 + 631689 * 2 ^ 59
def prefixEnd_631689 : Nat := 4983230072969 + 3 ^ 40 * 631689 * 2
def baseEnd_631689 : Nat := 216240054105389498388281

theorem tailTrace_631689 : CollatzResearch.WordTrace tailWord_631689 prefixEnd_631689 216240054105389498388281 := by
  unfold tailWord_631689
  simp only [CollatzResearch.WordTrace]
  refine ⟨23039590608506111737234121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15359727072337407824822747 23039590608506111737234121)
  ·
    refine ⟨17279692956379583802925591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23039590608506111737234121 17279692956379583802925591)
    ·
      refine ⟨25919539434569375704388387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17279692956379583802925591 25919539434569375704388387)
      ·
        refine ⟨38879309151854063556582581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25919539434569375704388387 38879309151854063556582581)
        ·
          refine ⟨3644935232986318458429617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 38879309151854063556582581 3644935232986318458429617)
          ·
            refine ⟨2733701424739738843822213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3644935232986318458429617 2733701424739738843822213)
            ·
              refine ⟨512569017138701033216665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2733701424739738843822213 512569017138701033216665)
              ·
                refine ⟨384426762854025774912499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 512569017138701033216665 384426762854025774912499)
                ·
                  refine ⟨576640144281038662368749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 384426762854025774912499 576640144281038662368749)
                  ·
                    refine ⟨216240054105389498388281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 576640144281038662368749 216240054105389498388281)
                    ·
                      rfl

theorem cell22_631689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 4, 2, 1, 3].length) (baseStart_631689 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_631689 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_631689 prefixEnd_631689 := by exact prefixLift 631689
  have htrace : WordTrace (prefixWord ++ tailWord_631689) baseStart_631689 baseEnd_631689 := by
    simpa [prefixWord, tailWord_631689, baseEnd_631689] using wordTrace_append hprefix tailTrace_631689
  have hstable : (prefixWord ++ tailWord_631689).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_631689).length < 2 ^ (prefixWord ++ tailWord_631689).sum := by decide
  have hdescent : baseEnd_631689 < baseStart_631689 := by decide
  rcases family_descends (prefixWord ++ tailWord_631689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_631700 : List Nat := [2, 4, 2, 1, 1, 1, 3, 1, 2, 5]
def baseStart_631700 : Nat := 118140960795 + 631700 * 2 ^ 59
def prefixEnd_631700 : Nat := 4983230072969 + 3 ^ 40 * 631700 * 2
def baseEnd_631700 : Nat := 216243819630189136363247

theorem tailTrace_631700 : CollatzResearch.WordTrace tailWord_631700 prefixEnd_631700 216243819630189136363247 := by
  unfold tailWord_631700
  simp only [CollatzResearch.WordTrace]
  refine ⟨11519995905733130307942277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15359994540977507077256369 11519995905733130307942277)
  ·
    refine ⟨2159999232324961932739177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11519995905733130307942277 2159999232324961932739177)
    ·
      refine ⟨1619999424243721449554383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2159999232324961932739177 1619999424243721449554383)
      ·
        refine ⟨2429999136365582174331575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1619999424243721449554383 2429999136365582174331575)
        ·
          refine ⟨3644998704548373261497363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2429999136365582174331575 3644998704548373261497363)
          ·
            refine ⟨5467498056822559892246045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3644998704548373261497363 5467498056822559892246045)
            ·
              refine ⟨2050311771308459959592267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5467498056822559892246045 2050311771308459959592267)
              ·
                refine ⟨3075467656962689939388401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2050311771308459959592267 3075467656962689939388401)
                ·
                  refine ⟨2306600742722017454541301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3075467656962689939388401 2306600742722017454541301)
                  ·
                    refine ⟨216243819630189136363247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2306600742722017454541301 216243819630189136363247)
                    ·
                      rfl

theorem cell22_631700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 3, 1, 2, 5].length) (baseStart_631700 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_631700 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_631700 prefixEnd_631700 := by exact prefixLift 631700
  have htrace : WordTrace (prefixWord ++ tailWord_631700) baseStart_631700 baseEnd_631700 := by
    simpa [prefixWord, tailWord_631700, baseEnd_631700] using wordTrace_append hprefix tailTrace_631700
  have hstable : (prefixWord ++ tailWord_631700).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_631700).length < 2 ^ (prefixWord ++ tailWord_631700).sum := by decide
  have hdescent : baseEnd_631700 < baseStart_631700 := by decide
  rcases family_descends (prefixWord ++ tailWord_631700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_631762 : List Nat := [3, 2, 2, 3, 1, 1, 3, 1, 1, 5]
def baseStart_631762 : Nat := 118140960795 + 631762 * 2 ^ 59
def prefixEnd_631762 : Nat := 4983230072969 + 3 ^ 40 * 631762 * 2
def baseEnd_631762 : Nat := 216265043497241641313057

theorem tailTrace_631762 : CollatzResearch.WordTrace tailWord_631762 prefixEnd_631762 216265043497241641313057 := by
  unfold tailWord_631762
  simp only [CollatzResearch.WordTrace]
  refine ⟨5760563284310411301160385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15361502091494430136427693 5760563284310411301160385)
  ·
    refine ⟨4320422463232808475870289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5760563284310411301160385 4320422463232808475870289)
    ·
      refine ⟨3240316847424606356902717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4320422463232808475870289 3240316847424606356902717)
      ·
        refine ⟨1215118817784227383838519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3240316847424606356902717 1215118817784227383838519)
        ·
          refine ⟨1822678226676341075757779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1215118817784227383838519 1822678226676341075757779)
          ·
            refine ⟨2734017340014511613636669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1822678226676341075757779 2734017340014511613636669)
            ·
              refine ⟨1025256502505441855113751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2734017340014511613636669 1025256502505441855113751)
              ·
                refine ⟨1537884753758162782670627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1025256502505441855113751 1537884753758162782670627)
                ·
                  refine ⟨2306827130637244174005941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1537884753758162782670627 2306827130637244174005941)
                  ·
                    refine ⟨216265043497241641313057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2306827130637244174005941 216265043497241641313057)
                    ·
                      rfl

theorem cell22_631762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 3, 1, 1, 5].length) (baseStart_631762 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_631762 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_631762 prefixEnd_631762 := by exact prefixLift 631762
  have htrace : WordTrace (prefixWord ++ tailWord_631762) baseStart_631762 baseEnd_631762 := by
    simpa [prefixWord, tailWord_631762, baseEnd_631762] using wordTrace_append hprefix tailTrace_631762
  have hstable : (prefixWord ++ tailWord_631762).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_631762).length < 2 ^ (prefixWord ++ tailWord_631762).sum := by decide
  have hdescent : baseEnd_631762 < baseStart_631762 := by decide
  rcases family_descends (prefixWord ++ tailWord_631762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_631775 : List Nat := [1, 1, 2, 3, 5, 1, 1, 8]
def baseStart_631775 : Nat := 118140960795 + 631775 * 2 ^ 59
def prefixEnd_631775 : Nat := 4983230072969 + 3 ^ 40 * 631775 * 2
def baseEnd_631775 : Nat := 24029943740323771193113

theorem tailTrace_631775 : CollatzResearch.WordTrace tailWord_631775 prefixEnd_631775 24029943740323771193113 := by
  unfold tailWord_631775
  simp only [CollatzResearch.WordTrace]
  refine ⟨23042727286194548424864779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15361818190796365616576519 23042727286194548424864779)
  ·
    refine ⟨34564090929291822637297169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23042727286194548424864779 34564090929291822637297169)
    ·
      refine ⟨25923068196968866977972877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34564090929291822637297169 25923068196968866977972877)
      ·
        refine ⟨9721150573863325116739829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25923068196968866977972877 9721150573863325116739829)
        ·
          refine ⟨911357866299686729694359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 9721150573863325116739829 911357866299686729694359)
          ·
            refine ⟨1367036799449530094541539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 911357866299686729694359 1367036799449530094541539)
            ·
              refine ⟨2050555199174295141812309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1367036799449530094541539 2050555199174295141812309)
              ·
                refine ⟨24029943740323771193113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2050555199174295141812309 24029943740323771193113)
                ·
                  rfl

theorem cell22_631775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 1, 8].length) (baseStart_631775 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_631775 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_631775 prefixEnd_631775 := by exact prefixLift 631775
  have htrace : WordTrace (prefixWord ++ tailWord_631775) baseStart_631775 baseEnd_631775 := by
    simpa [prefixWord, tailWord_631775, baseEnd_631775] using wordTrace_append hprefix tailTrace_631775
  have hstable : (prefixWord ++ tailWord_631775).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_631775).length < 2 ^ (prefixWord ++ tailWord_631775).sum := by decide
  have hdescent : baseEnd_631775 < baseStart_631775 := by decide
  rcases family_descends (prefixWord ++ tailWord_631775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_631781 : List Nat := [1, 3, 1, 6, 1, 2, 1, 3, 4]
def baseStart_631781 : Nat := 118140960795 + 631781 * 2 ^ 59
def prefixEnd_631781 : Nat := 4983230072969 + 3 ^ 40 * 631781 * 2
def baseEnd_631781 : Nat := 72090515861843975029333

theorem tailTrace_631781 : CollatzResearch.WordTrace tailWord_631781 prefixEnd_631781 72090515861843975029333 := by
  unfold tailWord_631781
  simp only [CollatzResearch.WordTrace]
  refine ⟨23042946124172811449583197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15361964082781874299722131 23042946124172811449583197)
  ·
    refine ⟨8641104796564804293593699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23042946124172811449583197 8641104796564804293593699)
    ·
      refine ⟨12961657194847206440390549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8641104796564804293593699 12961657194847206440390549)
      ·
        refine ⟨607577681008462801893307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 12961657194847206440390549 607577681008462801893307)
        ·
          refine ⟨911366521512694202839961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 607577681008462801893307 911366521512694202839961)
          ·
            refine ⟨683524891134520652129971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 911366521512694202839961 683524891134520652129971)
            ·
              refine ⟨1025287336701780978194957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 683524891134520652129971 1025287336701780978194957)
              ·
                refine ⟨384482751263167866823109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1025287336701780978194957 384482751263167866823109)
                ·
                  refine ⟨72090515861843975029333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 384482751263167866823109 72090515861843975029333)
                  ·
                    rfl

theorem cell22_631781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 2, 1, 3, 4].length) (baseStart_631781 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_631781 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_631781 prefixEnd_631781 := by exact prefixLift 631781
  have htrace : WordTrace (prefixWord ++ tailWord_631781) baseStart_631781 baseEnd_631781 := by
    simpa [prefixWord, tailWord_631781, baseEnd_631781] using wordTrace_append hprefix tailTrace_631781
  have hstable : (prefixWord ++ tailWord_631781).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_631781).length < 2 ^ (prefixWord ++ tailWord_631781).sum := by decide
  have hdescent : baseEnd_631781 < baseStart_631781 := by decide
  rcases family_descends (prefixWord ++ tailWord_631781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_631788 : List Nat := [2, 2, 1, 1, 2, 1, 1, 1, 3, 8]
def baseStart_631788 : Nat := 118140960795 + 631788 * 2 ^ 59
def prefixEnd_631788 : Nat := 4983230072969 + 3 ^ 40 * 631788 * 2
def baseEnd_631788 : Nat := 216273943828586240162977

theorem tailTrace_631788 : CollatzResearch.WordTrace tailWord_631788 prefixEnd_631788 216273943828586240162977 := by
  unfold tailWord_631788
  simp only [CollatzResearch.WordTrace]
  refine ⟨11521600717573725822544009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15362134290098301096725345 11521600717573725822544009)
  ·
    refine ⟨8641200538180294366908007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11521600717573725822544009 8641200538180294366908007)
    ·
      refine ⟨12961800807270441550362011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8641200538180294366908007 12961800807270441550362011)
      ·
        refine ⟨19442701210905662325543017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12961800807270441550362011 19442701210905662325543017)
        ·
          refine ⟨14582025908179246744157263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19442701210905662325543017 14582025908179246744157263)
          ·
            refine ⟨21873038862268870116235895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14582025908179246744157263 21873038862268870116235895)
            ·
              refine ⟨32809558293403305174353843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21873038862268870116235895 32809558293403305174353843)
              ·
                refine ⟨49214337440104957761530765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32809558293403305174353843 49214337440104957761530765)
                ·
                  refine ⟨18455376540039359160574037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 49214337440104957761530765 18455376540039359160574037)
                  ·
                    refine ⟨216273943828586240162977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 18455376540039359160574037 216273943828586240162977)
                    ·
                      rfl

theorem cell22_631788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 8].length) (baseStart_631788 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_631788 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_631788 prefixEnd_631788 := by exact prefixLift 631788
  have htrace : WordTrace (prefixWord ++ tailWord_631788) baseStart_631788 baseEnd_631788 := by
    simpa [prefixWord, tailWord_631788, baseEnd_631788] using wordTrace_append hprefix tailTrace_631788
  have hstable : (prefixWord ++ tailWord_631788).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_631788).length < 2 ^ (prefixWord ++ tailWord_631788).sum := by decide
  have hdescent : baseEnd_631788 < baseStart_631788 := by decide
  rcases family_descends (prefixWord ++ tailWord_631788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_631794 : List Nat := [3, 2, 1, 5, 1, 1, 1, 2, 2, 4]
def baseStart_631794 : Nat := 118140960795 + 631794 * 2 ^ 59
def prefixEnd_631794 : Nat := 4983230072969 + 3 ^ 40 * 631794 * 2
def baseEnd_631794 : Nat := 216275997751204224512959

theorem tailTrace_631794 : CollatzResearch.WordTrace tailWord_631794 prefixEnd_631794 216275997751204224512959 := by
  unfold tailWord_631794
  simp only [CollatzResearch.WordTrace]
  refine ⟨5760855068281428667451609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15362280182083809779870957 5760855068281428667451609)
  ·
    refine ⟨4320641301211071500588707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5760855068281428667451609 4320641301211071500588707)
    ·
      refine ⟨6480961951816607250883061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4320641301211071500588707 6480961951816607250883061)
      ·
        refine ⟨607590182982806929770287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 6480961951816607250883061 607590182982806929770287)
        ·
          refine ⟨911385274474210394655431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 607590182982806929770287 911385274474210394655431)
          ·
            refine ⟨1367077911711315591983147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 911385274474210394655431 1367077911711315591983147)
            ·
              refine ⟨2050616867566973387974721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1367077911711315591983147 2050616867566973387974721)
              ·
                refine ⟨1537962650675230040981041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2050616867566973387974721 1537962650675230040981041)
                ·
                  refine ⟨1153471988006422530735781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1537962650675230040981041 1153471988006422530735781)
                  ·
                    refine ⟨216275997751204224512959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1153471988006422530735781 216275997751204224512959)
                    ·
                      rfl

theorem cell22_631794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 1, 2, 2, 4].length) (baseStart_631794 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_631794 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_631794 prefixEnd_631794 := by exact prefixLift 631794
  have htrace : WordTrace (prefixWord ++ tailWord_631794) baseStart_631794 baseEnd_631794 := by
    simpa [prefixWord, tailWord_631794, baseEnd_631794] using wordTrace_append hprefix tailTrace_631794
  have hstable : (prefixWord ++ tailWord_631794).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_631794).length < 2 ^ (prefixWord ++ tailWord_631794).sum := by decide
  have hdescent : baseEnd_631794 < baseStart_631794 := by decide
  rcases family_descends (prefixWord ++ tailWord_631794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_631901 : List Nat := [1, 4, 4, 1, 2, 1, 1, 3, 1, 4]
def baseStart_631901 : Nat := 118140960795 + 631901 * 2 ^ 59
def prefixEnd_631901 : Nat := 4983230072969 + 3 ^ 40 * 631901 * 2
def baseEnd_631901 : Nat := 216312626037891612087631

theorem tailTrace_631901 : CollatzResearch.WordTrace tailWord_631901 prefixEnd_631901 216312626037891612087631 := by
  unfold tailWord_631901
  simp only [CollatzResearch.WordTrace]
  refine ⟨23047322883738071943951557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15364881922492047962634371 23047322883738071943951557)
  ·
    refine ⟨4321373040700888489490917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23047322883738071943951557 4321373040700888489490917)
    ·
      refine ⟨810257445131416591779547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4321373040700888489490917 810257445131416591779547)
      ·
        refine ⟨1215386167697124887669321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 810257445131416591779547 1215386167697124887669321)
        ·
          refine ⟨911539625772843665751991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1215386167697124887669321 911539625772843665751991)
          ·
            refine ⟨1367309438659265498627987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 911539625772843665751991 1367309438659265498627987)
            ·
              refine ⟨2050964157988898247941981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1367309438659265498627987 2050964157988898247941981)
              ·
                refine ⟨769111559245836842978243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2050964157988898247941981 769111559245836842978243)
                ·
                  refine ⟨1153667338868755264467365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 769111559245836842978243 1153667338868755264467365)
                  ·
                    refine ⟨216312626037891612087631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1153667338868755264467365 216312626037891612087631)
                    ·
                      rfl

theorem cell22_631901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 1, 3, 1, 4].length) (baseStart_631901 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_631901 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_631901 prefixEnd_631901 := by exact prefixLift 631901
  have htrace : WordTrace (prefixWord ++ tailWord_631901) baseStart_631901 baseEnd_631901 := by
    simpa [prefixWord, tailWord_631901, baseEnd_631901] using wordTrace_append hprefix tailTrace_631901
  have hstable : (prefixWord ++ tailWord_631901).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_631901).length < 2 ^ (prefixWord ++ tailWord_631901).sum := by decide
  have hdescent : baseEnd_631901 < baseStart_631901 := by decide
  rcases family_descends (prefixWord ++ tailWord_631901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_631914 : List Nat := [3, 1, 3, 2, 2, 2, 1, 1, 4, 3]
def baseStart_631914 : Nat := 118140960795 + 631914 * 2 ^ 59
def prefixEnd_631914 : Nat := 4983230072969 + 3 ^ 40 * 631914 * 2
def baseEnd_631914 : Nat := 216317076203563911512591

theorem tailTrace_631914 : CollatzResearch.WordTrace tailWord_631914 prefixEnd_631914 216317076203563911512591 := by
  unfold tailWord_631914
  simp only [CollatzResearch.WordTrace]
  refine ⟨5761949258172743791043699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15365198021793983442783197 5761949258172743791043699)
  ·
    refine ⟨8642923887259115686565549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5761949258172743791043699 8642923887259115686565549)
    ·
      refine ⟨3241096457722168382462081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8642923887259115686565549 3241096457722168382462081)
      ·
        refine ⟨2430822343291626286846561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3241096457722168382462081 2430822343291626286846561)
        ·
          refine ⟨1823116757468719715134921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2430822343291626286846561 1823116757468719715134921)
          ·
            refine ⟨1367337568101539786351191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1823116757468719715134921 1367337568101539786351191)
            ·
              refine ⟨2051006352152309679526787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1367337568101539786351191 2051006352152309679526787)
              ·
                refine ⟨3076509528228464519290181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2051006352152309679526787 3076509528228464519290181)
                ·
                  refine ⟨576845536542837097366909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3076509528228464519290181 576845536542837097366909)
                  ·
                    refine ⟨216317076203563911512591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 576845536542837097366909 216317076203563911512591)
                    ·
                      rfl

theorem cell22_631914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 1, 1, 4, 3].length) (baseStart_631914 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_631914 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_631914 prefixEnd_631914 := by exact prefixLift 631914
  have htrace : WordTrace (prefixWord ++ tailWord_631914) baseStart_631914 baseEnd_631914 := by
    simpa [prefixWord, tailWord_631914, baseEnd_631914] using wordTrace_append hprefix tailTrace_631914
  have hstable : (prefixWord ++ tailWord_631914).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_631914).length < 2 ^ (prefixWord ++ tailWord_631914).sum := by decide
  have hdescent : baseEnd_631914 < baseStart_631914 := by decide
  rcases family_descends (prefixWord ++ tailWord_631914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_631955 : List Nat := [1, 1, 1, 2, 1, 2, 5, 2, 7]
def baseStart_631955 : Nat := 118140960795 + 631955 * 2 ^ 59
def prefixEnd_631955 : Nat := 4983230072969 + 3 ^ 40 * 631955 * 2
def baseEnd_631955 : Nat := 72110370447151157079155

theorem tailTrace_631955 : CollatzResearch.WordTrace tailWord_631955 prefixEnd_631955 72110370447151157079155 := by
  unfold tailWord_631955
  simp only [CollatzResearch.WordTrace]
  refine ⟨23049292425542439166417319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15366194950361626110944879 23049292425542439166417319)
  ·
    refine ⟨34573938638313658749625979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23049292425542439166417319 34573938638313658749625979)
    ·
      refine ⟨51860907957470488124438969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34573938638313658749625979 51860907957470488124438969)
      ·
        refine ⟨38895680968102866093329227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51860907957470488124438969 38895680968102866093329227)
        ·
          refine ⟨58343521452154299139993841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38895680968102866093329227 58343521452154299139993841)
          ·
            refine ⟨43757641089115724354995381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58343521452154299139993841 43757641089115724354995381)
            ·
              refine ⟨4102278852104599158280817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 43757641089115724354995381 4102278852104599158280817)
              ·
                refine ⟨3076709139078449368710613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4102278852104599158280817 3076709139078449368710613)
                ·
                  refine ⟨72110370447151157079155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3076709139078449368710613 72110370447151157079155)
                  ·
                    rfl

theorem cell22_631955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 5, 2, 7].length) (baseStart_631955 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_631955 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_631955 prefixEnd_631955 := by exact prefixLift 631955
  have htrace : WordTrace (prefixWord ++ tailWord_631955) baseStart_631955 baseEnd_631955 := by
    simpa [prefixWord, tailWord_631955, baseEnd_631955] using wordTrace_append hprefix tailTrace_631955
  have hstable : (prefixWord ++ tailWord_631955).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_631955).length < 2 ^ (prefixWord ++ tailWord_631955).sum := by decide
  have hdescent : baseEnd_631955 < baseStart_631955 := by decide
  rcases family_descends (prefixWord ++ tailWord_631955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_631972 : List Nat := [2, 3, 1, 2, 3, 1, 2, 1, 7]
def baseStart_631972 : Nat := 118140960795 + 631972 * 2 ^ 59
def prefixEnd_631972 : Nat := 4983230072969 + 3 ^ 40 * 631972 * 2
def baseEnd_631972 : Nat := 72112310262957031187471

theorem tailTrace_631972 : CollatzResearch.WordTrace tailWord_631972 prefixEnd_631972 72112310262957031187471 := by
  unfold tailWord_631972
  simp only [CollatzResearch.WordTrace]
  refine ⟨11524956233240425534893085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15366608310987234046524113 11524956233240425534893085)
  ·
    refine ⟨4321858587465159575584907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11524956233240425534893085 4321858587465159575584907)
    ·
      refine ⟨6482787881197739363377361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4321858587465159575584907 6482787881197739363377361)
      ·
        refine ⟨4862090910898304522533021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6482787881197739363377361 4862090910898304522533021)
        ·
          refine ⟨1823284091586864195949883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4862090910898304522533021 1823284091586864195949883)
          ·
            refine ⟨2734926137380296293924825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1823284091586864195949883 2734926137380296293924825)
            ·
              refine ⟨2051194603035222220443619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2734926137380296293924825 2051194603035222220443619)
              ·
                refine ⟨3076791904552833330665429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2051194603035222220443619 3076791904552833330665429)
                ·
                  refine ⟨72112310262957031187471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3076791904552833330665429 72112310262957031187471)
                  ·
                    rfl

theorem cell22_631972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 2, 1, 7].length) (baseStart_631972 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_631972 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_631972 prefixEnd_631972 := by exact prefixLift 631972
  have htrace : WordTrace (prefixWord ++ tailWord_631972) baseStart_631972 baseEnd_631972 := by
    simpa [prefixWord, tailWord_631972, baseEnd_631972] using wordTrace_append hprefix tailTrace_631972
  have hstable : (prefixWord ++ tailWord_631972).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_631972).length < 2 ^ (prefixWord ++ tailWord_631972).sum := by decide
  have hdescent : baseEnd_631972 < baseStart_631972 := by decide
  rcases family_descends (prefixWord ++ tailWord_631972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_632092 : List Nat := [2, 2, 3, 1, 1, 1, 2, 1, 1, 8]
def baseStart_632092 : Nat := 118140960795 + 632092 * 2 ^ 59
def prefixEnd_632092 : Nat := 4983230072969 + 3 ^ 40 * 632092 * 2
def baseEnd_632092 : Nat := 216378009241230780562045

theorem tailTrace_632092 : CollatzResearch.WordTrace tailWord_632092 prefixEnd_632092 216378009241230780562045 := by
  unfold tailWord_632092
  simp only [CollatzResearch.WordTrace]
  refine ⟨11527144613023055782077265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15369526150697407709436353 11527144613023055782077265)
  ·
    refine ⟨8645358459767291836557949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11527144613023055782077265 8645358459767291836557949)
    ·
      refine ⟨3242009422412734438709231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8645358459767291836557949 3242009422412734438709231)
      ·
        refine ⟨4863014133619101658063847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3242009422412734438709231 4863014133619101658063847)
        ·
          refine ⟨7294521200428652487095771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4863014133619101658063847 7294521200428652487095771)
          ·
            refine ⟨10941781800642978730643657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7294521200428652487095771 10941781800642978730643657)
            ·
              refine ⟨8206336350482234047982743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10941781800642978730643657 8206336350482234047982743)
              ·
                refine ⟨12309504525723351071974115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8206336350482234047982743 12309504525723351071974115)
                ·
                  refine ⟨18464256788585026607961173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12309504525723351071974115 18464256788585026607961173)
                  ·
                    refine ⟨216378009241230780562045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 18464256788585026607961173 216378009241230780562045)
                    ·
                      rfl

theorem cell22_632092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 1, 1, 8].length) (baseStart_632092 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_632092 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_632092 prefixEnd_632092 := by exact prefixLift 632092
  have htrace : WordTrace (prefixWord ++ tailWord_632092) baseStart_632092 baseEnd_632092 := by
    simpa [prefixWord, tailWord_632092, baseEnd_632092] using wordTrace_append hprefix tailTrace_632092
  have hstable : (prefixWord ++ tailWord_632092).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_632092).length < 2 ^ (prefixWord ++ tailWord_632092).sum := by decide
  have hdescent : baseEnd_632092 < baseStart_632092 := by decide
  rcases family_descends (prefixWord ++ tailWord_632092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_632231 : List Nat := [1, 1, 6, 1, 1, 1, 5, 6]
def baseStart_632231 : Nat := 118140960795 + 632231 * 2 ^ 59
def prefixEnd_632231 : Nat := 4983230072969 + 3 ^ 40 * 632231 * 2
def baseEnd_632231 : Nat := 24047287975764527926291

theorem tailTrace_632231 : CollatzResearch.WordTrace tailWord_632231 prefixEnd_632231 24047287975764527926291 := by
  unfold tailWord_632231
  simp only [CollatzResearch.WordTrace]
  refine ⟨23059358972542538303464547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15372905981695025535643031 23059358972542538303464547)
  ·
    refine ⟨34589038458813807455196821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23059358972542538303464547 34589038458813807455196821)
    ·
      refine ⟨1621361177756897224462351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 34589038458813807455196821 1621361177756897224462351)
      ·
        refine ⟨2432041766635345836693527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1621361177756897224462351 2432041766635345836693527)
        ·
          refine ⟨3648062649953018755040291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2432041766635345836693527 3648062649953018755040291)
          ·
            refine ⟨5472093974929528132560437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3648062649953018755040291 5472093974929528132560437)
            ·
              refine ⟨513008810149643262427541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5472093974929528132560437 513008810149643262427541)
              ·
                refine ⟨24047287975764527926291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 513008810149643262427541 24047287975764527926291)
                ·
                  rfl

theorem cell22_632231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 5, 6].length) (baseStart_632231 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_632231 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_632231 prefixEnd_632231 := by exact prefixLift 632231
  have htrace : WordTrace (prefixWord ++ tailWord_632231) baseStart_632231 baseEnd_632231 := by
    simpa [prefixWord, tailWord_632231, baseEnd_632231] using wordTrace_append hprefix tailTrace_632231
  have hstable : (prefixWord ++ tailWord_632231).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_632231).length < 2 ^ (prefixWord ++ tailWord_632231).sum := by decide
  have hdescent : baseEnd_632231 < baseStart_632231 := by decide
  rcases family_descends (prefixWord ++ tailWord_632231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_632252 : List Nat := [2, 2, 2, 4, 3, 1, 1, 2, 2, 3]
def baseStart_632252 : Nat := 118140960795 + 632252 * 2 ^ 59
def prefixEnd_632252 : Nat := 4983230072969 + 3 ^ 40 * 632252 * 2
def baseEnd_632252 : Nat := 216432780511043696561555

theorem tailTrace_632252 : CollatzResearch.WordTrace tailWord_632252 prefixEnd_632252 216432780511043696561555 := by
  unfold tailWord_632252
  simp only [CollatzResearch.WordTrace]
  refine ⟨11530062452733229444989505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15373416603644305926652673 11530062452733229444989505)
  ·
    refine ⟨8647546839549922083742129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11530062452733229444989505 8647546839549922083742129)
    ·
      refine ⟨6485660129662441562806597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8647546839549922083742129 6485660129662441562806597)
      ·
        refine ⟨1216061274311707793026237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6485660129662441562806597 1216061274311707793026237)
        ·
          refine ⟨456022977866890422384839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1216061274311707793026237 456022977866890422384839)
          ·
            refine ⟨684034466800335633577259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 456022977866890422384839 684034466800335633577259)
            ·
              refine ⟨1026051700200503450365889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 684034466800335633577259 1026051700200503450365889)
              ·
                refine ⟨769538775150377587774417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1026051700200503450365889 769538775150377587774417)
                ·
                  refine ⟨577154081362783190830813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 769538775150377587774417 577154081362783190830813)
                  ·
                    refine ⟨216432780511043696561555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 577154081362783190830813 216432780511043696561555)
                    ·
                      rfl

theorem cell22_632252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 3, 1, 1, 2, 2, 3].length) (baseStart_632252 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_632252 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_632252 prefixEnd_632252 := by exact prefixLift 632252
  have htrace : WordTrace (prefixWord ++ tailWord_632252) baseStart_632252 baseEnd_632252 := by
    simpa [prefixWord, tailWord_632252, baseEnd_632252] using wordTrace_append hprefix tailTrace_632252
  have hstable : (prefixWord ++ tailWord_632252).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_632252).length < 2 ^ (prefixWord ++ tailWord_632252).sum := by decide
  have hdescent : baseEnd_632252 < baseStart_632252 := by decide
  rcases family_descends (prefixWord ++ tailWord_632252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_632263 : List Nat := [1, 1, 4, 1, 1, 3, 1, 6, 1, 3]
def baseStart_632263 : Nat := 118140960795 + 632263 * 2 ^ 59
def prefixEnd_632263 : Nat := 4983230072969 + 3 ^ 40 * 632263 * 2
def baseEnd_632263 : Nat := 216436546035843334536521

theorem tailTrace_632263 : CollatzResearch.WordTrace tailWord_632263 prefixEnd_632263 216436546035843334536521 := by
  unfold tailWord_632263
  simp only [CollatzResearch.WordTrace]
  refine ⟨23060526108426607768629443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15373684072284405179086295 23060526108426607768629443)
  ·
    refine ⟨34590789162639911652944165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23060526108426607768629443 34590789162639911652944165)
    ·
      refine ⟨6485772967994983434927031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34590789162639911652944165 6485772967994983434927031)
      ·
        refine ⟨9728659451992475152390547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6485772967994983434927031 9728659451992475152390547)
        ·
          refine ⟨14592989177988712728585821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9728659451992475152390547 14592989177988712728585821)
          ·
            refine ⟨5472370941745767273219683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14592989177988712728585821 5472370941745767273219683)
            ·
              refine ⟨8208556412618650909829525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5472370941745767273219683 8208556412618650909829525)
              ·
                refine ⟨384776081841499261398259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 8208556412618650909829525 384776081841499261398259)
                ·
                  refine ⟨577164122762248892097389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 384776081841499261398259 577164122762248892097389)
                  ·
                    refine ⟨216436546035843334536521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 577164122762248892097389 216436546035843334536521)
                    ·
                      rfl

theorem cell22_632263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 6, 1, 3].length) (baseStart_632263 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_632263 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_632263 prefixEnd_632263 := by exact prefixLift 632263
  have htrace : WordTrace (prefixWord ++ tailWord_632263) baseStart_632263 baseEnd_632263 := by
    simpa [prefixWord, tailWord_632263, baseEnd_632263] using wordTrace_append hprefix tailTrace_632263
  have hstable : (prefixWord ++ tailWord_632263).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_632263).length < 2 ^ (prefixWord ++ tailWord_632263).sum := by decide
  have hdescent : baseEnd_632263 < baseStart_632263 := by decide
  rcases family_descends (prefixWord ++ tailWord_632263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_632319 : List Nat := [1, 1, 2, 2, 1, 2, 2, 1, 5, 5]
def baseStart_632319 : Nat := 118140960795 + 632319 * 2 ^ 59
def prefixEnd_632319 : Nat := 4983230072969 + 3 ^ 40 * 632319 * 2
def baseEnd_632319 : Nat := 216455715980277855136349

theorem tailTrace_632319 : CollatzResearch.WordTrace tailWord_632319 prefixEnd_632319 216455715980277855136349 := by
  unfold tailWord_632319
  simp only [CollatzResearch.WordTrace]
  refine ⟨23062568596223729332668011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15375045730815819555112007 23062568596223729332668011)
  ·
    refine ⟨34593852894335593999002017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23062568596223729332668011 34593852894335593999002017)
    ·
      refine ⟨25945389670751695499251513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34593852894335593999002017 25945389670751695499251513)
      ·
        refine ⟨19459042253063771624438635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25945389670751695499251513 19459042253063771624438635)
        ·
          refine ⟨29188563379595657436657953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19459042253063771624438635 29188563379595657436657953)
          ·
            refine ⟨21891422534696743077493465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29188563379595657436657953 21891422534696743077493465)
            ·
              refine ⟨16418566901022557308120099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21891422534696743077493465 16418566901022557308120099)
              ·
                refine ⟨24627850351533835962180149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16418566901022557308120099 24627850351533835962180149)
                ·
                  refine ⟨2308860970456297121454389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 24627850351533835962180149 2308860970456297121454389)
                  ·
                    refine ⟨216455715980277855136349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2308860970456297121454389 216455715980277855136349)
                    ·
                      rfl

theorem cell22_632319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 1, 5, 5].length) (baseStart_632319 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_632319 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_632319 prefixEnd_632319 := by exact prefixLift 632319
  have htrace : WordTrace (prefixWord ++ tailWord_632319) baseStart_632319 baseEnd_632319 := by
    simpa [prefixWord, tailWord_632319, baseEnd_632319] using wordTrace_append hprefix tailTrace_632319
  have hstable : (prefixWord ++ tailWord_632319).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_632319).length < 2 ^ (prefixWord ++ tailWord_632319).sum := by decide
  have hdescent : baseEnd_632319 < baseStart_632319 := by decide
  rcases family_descends (prefixWord ++ tailWord_632319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_632340 : List Nat := [2, 4, 3, 1, 2, 1, 1, 1, 3, 4]
def baseStart_632340 : Nat := 118140960795 + 632340 * 2 ^ 59
def prefixEnd_632340 : Nat := 4983230072969 + 3 ^ 40 * 632340 * 2
def baseEnd_632340 : Nat := 216462904709440800361285

theorem tailTrace_632340 : CollatzResearch.WordTrace tailWord_632340 prefixEnd_632340 216462904709440800361285 := by
  unfold tailWord_632340
  simp only [CollatzResearch.WordTrace]
  refine ⟨11531667264573824959591237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15375556352765099946121649 11531667264573824959591237)
  ·
    refine ⟨2162187612107592179923357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11531667264573824959591237 2162187612107592179923357)
    ·
      refine ⟨810820354540347067471259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2162187612107592179923357 810820354540347067471259)
      ·
        refine ⟨1216230531810520601206889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 810820354540347067471259 1216230531810520601206889)
        ·
          refine ⟨912172898857890450905167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1216230531810520601206889 912172898857890450905167)
          ·
            refine ⟨1368259348286835676357751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 912172898857890450905167 1368259348286835676357751)
            ·
              refine ⟨2052389022430253514536627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1368259348286835676357751 2052389022430253514536627)
              ·
                refine ⟨3078583533645380271804941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2052389022430253514536627 3078583533645380271804941)
                ·
                  refine ⟨1154468825117017601926853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3078583533645380271804941 1154468825117017601926853)
                  ·
                    refine ⟨216462904709440800361285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1154468825117017601926853 216462904709440800361285)
                    ·
                      rfl

theorem cell22_632340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 1, 1, 3, 4].length) (baseStart_632340 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_632340 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_632340 prefixEnd_632340 := by exact prefixLift 632340
  have htrace : WordTrace (prefixWord ++ tailWord_632340) baseStart_632340 baseEnd_632340 := by
    simpa [prefixWord, tailWord_632340, baseEnd_632340] using wordTrace_append hprefix tailTrace_632340
  have hstable : (prefixWord ++ tailWord_632340).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_632340).length < 2 ^ (prefixWord ++ tailWord_632340).sum := by decide
  have hdescent : baseEnd_632340 < baseStart_632340 := by decide
  rcases family_descends (prefixWord ++ tailWord_632340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_632351 : List Nat := [1, 1, 2, 4, 1, 1, 3, 3, 2, 4]
def baseStart_632351 : Nat := 118140960795 + 632351 * 2 ^ 59
def prefixEnd_632351 : Nat := 4983230072969 + 3 ^ 40 * 632351 * 2
def baseEnd_632351 : Nat := 216466670234240438336251

theorem tailTrace_632351 : CollatzResearch.WordTrace tailWord_632351 prefixEnd_632351 216466670234240438336251 := by
  unfold tailWord_632351
  simp only [CollatzResearch.WordTrace]
  refine ⟨23063735732107798797832907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15375823821405199198555271 23063735732107798797832907)
  ·
    refine ⟨34595603598161698196749361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23063735732107798797832907 34595603598161698196749361)
    ·
      refine ⟨25946702698621273647562021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34595603598161698196749361 25946702698621273647562021)
      ·
        refine ⟨4865006755991488808917879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25946702698621273647562021 4865006755991488808917879)
        ·
          refine ⟨7297510133987233213376819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4865006755991488808917879 7297510133987233213376819)
          ·
            refine ⟨10946265200980849820065229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7297510133987233213376819 10946265200980849820065229)
            ·
              refine ⟨4104849450367818682524461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10946265200980849820065229 4104849450367818682524461)
              ·
                refine ⟨1539318543887932005946673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4104849450367818682524461 1539318543887932005946673)
                ·
                  refine ⟨1154488907915949004460005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1539318543887932005946673 1154488907915949004460005)
                  ·
                    refine ⟨216466670234240438336251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1154488907915949004460005 216466670234240438336251)
                    ·
                      rfl

theorem cell22_632351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 3, 3, 2, 4].length) (baseStart_632351 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_632351 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_632351 prefixEnd_632351 := by exact prefixLift 632351
  have htrace : WordTrace (prefixWord ++ tailWord_632351) baseStart_632351 baseEnd_632351 := by
    simpa [prefixWord, tailWord_632351, baseEnd_632351] using wordTrace_append hprefix tailTrace_632351
  have hstable : (prefixWord ++ tailWord_632351).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_632351).length < 2 ^ (prefixWord ++ tailWord_632351).sum := by decide
  have hdescent : baseEnd_632351 < baseStart_632351 := by decide
  rcases family_descends (prefixWord ++ tailWord_632351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_632366 : List Nat := [4, 1, 3, 1, 2, 11]
def baseStart_632366 : Nat := 118140960795 + 632366 * 2 ^ 59
def prefixEnd_632366 : Nat := 4983230072969 + 3 ^ 40 * 632366 * 2
def baseEnd_632366 : Nat := 2672491420256609866805

theorem tailTrace_632366 : CollatzResearch.WordTrace tailWord_632366 prefixEnd_632366 2672491420256609866805 := by
  unfold tailWord_632366
  simp only [CollatzResearch.WordTrace]
  refine ⟨2883035353381682044953619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15376188551368970906419301 2883035353381682044953619)
  ·
    refine ⟨4324553030072523067430429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2883035353381682044953619 4324553030072523067430429)
    ·
      refine ⟨1621707386277196150286411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4324553030072523067430429 1621707386277196150286411)
      ·
        refine ⟨2432561079415794225429617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1621707386277196150286411 2432561079415794225429617)
        ·
          refine ⟨1824420809561845669072213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2432561079415794225429617 1824420809561845669072213)
          ·
            refine ⟨2672491420256609866805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 1824420809561845669072213 2672491420256609866805)
            ·
              rfl

theorem cell22_632366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 11].length) (baseStart_632366 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_632366 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_632366 prefixEnd_632366 := by exact prefixLift 632366
  have htrace : WordTrace (prefixWord ++ tailWord_632366) baseStart_632366 baseEnd_632366 := by
    simpa [prefixWord, tailWord_632366, baseEnd_632366] using wordTrace_append hprefix tailTrace_632366
  have hstable : (prefixWord ++ tailWord_632366).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_632366).length < 2 ^ (prefixWord ++ tailWord_632366).sum := by decide
  have hdescent : baseEnd_632366 < baseStart_632366 := by decide
  rcases family_descends (prefixWord ++ tailWord_632366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_632445 : List Nat := [1, 4, 1, 1, 4, 2, 3, 1, 5]
def baseStart_632445 : Nat := 118140960795 + 632445 * 2 ^ 59
def prefixEnd_632445 : Nat := 4983230072969 + 3 ^ 40 * 632445 * 2
def baseEnd_632445 : Nat := 72166282785085175495321

theorem tailTrace_632445 : CollatzResearch.WordTrace tailWord_632445 prefixEnd_632445 72166282785085175495321 := by
  unfold tailWord_632445
  simp only [CollatzResearch.WordTrace]
  refine ⟨23067164193767252851754789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15378109462511501901169859 23067164193767252851754789)
  ·
    refine ⟨4325093286331359909704023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23067164193767252851754789 4325093286331359909704023)
    ·
      refine ⟨6487639929497039864556035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4325093286331359909704023 6487639929497039864556035)
      ·
        refine ⟨9731459894245559796834053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6487639929497039864556035 9731459894245559796834053)
        ·
          refine ⟨1824648730171042461906385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9731459894245559796834053 1824648730171042461906385)
          ·
            refine ⟨1368486547628281846429789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1824648730171042461906385 1368486547628281846429789)
            ·
              refine ⟨513182455360605692411171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1368486547628281846429789 513182455360605692411171)
              ·
                refine ⟨769773683040908538616757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 513182455360605692411171 769773683040908538616757)
                ·
                  refine ⟨72166282785085175495321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 769773683040908538616757 72166282785085175495321)
                  ·
                    rfl

theorem cell22_632445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 3, 1, 5].length) (baseStart_632445 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_632445 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_632445 prefixEnd_632445 := by exact prefixLift 632445
  have htrace : WordTrace (prefixWord ++ tailWord_632445) baseStart_632445 baseEnd_632445 := by
    simpa [prefixWord, tailWord_632445, baseEnd_632445] using wordTrace_append hprefix tailTrace_632445
  have hstable : (prefixWord ++ tailWord_632445).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_632445).length < 2 ^ (prefixWord ++ tailWord_632445).sum := by decide
  have hdescent : baseEnd_632445 < baseStart_632445 := by decide
  rcases family_descends (prefixWord ++ tailWord_632445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_632466 : List Nat := [3, 2, 3, 1, 4, 1, 1, 3, 1, 3]
def baseStart_632466 : Nat := 118140960795 + 632466 * 2 ^ 59
def prefixEnd_632466 : Nat := 4983230072969 + 3 ^ 40 * 632466 * 2
def baseEnd_632466 : Nat := 216506037084418471710899

theorem tailTrace_632466 : CollatzResearch.WordTrace tailWord_632466 prefixEnd_632466 216506037084418471710899 := by
  unfold tailWord_632466
  simp only [CollatzResearch.WordTrace]
  refine ⟨5766982531672793359567313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15378620084460782292179501 5766982531672793359567313)
  ·
    refine ⟨4325236898754595019675485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5766982531672793359567313 4325236898754595019675485)
    ·
      refine ⟨1621963837032973132378307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4325236898754595019675485 1621963837032973132378307)
      ·
        refine ⟨2432945755549459698567461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1621963837032973132378307 2432945755549459698567461)
        ·
          refine ⟨456177329165523693481399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2432945755549459698567461 456177329165523693481399)
          ·
            refine ⟨684265993748285540222099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 456177329165523693481399 684265993748285540222099)
            ·
              refine ⟨1026398990622428310333149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 684265993748285540222099 1026398990622428310333149)
              ·
                refine ⟨384899621483410616374931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1026398990622428310333149 384899621483410616374931)
                ·
                  refine ⟨577349432225115924562397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 384899621483410616374931 577349432225115924562397)
                  ·
                    refine ⟨216506037084418471710899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 577349432225115924562397 216506037084418471710899)
                    ·
                      rfl

theorem cell22_632466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 4, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 4, 1, 1, 3, 1, 3].length) (baseStart_632466 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_632466 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_632466 prefixEnd_632466 := by exact prefixLift 632466
  have htrace : WordTrace (prefixWord ++ tailWord_632466) baseStart_632466 baseEnd_632466 := by
    simpa [prefixWord, tailWord_632466, baseEnd_632466] using wordTrace_append hprefix tailTrace_632466
  have hstable : (prefixWord ++ tailWord_632466).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_632466).length < 2 ^ (prefixWord ++ tailWord_632466).sum := by decide
  have hdescent : baseEnd_632466 < baseStart_632466 := by decide
  rcases family_descends (prefixWord ++ tailWord_632466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_632473 : List Nat := [1, 2, 1, 2, 1, 2, 2, 7, 4]
def baseStart_632473 : Nat := 118140960795 + 632473 * 2 ^ 59
def prefixEnd_632473 : Nat := 4983230072969 + 3 ^ 40 * 632473 * 2
def baseEnd_632473 : Nat := 72169477775824262261959

theorem tailTrace_632473 : CollatzResearch.WordTrace tailWord_632473 prefixEnd_632473 72169477775824262261959 := by
  unfold tailWord_632473
  simp only [CollatzResearch.WordTrace]
  refine ⟨23068185437665813633774073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15378790291777209089182715 23068185437665813633774073)
  ·
    refine ⟨17301139078249360225330555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23068185437665813633774073 17301139078249360225330555)
    ·
      refine ⟨25951708617374040337995833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17301139078249360225330555 25951708617374040337995833)
      ·
        refine ⟨19463781463030530253496875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25951708617374040337995833 19463781463030530253496875)
        ·
          refine ⟨29195672194545795380245313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19463781463030530253496875 29195672194545795380245313)
          ·
            refine ⟨21896754145909346535183985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29195672194545795380245313 21896754145909346535183985)
            ·
              refine ⟨16422565609432009901387989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21896754145909346535183985 16422565609432009901387989)
              ·
                refine ⟨384903881471062732063781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 16422565609432009901387989 384903881471062732063781)
                ·
                  refine ⟨72169477775824262261959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 384903881471062732063781 72169477775824262261959)
                  ·
                    rfl

theorem cell22_632473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 7, 4].length) (baseStart_632473 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_632473 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_632473 prefixEnd_632473 := by exact prefixLift 632473
  have htrace : WordTrace (prefixWord ++ tailWord_632473) baseStart_632473 baseEnd_632473 := by
    simpa [prefixWord, tailWord_632473, baseEnd_632473] using wordTrace_append hprefix tailTrace_632473
  have hstable : (prefixWord ++ tailWord_632473).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_632473).length < 2 ^ (prefixWord ++ tailWord_632473).sum := by decide
  have hdescent : baseEnd_632473 < baseStart_632473 := by decide
  rcases family_descends (prefixWord ++ tailWord_632473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_632541 : List Nat := [1, 4, 3, 3, 1, 2, 2, 2, 4]
def baseStart_632541 : Nat := 118140960795 + 632541 * 2 ^ 59
def prefixEnd_632541 : Nat := 4983230072969 + 3 ^ 40 * 632541 * 2
def baseEnd_632541 : Nat := 72177237039047758695223

theorem tailTrace_632541 : CollatzResearch.WordTrace tailWord_632541 prefixEnd_632541 72177237039047758695223 := by
  unfold tailWord_632541
  simp only [CollatzResearch.WordTrace]
  refine ⟨23070665601419461247249477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15380443734279640831499651 23070665601419461247249477)
  ·
    refine ⟨4325749800266148983859277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23070665601419461247249477 4325749800266148983859277)
    ·
      refine ⟨1622156175099805868947229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4325749800266148983859277 1622156175099805868947229)
      ·
        refine ⟨608308565662427200855211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1622156175099805868947229 608308565662427200855211)
        ·
          refine ⟨912462848493640801282817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 608308565662427200855211 912462848493640801282817)
          ·
            refine ⟨684347136370230600962113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 912462848493640801282817 684347136370230600962113)
            ·
              refine ⟨513260352277672950721585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 684347136370230600962113 513260352277672950721585)
              ·
                refine ⟨384945264208254713041189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 513260352277672950721585 384945264208254713041189)
                ·
                  refine ⟨72177237039047758695223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 384945264208254713041189 72177237039047758695223)
                  ·
                    rfl

theorem cell22_632541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 2, 2, 2, 4].length) (baseStart_632541 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_632541 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_632541 prefixEnd_632541 := by exact prefixLift 632541
  have htrace : WordTrace (prefixWord ++ tailWord_632541) baseStart_632541 baseEnd_632541 := by
    simpa [prefixWord, tailWord_632541, baseEnd_632541] using wordTrace_append hprefix tailTrace_632541
  have hstable : (prefixWord ++ tailWord_632541).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_632541).length < 2 ^ (prefixWord ++ tailWord_632541).sum := by decide
  have hdescent : baseEnd_632541 < baseStart_632541 := by decide
  rcases family_descends (prefixWord ++ tailWord_632541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_632563 : List Nat := [1, 1, 1, 2, 2, 3, 4, 3, 5]
def baseStart_632563 : Nat := 118140960795 + 632563 * 2 ^ 59
def prefixEnd_632563 : Nat := 4983230072969 + 3 ^ 40 * 632563 * 2
def baseEnd_632563 : Nat := 72179747388914184011867

theorem tailTrace_632563 : CollatzResearch.WordTrace tailWord_632563 prefixEnd_632563 72179747388914184011867 := by
  unfold tailWord_632563
  simp only [CollatzResearch.WordTrace]
  refine ⟨23071468007339759004550343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15380978671559839336366895 23071468007339759004550343)
  ·
    refine ⟨34607202011009638506825515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23071468007339759004550343 34607202011009638506825515)
    ·
      refine ⟨51910803016514457760238273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34607202011009638506825515 51910803016514457760238273)
      ·
        refine ⟨38933102262385843320178705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51910803016514457760238273 38933102262385843320178705)
        ·
          refine ⟨29199826696789382490134029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38933102262385843320178705 29199826696789382490134029)
          ·
            refine ⟨10949935011296018433800261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29199826696789382490134029 10949935011296018433800261)
            ·
              refine ⟨2053112814618003456337549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10949935011296018433800261 2053112814618003456337549)
              ·
                refine ⟨769917305481751296126581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2053112814618003456337549 769917305481751296126581)
                ·
                  refine ⟨72179747388914184011867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 769917305481751296126581 72179747388914184011867)
                  ·
                    rfl

theorem cell22_632563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 4, 3, 5].length) (baseStart_632563 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_632563 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_632563 prefixEnd_632563 := by exact prefixLift 632563
  have htrace : WordTrace (prefixWord ++ tailWord_632563) baseStart_632563 baseEnd_632563 := by
    simpa [prefixWord, tailWord_632563, baseEnd_632563] using wordTrace_append hprefix tailTrace_632563
  have hstable : (prefixWord ++ tailWord_632563).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_632563).length < 2 ^ (prefixWord ++ tailWord_632563).sum := by decide
  have hdescent : baseEnd_632563 < baseStart_632563 := by decide
  rcases family_descends (prefixWord ++ tailWord_632563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_632627 : List Nat := [1, 1, 1, 2, 7, 1, 2, 2, 1, 4]
def baseStart_632627 : Nat := 118140960795 + 632627 * 2 ^ 59
def prefixEnd_632627 : Nat := 4983230072969 + 3 ^ 40 * 632627 * 2
def baseEnd_632627 : Nat := 216561150674667718435405

theorem tailTrace_632627 : CollatzResearch.WordTrace tailWord_632627 prefixEnd_632627 216561150674667718435405 := by
  unfold tailWord_632627
  simp only [CollatzResearch.WordTrace]
  refine ⟨23073802279107897934880135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15382534852738598623253423 23073802279107897934880135)
  ·
    refine ⟨34610703418661846902320203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23073802279107897934880135 34610703418661846902320203)
    ·
      refine ⟨51916055127992770353480305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34610703418661846902320203 51916055127992770353480305)
      ·
        refine ⟨38937041345994577765110229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51916055127992770353480305 38937041345994577765110229)
        ·
          refine ⟨912586906546747916369771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 38937041345994577765110229 912586906546747916369771)
          ·
            refine ⟨1368880359820121874554657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 912586906546747916369771 1368880359820121874554657)
            ·
              refine ⟨1026660269865091405915993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1368880359820121874554657 1026660269865091405915993)
              ·
                refine ⟨769995202398818554436995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1026660269865091405915993 769995202398818554436995)
                ·
                  refine ⟨1154992803598227831655493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 769995202398818554436995 1154992803598227831655493)
                  ·
                    refine ⟨216561150674667718435405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1154992803598227831655493 216561150674667718435405)
                    ·
                      rfl

theorem cell22_632627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 2, 2, 1, 4].length) (baseStart_632627 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_632627 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_632627 prefixEnd_632627 := by exact prefixLift 632627
  have htrace : WordTrace (prefixWord ++ tailWord_632627) baseStart_632627 baseEnd_632627 := by
    simpa [prefixWord, tailWord_632627, baseEnd_632627] using wordTrace_append hprefix tailTrace_632627
  have hstable : (prefixWord ++ tailWord_632627).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_632627).length < 2 ^ (prefixWord ++ tailWord_632627).sum := by decide
  have hdescent : baseEnd_632627 < baseStart_632627 := by decide
  rcases family_descends (prefixWord ++ tailWord_632627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_632674 : List Nat := [3, 3, 2, 1, 2, 2, 1, 3, 2, 3]
def baseStart_632674 : Nat := 118140960795 + 632674 * 2 ^ 59
def prefixEnd_632674 : Nat := 4983230072969 + 3 ^ 40 * 632674 * 2
def baseEnd_632674 : Nat := 216577239735175262510261

theorem tailTrace_632674 : CollatzResearch.WordTrace tailWord_632674 prefixEnd_632674 216577239735175262510261 := by
  unfold tailWord_632674
  simp only [CollatzResearch.WordTrace]
  refine ⟨5768879127484406240460269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15383677673291749974560717 5768879127484406240460269)
  ·
    refine ⟨2163329672806652340172601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5768879127484406240460269 2163329672806652340172601)
    ·
      refine ⟨1622497254604989255129451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2163329672806652340172601 1622497254604989255129451)
      ·
        refine ⟨2433745881907483882694177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1622497254604989255129451 2433745881907483882694177)
        ·
          refine ⟨1825309411430612912020633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2433745881907483882694177 1825309411430612912020633)
          ·
            refine ⟨1368982058572959684015475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1825309411430612912020633 1368982058572959684015475)
            ·
              refine ⟨2053473087859439526023213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1368982058572959684015475 2053473087859439526023213)
              ·
                refine ⟨770052407947289822258705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2053473087859439526023213 770052407947289822258705)
                ·
                  refine ⟨577539305960467366694029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 770052407947289822258705 577539305960467366694029)
                  ·
                    refine ⟨216577239735175262510261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 577539305960467366694029 216577239735175262510261)
                    ·
                      rfl

theorem cell22_632674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 1, 3, 2, 3].length) (baseStart_632674 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_632674 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_632674 prefixEnd_632674 := by exact prefixLift 632674
  have htrace : WordTrace (prefixWord ++ tailWord_632674) baseStart_632674 baseEnd_632674 := by
    simpa [prefixWord, tailWord_632674, baseEnd_632674] using wordTrace_append hprefix tailTrace_632674
  have hstable : (prefixWord ++ tailWord_632674).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_632674).length < 2 ^ (prefixWord ++ tailWord_632674).sum := by decide
  have hdescent : baseEnd_632674 < baseStart_632674 := by decide
  rcases family_descends (prefixWord ++ tailWord_632674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_632698 : List Nat := [3, 1, 1, 1, 1, 1, 4, 1, 9]
def baseStart_632698 : Nat := 118140960795 + 632698 * 2 ^ 59
def prefixEnd_632698 : Nat := 4983230072969 + 3 ^ 40 * 632698 * 2
def baseEnd_632698 : Nat := 72195151808549066636729

theorem tailTrace_632698 : CollatzResearch.WordTrace tailWord_632698 prefixEnd_632698 72195151808549066636729 := by
  unfold tailWord_632698
  simp only [CollatzResearch.WordTrace]
  refine ⟨5769097965462669265178687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15384261241233784707143165 5769097965462669265178687)
  ·
    refine ⟨8653646948194003897768031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5769097965462669265178687 8653646948194003897768031)
    ·
      refine ⟨12980470422291005846652047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8653646948194003897768031 12980470422291005846652047)
      ·
        refine ⟨19470705633436508769978071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12980470422291005846652047 19470705633436508769978071)
        ·
          refine ⟨29206058450154763154967107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19470705633436508769978071 29206058450154763154967107)
          ·
            refine ⟨43809087675232144732450661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29206058450154763154967107 43809087675232144732450661)
            ·
              refine ⟨8214203939106027137334499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 43809087675232144732450661 8214203939106027137334499)
              ·
                refine ⟨12321305908659040706001749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8214203939106027137334499 12321305908659040706001749)
                ·
                  refine ⟨72195151808549066636729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 12321305908659040706001749 72195151808549066636729)
                  ·
                    rfl

theorem cell22_632698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 1, 9].length) (baseStart_632698 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_632698 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_632698 prefixEnd_632698 := by exact prefixLift 632698
  have htrace : WordTrace (prefixWord ++ tailWord_632698) baseStart_632698 baseEnd_632698 := by
    simpa [prefixWord, tailWord_632698, baseEnd_632698] using wordTrace_append hprefix tailTrace_632698
  have hstable : (prefixWord ++ tailWord_632698).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_632698).length < 2 ^ (prefixWord ++ tailWord_632698).sum := by decide
  have hdescent : baseEnd_632698 < baseStart_632698 := by decide
  rcases family_descends (prefixWord ++ tailWord_632698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_632730 : List Nat := [3, 1, 1, 4, 2, 1, 1, 1, 1, 7]
def baseStart_632730 : Nat := 118140960795 + 632730 * 2 ^ 59
def prefixEnd_632730 : Nat := 4983230072969 + 3 ^ 40 * 632730 * 2
def baseEnd_632730 : Nat := 216596409679609783110089

theorem tailTrace_632730 : CollatzResearch.WordTrace tailWord_632730 prefixEnd_632730 216596409679609783110089 := by
  unfold tailWord_632730
  simp only [CollatzResearch.WordTrace]
  refine ⟨5769389749433686631469911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15385039331823164350586429 5769389749433686631469911)
  ·
    refine ⟨8654084624150529947204867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5769389749433686631469911 8654084624150529947204867)
    ·
      refine ⟨12981126936225794920807301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8654084624150529947204867 12981126936225794920807301)
      ·
        refine ⟨2433961300542336547651369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12981126936225794920807301 2433961300542336547651369)
        ·
          refine ⟨1825470975406752410738527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2433961300542336547651369 1825470975406752410738527)
          ·
            refine ⟨2738206463110128616107791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1825470975406752410738527 2738206463110128616107791)
            ·
              refine ⟨4107309694665192924161687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2738206463110128616107791 4107309694665192924161687)
              ·
                refine ⟨6160964541997789386242531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4107309694665192924161687 6160964541997789386242531)
                ·
                  refine ⟨9241446812996684079363797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6160964541997789386242531 9241446812996684079363797)
                  ·
                    refine ⟨216596409679609783110089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 9241446812996684079363797 216596409679609783110089)
                    ·
                      rfl

theorem cell22_632730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 1, 1, 1, 7].length) (baseStart_632730 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_632730 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_632730 prefixEnd_632730 := by exact prefixLift 632730
  have htrace : WordTrace (prefixWord ++ tailWord_632730) baseStart_632730 baseEnd_632730 := by
    simpa [prefixWord, tailWord_632730, baseEnd_632730] using wordTrace_append hprefix tailTrace_632730
  have hstable : (prefixWord ++ tailWord_632730).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_632730).length < 2 ^ (prefixWord ++ tailWord_632730).sum := by decide
  have hdescent : baseEnd_632730 < baseStart_632730 := by decide
  rcases family_descends (prefixWord ++ tailWord_632730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_632732 : List Nat := [2, 2, 3, 3, 1, 1, 2, 3, 5]
def baseStart_632732 : Nat := 118140960795 + 632732 * 2 ^ 59
def prefixEnd_632732 : Nat := 4983230072969 + 3 ^ 40 * 632732 * 2
def baseEnd_632732 : Nat := 72199031440160814853361

theorem tailTrace_632732 : CollatzResearch.WordTrace tailWord_632732 prefixEnd_632732 72199031440160814853361 := by
  unfold tailWord_632732
  simp only [CollatzResearch.WordTrace]
  refine ⟨11538815971863750433726225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15385087962485000578301633 11538815971863750433726225)
  ·
    refine ⟨8654111978897812825294669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11538815971863750433726225 8654111978897812825294669)
    ·
      refine ⟨3245291992086679809485501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8654111978897812825294669 3245291992086679809485501)
      ·
        refine ⟨1216984497032504928557063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3245291992086679809485501 1216984497032504928557063)
        ·
          refine ⟨1825476745548757392835595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1216984497032504928557063 1825476745548757392835595)
          ·
            refine ⟨2738215118323136089253393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1825476745548757392835595 2738215118323136089253393)
            ·
              refine ⟨2053661338742352066940045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2738215118323136089253393 2053661338742352066940045)
              ·
                refine ⟨770123002028382025102517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2053661338742352066940045 770123002028382025102517)
                ·
                  refine ⟨72199031440160814853361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 770123002028382025102517 72199031440160814853361)
                  ·
                    rfl

theorem cell22_632732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 2, 3, 5].length) (baseStart_632732 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_632732 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_632732 prefixEnd_632732 := by exact prefixLift 632732
  have htrace : WordTrace (prefixWord ++ tailWord_632732) baseStart_632732 baseEnd_632732 := by
    simpa [prefixWord, tailWord_632732, baseEnd_632732] using wordTrace_append hprefix tailTrace_632732
  have hstable : (prefixWord ++ tailWord_632732).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_632732).length < 2 ^ (prefixWord ++ tailWord_632732).sum := by decide
  have hdescent : baseEnd_632732 < baseStart_632732 := by decide
  rcases family_descends (prefixWord ++ tailWord_632732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_632944 : List Nat := [2, 1, 1, 1, 5, 3, 1, 1, 4, 3]
def baseStart_632944 : Nat := 118140960795 + 632944 * 2 ^ 59
def prefixEnd_632944 : Nat := 4983230072969 + 3 ^ 40 * 632944 * 2
def baseEnd_632944 : Nat := 216669666252984558259433

theorem tailTrace_632944 : CollatzResearch.WordTrace tailWord_632944 prefixEnd_632944 216669666252984558259433 := by
  unfold tailWord_632944
  simp only [CollatzResearch.WordTrace]
  refine ⟨11542682109479730537084943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15390242812639640716113257 11542682109479730537084943)
  ·
    refine ⟨17314023164219595805627415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11542682109479730537084943 17314023164219595805627415)
    ·
      refine ⟨25971034746329393708441123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17314023164219595805627415 25971034746329393708441123)
      ·
        refine ⟨38956552119494090562661685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25971034746329393708441123 38956552119494090562661685)
        ·
          refine ⟨3652176761202570990249533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 38956552119494090562661685 3652176761202570990249533)
          ·
            refine ⟨1369566285450964121343575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3652176761202570990249533 1369566285450964121343575)
            ·
              refine ⟨2054349428176446182015363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1369566285450964121343575 2054349428176446182015363)
              ·
                refine ⟨3081524142264669273023045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2054349428176446182015363 3081524142264669273023045)
                ·
                  refine ⟨577785776674625488691821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3081524142264669273023045 577785776674625488691821)
                  ·
                    refine ⟨216669666252984558259433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 577785776674625488691821 216669666252984558259433)
                    ·
                      rfl

theorem cell22_632944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 1, 1, 4, 3].length) (baseStart_632944 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_632944 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_632944 prefixEnd_632944 := by exact prefixLift 632944
  have htrace : WordTrace (prefixWord ++ tailWord_632944) baseStart_632944 baseEnd_632944 := by
    simpa [prefixWord, tailWord_632944, baseEnd_632944] using wordTrace_append hprefix tailTrace_632944
  have hstable : (prefixWord ++ tailWord_632944).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_632944).length < 2 ^ (prefixWord ++ tailWord_632944).sum := by decide
  have hdescent : baseEnd_632944 < baseStart_632944 := by decide
  rcases family_descends (prefixWord ++ tailWord_632944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_632961 : List Nat := [1, 2, 4, 2, 3, 2, 1, 1, 1, 5]
def baseStart_632961 : Nat := 118140960795 + 632961 * 2 ^ 59
def prefixEnd_632961 : Nat := 4983230072969 + 3 ^ 40 * 632961 * 2
def baseEnd_632961 : Nat := 216675485700402180584381

theorem tailTrace_632961 : CollatzResearch.WordTrace tailWord_632961 prefixEnd_632961 216675485700402180584381 := by
  unfold tailWord_632961
  simp only [CollatzResearch.WordTrace]
  refine ⟨23085984259897872977538737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15390656173265248651692491 23085984259897872977538737)
  ·
    refine ⟨17314488194923404733154053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23085984259897872977538737 17314488194923404733154053)
    ·
      refine ⟨3246466536548138387466385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17314488194923404733154053 3246466536548138387466385)
      ·
        refine ⟨2434849902411103790599789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3246466536548138387466385 2434849902411103790599789)
        ·
          refine ⟨913068713404163921474921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2434849902411103790599789 913068713404163921474921)
          ·
            refine ⟨684801535053122941106191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 913068713404163921474921 684801535053122941106191)
            ·
              refine ⟨1027202302579684411659287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 684801535053122941106191 1027202302579684411659287)
              ·
                refine ⟨1540803453869526617488931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1027202302579684411659287 1540803453869526617488931)
                ·
                  refine ⟨2311205180804289926233397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1540803453869526617488931 2311205180804289926233397)
                  ·
                    refine ⟨216675485700402180584381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2311205180804289926233397 216675485700402180584381)
                    ·
                      rfl

theorem cell22_632961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 2, 1, 1, 1, 5].length) (baseStart_632961 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_632961 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_632961 prefixEnd_632961 := by exact prefixLift 632961
  have htrace : WordTrace (prefixWord ++ tailWord_632961) baseStart_632961 baseEnd_632961 := by
    simpa [prefixWord, tailWord_632961, baseEnd_632961] using wordTrace_append hprefix tailTrace_632961
  have hstable : (prefixWord ++ tailWord_632961).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_632961).length < 2 ^ (prefixWord ++ tailWord_632961).sum := by decide
  have hdescent : baseEnd_632961 < baseStart_632961 := by decide
  rcases family_descends (prefixWord ++ tailWord_632961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_632974 : List Nat := [4, 1, 1, 3, 3, 1, 1, 8]
def baseStart_632974 : Nat := 118140960795 + 632974 * 2 ^ 59
def prefixEnd_632974 : Nat := 4983230072969 + 3 ^ 40 * 632974 * 2
def baseEnd_632974 : Nat := 24075548429563831112149

theorem tailTrace_632974 : CollatzResearch.WordTrace tailWord_632974 prefixEnd_632974 24075548429563831112149 := by
  unfold tailWord_632974
  simp only [CollatzResearch.WordTrace]
  refine ⟨2885807301106347024720247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15390972272567184131841317 2885807301106347024720247)
  ·
    refine ⟨4328710951659520537080371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2885807301106347024720247 4328710951659520537080371)
    ·
      refine ⟨6493066427489280805620557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4328710951659520537080371 6493066427489280805620557)
      ·
        refine ⟨2434899910308480302107709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6493066427489280805620557 2434899910308480302107709)
        ·
          refine ⟨913087466365680113290391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2434899910308480302107709 913087466365680113290391)
          ·
            refine ⟨1369631199548520169935587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 913087466365680113290391 1369631199548520169935587)
            ·
              refine ⟨2054446799322780254903381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1369631199548520169935587 2054446799322780254903381)
              ·
                refine ⟨24075548429563831112149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2054446799322780254903381 24075548429563831112149)
                ·
                  rfl

theorem cell22_632974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 1, 8].length) (baseStart_632974 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_632974 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_632974 prefixEnd_632974 := by exact prefixLift 632974
  have htrace : WordTrace (prefixWord ++ tailWord_632974) baseStart_632974 baseEnd_632974 := by
    simpa [prefixWord, tailWord_632974, baseEnd_632974] using wordTrace_append hprefix tailTrace_632974
  have hstable : (prefixWord ++ tailWord_632974).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_632974).length < 2 ^ (prefixWord ++ tailWord_632974).sum := by decide
  have hdescent : baseEnd_632974 < baseStart_632974 := by decide
  rcases family_descends (prefixWord ++ tailWord_632974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_632980 : List Nat := [2, 4, 2, 3, 1, 2, 1, 3, 4]
def baseStart_632980 : Nat := 118140960795 + 632980 * 2 ^ 59
def prefixEnd_632980 : Nat := 4983230072969 + 3 ^ 40 * 632980 * 2
def baseEnd_632980 : Nat := 72227329929564154786441

theorem tailTrace_632980 : CollatzResearch.WordTrace tailWord_632980 prefixEnd_632980 72227329929564154786441 := by
  unfold tailWord_632980
  simp only [CollatzResearch.WordTrace]
  refine ⟨11543338623414519611240197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15391118164552692814986929 11543338623414519611240197)
  ·
    refine ⟨2164375991890222427107537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11543338623414519611240197 2164375991890222427107537)
    ·
      refine ⟨1623281993917666820330653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2164375991890222427107537 1623281993917666820330653)
      ·
        refine ⟨608730747719125057623995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1623281993917666820330653 608730747719125057623995)
        ·
          refine ⟨913096121578687586435993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 608730747719125057623995 913096121578687586435993)
          ·
            refine ⟨684822091184015689826995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 913096121578687586435993 684822091184015689826995)
            ·
              refine ⟨1027233136776023534740493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 684822091184015689826995 1027233136776023534740493)
              ·
                refine ⟨385212426291008825527685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1027233136776023534740493 385212426291008825527685)
                ·
                  refine ⟨72227329929564154786441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 385212426291008825527685 72227329929564154786441)
                  ·
                    rfl

theorem cell22_632980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 2, 1, 3, 4].length) (baseStart_632980 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_632980 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_632980 prefixEnd_632980 := by exact prefixLift 632980
  have htrace : WordTrace (prefixWord ++ tailWord_632980) baseStart_632980 baseEnd_632980 := by
    simpa [prefixWord, tailWord_632980, baseEnd_632980] using wordTrace_append hprefix tailTrace_632980
  have hstable : (prefixWord ++ tailWord_632980).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_632980).length < 2 ^ (prefixWord ++ tailWord_632980).sum := by decide
  have hdescent : baseEnd_632980 < baseStart_632980 := by decide
  rcases family_descends (prefixWord ++ tailWord_632980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_633012 : List Nat := [2, 5, 3, 1, 1, 1, 1, 3, 2, 3]
def baseStart_633012 : Nat := 118140960795 + 633012 * 2 ^ 59
def prefixEnd_633012 : Nat := 4983230072969 + 3 ^ 40 * 633012 * 2
def baseEnd_633012 : Nat := 216692944042655047559225

theorem tailTrace_633012 : CollatzResearch.WordTrace tailWord_633012 prefixEnd_633012 216692944042655047559225 := by
  unfold tailWord_633012
  simp only [CollatzResearch.WordTrace]
  refine ⟨11543922191356554343822645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15391896255142072458430193 11543922191356554343822645)
  ·
    refine ⟨1082242705439676969733373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 11543922191356554343822645 1082242705439676969733373)
    ·
      refine ⟨405841014539878863650015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1082242705439676969733373 405841014539878863650015)
      ·
        refine ⟨608761521809818295475023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 405841014539878863650015 608761521809818295475023)
        ·
          refine ⟨913142282714727443212535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 608761521809818295475023 913142282714727443212535)
          ·
            refine ⟨1369713424072091164818803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 913142282714727443212535 1369713424072091164818803)
            ·
              refine ⟨2054570136108136747228205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1369713424072091164818803 2054570136108136747228205)
              ·
                refine ⟨770463801040551280210577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2054570136108136747228205 770463801040551280210577)
                ·
                  refine ⟨577847850780413460157933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 770463801040551280210577 577847850780413460157933)
                  ·
                    refine ⟨216692944042655047559225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 577847850780413460157933 216692944042655047559225)
                    ·
                      rfl

theorem cell22_633012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 1, 3, 2, 3].length) (baseStart_633012 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_633012 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_633012 prefixEnd_633012 := by exact prefixLift 633012
  have htrace : WordTrace (prefixWord ++ tailWord_633012) baseStart_633012 baseEnd_633012 := by
    simpa [prefixWord, tailWord_633012, baseEnd_633012] using wordTrace_append hprefix tailTrace_633012
  have hstable : (prefixWord ++ tailWord_633012).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_633012).length < 2 ^ (prefixWord ++ tailWord_633012).sum := by decide
  have hdescent : baseEnd_633012 < baseStart_633012 := by decide
  rcases family_descends (prefixWord ++ tailWord_633012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_633017 : List Nat := [1, 2, 1, 4, 1, 2, 2, 1, 1, 7]
def baseStart_633017 : Nat := 118140960795 + 633017 * 2 ^ 59
def prefixEnd_633017 : Nat := 4983230072969 + 3 ^ 40 * 633017 * 2
def baseEnd_633017 : Nat := 216694655644836701184209

theorem tailTrace_633017 : CollatzResearch.WordTrace tailWord_633017 prefixEnd_633017 216694655644836701184209 := by
  unfold tailWord_633017
  simp only [CollatzResearch.WordTrace]
  refine ⟨23088026747694994541577305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15392017831796663027718203 23088026747694994541577305)
  ·
    refine ⟨17316020060771245906182979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23088026747694994541577305 17316020060771245906182979)
    ·
      refine ⟨25974030091156868859274469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17316020060771245906182979 25974030091156868859274469)
      ·
        refine ⟨4870130642091912911113963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25974030091156868859274469 4870130642091912911113963)
        ·
          refine ⟨7305195963137869366670945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4870130642091912911113963 7305195963137869366670945)
          ·
            refine ⟨5478896972353402025003209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7305195963137869366670945 5478896972353402025003209)
            ·
              refine ⟨4109172729265051518752407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5478896972353402025003209 4109172729265051518752407)
              ·
                refine ⟨6163759093897577278128611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4109172729265051518752407 6163759093897577278128611)
                ·
                  refine ⟨9245638640846365917192917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6163759093897577278128611 9245638640846365917192917)
                  ·
                    refine ⟨216694655644836701184209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 9245638640846365917192917 216694655644836701184209)
                    ·
                      rfl

theorem cell22_633017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 2, 1, 1, 7].length) (baseStart_633017 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_633017 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_633017 prefixEnd_633017 := by exact prefixLift 633017
  have htrace : WordTrace (prefixWord ++ tailWord_633017) baseStart_633017 baseEnd_633017 := by
    simpa [prefixWord, tailWord_633017, baseEnd_633017] using wordTrace_append hprefix tailTrace_633017
  have hstable : (prefixWord ++ tailWord_633017).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_633017).length < 2 ^ (prefixWord ++ tailWord_633017).sum := by decide
  have hdescent : baseEnd_633017 < baseStart_633017 := by decide
  rcases family_descends (prefixWord ++ tailWord_633017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_633049 : List Nat := [1, 2, 1, 2, 3, 1, 2, 5, 1, 4]
def baseStart_633049 : Nat := 118140960795 + 633049 * 2 ^ 59
def prefixEnd_633049 : Nat := 4983230072969 + 3 ^ 40 * 633049 * 2
def baseEnd_633049 : Nat := 216705609898799284384111

theorem tailTrace_633049 : CollatzResearch.WordTrace tailWord_633049 prefixEnd_633049 216705609898799284384111 := by
  unfold tailWord_633049
  simp only [CollatzResearch.WordTrace]
  refine ⟨23089193883579064006742201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15392795922386042671161467 23089193883579064006742201)
  ·
    refine ⟨17316895412684298005056651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23089193883579064006742201 17316895412684298005056651)
    ·
      refine ⟨25975343119026447007584977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17316895412684298005056651 25975343119026447007584977)
      ·
        refine ⟨19481507339269835255688733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25975343119026447007584977 19481507339269835255688733)
        ·
          refine ⟨7305565252226188220883275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19481507339269835255688733 7305565252226188220883275)
          ·
            refine ⟨10958347878339282331324913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7305565252226188220883275 10958347878339282331324913)
            ·
              refine ⟨8218760908754461748493685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10958347878339282331324913 8218760908754461748493685)
              ·
                refine ⟨770508835195730788921283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8218760908754461748493685 770508835195730788921283)
                ·
                  refine ⟨1155763252793596183381925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 770508835195730788921283 1155763252793596183381925)
                  ·
                    refine ⟨216705609898799284384111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1155763252793596183381925 216705609898799284384111)
                    ·
                      rfl

theorem cell22_633049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 5, 1, 4].length) (baseStart_633049 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_633049 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_633049 prefixEnd_633049 := by exact prefixLift 633049
  have htrace : WordTrace (prefixWord ++ tailWord_633049) baseStart_633049 baseEnd_633049 := by
    simpa [prefixWord, tailWord_633049, baseEnd_633049] using wordTrace_append hprefix tailTrace_633049
  have hstable : (prefixWord ++ tailWord_633049).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_633049).length < 2 ^ (prefixWord ++ tailWord_633049).sum := by decide
  have hdescent : baseEnd_633049 < baseStart_633049 := by decide
  rcases family_descends (prefixWord ++ tailWord_633049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_633107 : List Nat := [1, 1, 1, 2, 1, 3, 1, 2, 1, 9]
def baseStart_633107 : Nat := 118140960795 + 633107 * 2 ^ 59
def prefixEnd_633107 : Nat := 4983230072969 + 3 ^ 40 * 633107 * 2
def baseEnd_633107 : Nat := 216725464484106466433933

theorem tailTrace_633107 : CollatzResearch.WordTrace tailWord_633107 prefixEnd_633107 216725464484106466433933 := by
  unfold tailWord_633107
  simp only [CollatzResearch.WordTrace]
  refine ⟨23091309317368939912353575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15394206211579293274902383 23091309317368939912353575)
  ·
    refine ⟨34636963976053409868530363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23091309317368939912353575 34636963976053409868530363)
    ·
      refine ⟨51955445964080114802795545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34636963976053409868530363 51955445964080114802795545)
      ·
        refine ⟨38966584473060086102096659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51955445964080114802795545 38966584473060086102096659)
        ·
          refine ⟨58449876709590129153144989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38966584473060086102096659 58449876709590129153144989)
          ·
            refine ⟨21918703766096298432429371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 58449876709590129153144989 21918703766096298432429371)
            ·
              refine ⟨32878055649144447648644057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21918703766096298432429371 32878055649144447648644057)
              ·
                refine ⟨24658541736858335736483043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32878055649144447648644057 24658541736858335736483043)
                ·
                  refine ⟨36987812605287503604724565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24658541736858335736483043 36987812605287503604724565)
                  ·
                    refine ⟨216725464484106466433933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 36987812605287503604724565 216725464484106466433933)
                    ·
                      rfl

theorem cell22_633107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 2, 1, 9].length) (baseStart_633107 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_633107 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_633107 prefixEnd_633107 := by exact prefixLift 633107
  have htrace : WordTrace (prefixWord ++ tailWord_633107) baseStart_633107 baseEnd_633107 := by
    simpa [prefixWord, tailWord_633107, baseEnd_633107] using wordTrace_append hprefix tailTrace_633107
  have hstable : (prefixWord ++ tailWord_633107).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_633107).length < 2 ^ (prefixWord ++ tailWord_633107).sum := by decide
  have hdescent : baseEnd_633107 < baseStart_633107 := by decide
  rcases family_descends (prefixWord ++ tailWord_633107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_633130 : List Nat := [3, 1, 4, 2, 3, 1, 1, 1, 1, 5]
def baseStart_633130 : Nat := 118140960795 + 633130 * 2 ^ 59
def prefixEnd_633130 : Nat := 4983230072969 + 3 ^ 40 * 633130 * 2
def baseEnd_633130 : Nat := 216733337854142073108863

theorem tailTrace_633130 : CollatzResearch.WordTrace tailWord_633130 prefixEnd_633130 216733337854142073108863 := by
  unfold tailWord_633130
  simp only [CollatzResearch.WordTrace]
  refine ⟨5773037049071403710110211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15394765464190409893627229 5773037049071403710110211)
  ·
    refine ⟨8659555573607105565165317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5773037049071403710110211 8659555573607105565165317)
    ·
      refine ⟨1623666670051332293468497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8659555573607105565165317 1623666670051332293468497)
      ·
        refine ⟨1217750002538499220101373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1623666670051332293468497 1217750002538499220101373)
        ·
          refine ⟨456656250951937207538015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1217750002538499220101373 456656250951937207538015)
          ·
            refine ⟨684984376427905811307023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 456656250951937207538015 684984376427905811307023)
            ·
              refine ⟨1027476564641858716960535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 684984376427905811307023 1027476564641858716960535)
              ·
                refine ⟨1541214846962788075440803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1027476564641858716960535 1541214846962788075440803)
                ·
                  refine ⟨2311822270444182113161205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1541214846962788075440803 2311822270444182113161205)
                  ·
                    refine ⟨216733337854142073108863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2311822270444182113161205 216733337854142073108863)
                    ·
                      rfl

theorem cell22_633130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 3, 1, 1, 1, 1, 5].length) (baseStart_633130 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_633130 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_633130 prefixEnd_633130 := by exact prefixLift 633130
  have htrace : WordTrace (prefixWord ++ tailWord_633130) baseStart_633130 baseEnd_633130 := by
    simpa [prefixWord, tailWord_633130, baseEnd_633130] using wordTrace_append hprefix tailTrace_633130
  have hstable : (prefixWord ++ tailWord_633130).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_633130).length < 2 ^ (prefixWord ++ tailWord_633130).sum := by decide
  have hdescent : baseEnd_633130 < baseStart_633130 := by decide
  rcases family_descends (prefixWord ++ tailWord_633130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_633141 : List Nat := [1, 3, 3, 1, 2, 1, 1, 4, 3, 3]
def baseStart_633141 : Nat := 118140960795 + 633141 * 2 ^ 59
def prefixEnd_633141 : Nat := 4983230072969 + 3 ^ 40 * 633141 * 2
def baseEnd_633141 : Nat := 216737103378941711083829

theorem tailTrace_633141 : CollatzResearch.WordTrace tailWord_633141 prefixEnd_633141 216737103378941711083829 := by
  unfold tailWord_633141
  simp only [CollatzResearch.WordTrace]
  refine ⟨23092549399245763719091277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15395032932830509146060851 23092549399245763719091277)
  ·
    refine ⟨8659706024717161394659229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23092549399245763719091277 8659706024717161394659229)
    ·
      refine ⟨3247389759268935522997211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8659706024717161394659229 3247389759268935522997211)
      ·
        refine ⟨4871084638903403284495817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3247389759268935522997211 4871084638903403284495817)
        ·
          refine ⟨3653313479177552463371863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4871084638903403284495817 3653313479177552463371863)
          ·
            refine ⟨5479970218766328695057795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3653313479177552463371863 5479970218766328695057795)
            ·
              refine ⟨8219955328149493042586693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5479970218766328695057795 8219955328149493042586693)
              ·
                refine ⟨1541241624028029945485005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8219955328149493042586693 1541241624028029945485005)
                ·
                  refine ⟨577965609010511229556877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1541241624028029945485005 577965609010511229556877)
                  ·
                    refine ⟨216737103378941711083829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 577965609010511229556877 216737103378941711083829)
                    ·
                      rfl

theorem cell22_633141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 4, 3, 3].length) (baseStart_633141 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_633141 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_633141 prefixEnd_633141 := by exact prefixLift 633141
  have htrace : WordTrace (prefixWord ++ tailWord_633141) baseStart_633141 baseEnd_633141 := by
    simpa [prefixWord, tailWord_633141, baseEnd_633141] using wordTrace_append hprefix tailTrace_633141
  have hstable : (prefixWord ++ tailWord_633141).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_633141).length < 2 ^ (prefixWord ++ tailWord_633141).sum := by decide
  have hdescent : baseEnd_633141 < baseStart_633141 := by decide
  rcases family_descends (prefixWord ++ tailWord_633141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_633175 : List Nat := [1, 1, 3, 2, 3, 1, 5, 2, 1, 3]
def baseStart_633175 : Nat := 118140960795 + 633175 * 2 ^ 59
def prefixEnd_633175 : Nat := 4983230072969 + 3 ^ 40 * 633175 * 2
def baseEnd_633175 : Nat := 216748742273776955733725

theorem tailTrace_633175 : CollatzResearch.WordTrace tailWord_633175 prefixEnd_633175 216748742273776955733725 := by
  unfold tailWord_633175
  simp only [CollatzResearch.WordTrace]
  refine ⟨23093789481122587525828979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15395859654081725017219319 23093789481122587525828979)
  ·
    refine ⟨34640684221683881288743469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23093789481122587525828979 34640684221683881288743469)
    ·
      refine ⟨12990256583131455483278801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34640684221683881288743469 12990256583131455483278801)
      ·
        refine ⟨9742692437348591612459101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12990256583131455483278801 9742692437348591612459101)
        ·
          refine ⟨3653509664005721854672163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9742692437348591612459101 3653509664005721854672163)
          ·
            refine ⟨5480264496008582782008245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3653509664005721854672163 5480264496008582782008245)
            ·
              refine ⟨513774796500804635813273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5480264496008582782008245 513774796500804635813273)
              ·
                refine ⟨385331097375603476859955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 513774796500804635813273 385331097375603476859955)
                ·
                  refine ⟨577996646063405215289933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 385331097375603476859955 577996646063405215289933)
                  ·
                    refine ⟨216748742273776955733725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 577996646063405215289933 216748742273776955733725)
                    ·
                      rfl

theorem cell22_633175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 5, 2, 1, 3].length) (baseStart_633175 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_633175 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_633175 prefixEnd_633175 := by exact prefixLift 633175
  have htrace : WordTrace (prefixWord ++ tailWord_633175) baseStart_633175 baseEnd_633175 := by
    simpa [prefixWord, tailWord_633175, baseEnd_633175] using wordTrace_append hprefix tailTrace_633175
  have hstable : (prefixWord ++ tailWord_633175).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_633175).length < 2 ^ (prefixWord ++ tailWord_633175).sum := by decide
  have hdescent : baseEnd_633175 < baseStart_633175 := by decide
  rcases family_descends (prefixWord ++ tailWord_633175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_633226 : List Nat := [3, 1, 2, 5, 2, 1, 2, 2, 1, 3]
def baseStart_633226 : Nat := 118140960795 + 633226 * 2 ^ 59
def prefixEnd_633226 : Nat := 4983230072969 + 3 ^ 40 * 633226 * 2
def baseEnd_633226 : Nat := 216766200616029822708569

theorem tailTrace_633226 : CollatzResearch.WordTrace tailWord_633226 prefixEnd_633226 216766200616029822708569 := by
  unfold tailWord_633226
  simp only [CollatzResearch.WordTrace]
  refine ⟨5773912400984455808983883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15397099735958548823957021 5773912400984455808983883)
  ·
    refine ⟨8660868601476683713475825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5773912400984455808983883 8660868601476683713475825)
    ·
      refine ⟨6495651451107512785106869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8660868601476683713475825 6495651451107512785106869)
      ·
        refine ⟨608967323541329323603769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 6495651451107512785106869 608967323541329323603769)
        ·
          refine ⟨456725492655996992702827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 608967323541329323603769 456725492655996992702827)
          ·
            refine ⟨685088238983995489054241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 456725492655996992702827 685088238983995489054241)
            ·
              refine ⟨513816179237996616790681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 685088238983995489054241 513816179237996616790681)
              ·
                refine ⟨385362134428497462593011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 513816179237996616790681 385362134428497462593011)
                ·
                  refine ⟨578043201642746193889517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 385362134428497462593011 578043201642746193889517)
                  ·
                    refine ⟨216766200616029822708569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 578043201642746193889517 216766200616029822708569)
                    ·
                      rfl

theorem cell22_633226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 2, 1, 2, 2, 1, 3].length) (baseStart_633226 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_633226 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_633226 prefixEnd_633226 := by exact prefixLift 633226
  have htrace : WordTrace (prefixWord ++ tailWord_633226) baseStart_633226 baseEnd_633226 := by
    simpa [prefixWord, tailWord_633226, baseEnd_633226] using wordTrace_append hprefix tailTrace_633226
  have hstable : (prefixWord ++ tailWord_633226).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_633226).length < 2 ^ (prefixWord ++ tailWord_633226).sum := by decide
  have hdescent : baseEnd_633226 < baseStart_633226 := by decide
  rcases family_descends (prefixWord ++ tailWord_633226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_633248 : List Nat := [2, 1, 1, 4, 1, 3, 2, 3, 2, 3]
def baseStart_633248 : Nat := 118140960795 + 633248 * 2 ^ 59
def prefixEnd_633248 : Nat := 4983230072969 + 3 ^ 40 * 633248 * 2
def baseEnd_633248 : Nat := 216773731665629098658501

theorem tailTrace_633248 : CollatzResearch.WordTrace tailWord_633248 prefixEnd_633248 216773731665629098658501 := by
  unfold tailWord_633248
  simp only [CollatzResearch.WordTrace]
  refine ⟨11548226004929060496618199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15397634673238747328824265 11548226004929060496618199)
  ·
    refine ⟨17322339007393590744927299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11548226004929060496618199 17322339007393590744927299)
    ·
      refine ⟨25983508511090386117390949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17322339007393590744927299 25983508511090386117390949)
      ·
        refine ⟨4871907845829447397010803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25983508511090386117390949 4871907845829447397010803)
        ·
          refine ⟨7307861768744171095516205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4871907845829447397010803 7307861768744171095516205)
          ·
            refine ⟨2740448163279064160818577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7307861768744171095516205 2740448163279064160818577)
            ·
              refine ⟨2055336122459298120613933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2740448163279064160818577 2055336122459298120613933)
              ·
                refine ⟨770751045922236795230225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2055336122459298120613933 770751045922236795230225)
                ·
                  refine ⟨578063284441677596422669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 770751045922236795230225 578063284441677596422669)
                  ·
                    refine ⟨216773731665629098658501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 578063284441677596422669 216773731665629098658501)
                    ·
                      rfl

theorem cell22_633248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 2, 3, 2, 3].length) (baseStart_633248 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_633248 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_633248 prefixEnd_633248 := by exact prefixLift 633248
  have htrace : WordTrace (prefixWord ++ tailWord_633248) baseStart_633248 baseEnd_633248 := by
    simpa [prefixWord, tailWord_633248, baseEnd_633248] using wordTrace_append hprefix tailTrace_633248
  have hstable : (prefixWord ++ tailWord_633248).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_633248).length < 2 ^ (prefixWord ++ tailWord_633248).sum := by decide
  have hdescent : baseEnd_633248 < baseStart_633248 := by decide
  rcases family_descends (prefixWord ++ tailWord_633248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_633357 : List Nat := [1, 7, 1, 1, 1, 2, 1, 3, 5]
def baseStart_633357 : Nat := 118140960795 + 633357 * 2 ^ 59
def prefixEnd_633357 : Nat := 4983230072969 + 3 ^ 40 * 633357 * 2
def baseEnd_633357 : Nat := 72270348197729715894389

theorem tailTrace_633357 : CollatzResearch.WordTrace tailWord_633357 prefixEnd_633357 72270348197729715894389 := by
  unfold tailWord_633357
  simp only [CollatzResearch.WordTrace]
  refine ⟨23100427566463232608954325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15400285044308821739302883 23100427566463232608954325)
  ·
    refine ⟨541416271088982014272367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 23100427566463232608954325 541416271088982014272367)
    ·
      refine ⟨812124406633473021408551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 541416271088982014272367 812124406633473021408551)
      ·
        refine ⟨1218186609950209532112827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 812124406633473021408551 1218186609950209532112827)
        ·
          refine ⟨1827279914925314298169241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1218186609950209532112827 1827279914925314298169241)
          ·
            refine ⟨1370459936193985723626931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1827279914925314298169241 1370459936193985723626931)
            ·
              refine ⟨2055689904290978585440397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1370459936193985723626931 2055689904290978585440397)
              ·
                refine ⟨770883714109116969540149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2055689904290978585440397 770883714109116969540149)
                ·
                  refine ⟨72270348197729715894389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 770883714109116969540149 72270348197729715894389)
                  ·
                    rfl

theorem cell22_633357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 1, 3, 5].length) (baseStart_633357 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_633357 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_633357 prefixEnd_633357 := by exact prefixLift 633357
  have htrace : WordTrace (prefixWord ++ tailWord_633357) baseStart_633357 baseEnd_633357 := by
    simpa [prefixWord, tailWord_633357, baseEnd_633357] using wordTrace_append hprefix tailTrace_633357
  have hstable : (prefixWord ++ tailWord_633357).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_633357).length < 2 ^ (prefixWord ++ tailWord_633357).sum := by decide
  have hdescent : baseEnd_633357 < baseStart_633357 := by decide
  rcases family_descends (prefixWord ++ tailWord_633357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_633381 : List Nat := [1, 3, 1, 2, 2, 1, 2, 3, 1, 6]
def baseStart_633381 : Nat := 118140960795 + 633381 * 2 ^ 59
def prefixEnd_633381 : Nat := 4983230072969 + 3 ^ 40 * 633381 * 2
def baseEnd_633381 : Nat := 216819260283661085083093

theorem tailTrace_633381 : CollatzResearch.WordTrace tailWord_633381 prefixEnd_633381 216819260283661085083093 := by
  unfold tailWord_633381
  simp only [CollatzResearch.WordTrace]
  refine ⟨23101302918376284707827997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15400868612250856471885331 23101302918376284707827997)
  ·
    refine ⟨8662988594391106765435499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23101302918376284707827997 8662988594391106765435499)
    ·
      refine ⟨12994482891586660148153249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8662988594391106765435499 12994482891586660148153249)
      ·
        refine ⟨9745862168689995111114937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12994482891586660148153249 9745862168689995111114937)
        ·
          refine ⟨7309396626517496333336203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9745862168689995111114937 7309396626517496333336203)
          ·
            refine ⟨10964094939776244500004305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7309396626517496333336203 10964094939776244500004305)
            ·
              refine ⟨8223071204832183375003229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10964094939776244500004305 8223071204832183375003229)
              ·
                refine ⟨3083651701812068765626211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8223071204832183375003229 3083651701812068765626211)
                ·
                  refine ⟨4625477552718103148439317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3083651701812068765626211 4625477552718103148439317)
                  ·
                    refine ⟨216819260283661085083093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4625477552718103148439317 216819260283661085083093)
                    ·
                      rfl

theorem cell22_633381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 3, 1, 6].length) (baseStart_633381 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_633381 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_633381 prefixEnd_633381 := by exact prefixLift 633381
  have htrace : WordTrace (prefixWord ++ tailWord_633381) baseStart_633381 baseEnd_633381 := by
    simpa [prefixWord, tailWord_633381, baseEnd_633381] using wordTrace_append hprefix tailTrace_633381
  have hstable : (prefixWord ++ tailWord_633381).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_633381).length < 2 ^ (prefixWord ++ tailWord_633381).sum := by decide
  have hdescent : baseEnd_633381 < baseStart_633381 := by decide
  rcases family_descends (prefixWord ++ tailWord_633381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_633400 : List Nat := [2, 1, 2, 1, 4, 1, 4, 2, 2, 3]
def baseStart_633400 : Nat := 118140960795 + 633400 * 2 ^ 59
def prefixEnd_633400 : Nat := 4983230072969 + 3 ^ 40 * 633400 * 2
def baseEnd_633400 : Nat := 216825764371951368858035

theorem tailTrace_633400 : CollatzResearch.WordTrace tailWord_633400 prefixEnd_633400 216825764371951368858035 := by
  unfold tailWord_633400
  simp only [CollatzResearch.WordTrace]
  refine ⟨11550997952653725476384827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15401330603538300635179769 11550997952653725476384827)
  ·
    refine ⟨17326496928980588214577241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11550997952653725476384827 17326496928980588214577241)
    ·
      refine ⟨12994872696735441160932931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17326496928980588214577241 12994872696735441160932931)
      ·
        refine ⟨19492309045103161741399397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12994872696735441160932931 19492309045103161741399397)
        ·
          refine ⟨3654807945956842826512387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19492309045103161741399397 3654807945956842826512387)
          ·
            refine ⟨5482211918935264239768581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3654807945956842826512387 5482211918935264239768581)
            ·
              refine ⟨1027914734800362044956609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5482211918935264239768581 1027914734800362044956609)
              ·
                refine ⟨770936051100271533717457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1027914734800362044956609 770936051100271533717457)
                ·
                  refine ⟨578202038325203650288093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 770936051100271533717457 578202038325203650288093)
                  ·
                    refine ⟨216825764371951368858035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 578202038325203650288093 216825764371951368858035)
                    ·
                      rfl

theorem cell22_633400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 4, 2, 2, 3].length) (baseStart_633400 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_633400 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_633400 prefixEnd_633400 := by exact prefixLift 633400
  have htrace : WordTrace (prefixWord ++ tailWord_633400) baseStart_633400 baseEnd_633400 := by
    simpa [prefixWord, tailWord_633400, baseEnd_633400] using wordTrace_append hprefix tailTrace_633400
  have hstable : (prefixWord ++ tailWord_633400).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_633400).length < 2 ^ (prefixWord ++ tailWord_633400).sum := by decide
  have hdescent : baseEnd_633400 < baseStart_633400 := by decide
  rcases family_descends (prefixWord ++ tailWord_633400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_633402 : List Nat := [3, 1, 1, 1, 3, 5, 2, 2, 4]
def baseStart_633402 : Nat := 118140960795 + 633402 * 2 ^ 59
def prefixEnd_633402 : Nat := 4983230072969 + 3 ^ 40 * 633402 * 2
def baseEnd_633402 : Nat := 72275483004274676769343

theorem tailTrace_633402 : CollatzResearch.WordTrace tailWord_633402 prefixEnd_633402 72275483004274676769343 := by
  unfold tailWord_633402
  simp only [CollatzResearch.WordTrace]
  refine ⟨5775517212825051323585615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15401379234200136862894973 5775517212825051323585615)
  ·
    refine ⟨8663275819237576985378423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5775517212825051323585615 8663275819237576985378423)
    ·
      refine ⟨12994913728856365478067635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8663275819237576985378423 12994913728856365478067635)
      ·
        refine ⟨19492370593284548217101453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12994913728856365478067635 19492370593284548217101453)
        ·
          refine ⟨7309638972481705581413045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19492370593284548217101453 7309638972481705581413045)
          ·
            refine ⟨685278653670159898257473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 7309638972481705581413045 685278653670159898257473)
            ·
              refine ⟨513958990252619923693105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 685278653670159898257473 513958990252619923693105)
              ·
                refine ⟨385469242689464942769829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 513958990252619923693105 385469242689464942769829)
                ·
                  refine ⟨72275483004274676769343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 385469242689464942769829 72275483004274676769343)
                  ·
                    rfl

theorem cell22_633402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 5, 2, 2, 4].length) (baseStart_633402 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_633402 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_633402 prefixEnd_633402 := by exact prefixLift 633402
  have htrace : WordTrace (prefixWord ++ tailWord_633402) baseStart_633402 baseEnd_633402 := by
    simpa [prefixWord, tailWord_633402, baseEnd_633402] using wordTrace_append hprefix tailTrace_633402
  have hstable : (prefixWord ++ tailWord_633402).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_633402).length < 2 ^ (prefixWord ++ tailWord_633402).sum := by decide
  have hdescent : baseEnd_633402 < baseStart_633402 := by decide
  rcases family_descends (prefixWord ++ tailWord_633402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_633413 : List Nat := [1, 3, 1, 1, 1, 7, 1, 7]
def baseStart_633413 : Nat := 118140960795 + 633413 * 2 ^ 59
def prefixEnd_633413 : Nat := 4983230072969 + 3 ^ 40 * 633413 * 2
def baseEnd_633413 : Nat := 24092246059735963142555

theorem tailTrace_633413 : CollatzResearch.WordTrace tailWord_633413 prefixEnd_633413 24092246059735963142555 := by
  unfold tailWord_633413
  simp only [CollatzResearch.WordTrace]
  refine ⟨23102470054260354172992893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15401646702840236115328595 23102470054260354172992893)
  ·
    refine ⟨8663426270347632814872335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23102470054260354172992893 8663426270347632814872335)
    ·
      refine ⟨12995139405521449222308503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8663426270347632814872335 12995139405521449222308503)
      ·
        refine ⟨19492709108282173833462755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12995139405521449222308503 19492709108282173833462755)
        ·
          refine ⟨29239063662423260750194133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19492709108282173833462755 29239063662423260750194133)
          ·
            refine ⟨685290554588045173832675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 29239063662423260750194133 685290554588045173832675)
            ·
              refine ⟨1027935831882067760749013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 685290554588045173832675 1027935831882067760749013)
              ·
                refine ⟨24092246059735963142555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1027935831882067760749013 24092246059735963142555)
                ·
                  rfl

theorem cell22_633413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 7, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 7, 1, 7].length) (baseStart_633413 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_633413 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_633413 prefixEnd_633413 := by exact prefixLift 633413
  have htrace : WordTrace (prefixWord ++ tailWord_633413) baseStart_633413 baseEnd_633413 := by
    simpa [prefixWord, tailWord_633413, baseEnd_633413] using wordTrace_append hprefix tailTrace_633413
  have hstable : (prefixWord ++ tailWord_633413).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_633413).length < 2 ^ (prefixWord ++ tailWord_633413).sum := by decide
  have hdescent : baseEnd_633413 < baseStart_633413 := by decide
  rcases family_descends (prefixWord ++ tailWord_633413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_633438 : List Nat := [4, 4, 1, 2, 1, 2, 2, 1, 1, 4]
def baseStart_633438 : Nat := 118140960795 + 633438 * 2 ^ 59
def prefixEnd_633438 : Nat := 4983230072969 + 3 ^ 40 * 633438 * 2
def baseEnd_633438 : Nat := 216838772548531936407919

theorem tailTrace_633438 : CollatzResearch.WordTrace tailWord_633438 prefixEnd_633438 216838772548531936407919 := by
  unfold tailWord_633438
  simp only [CollatzResearch.WordTrace]
  refine ⟨2887922734896222930331621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15402254586113188961768645 2887922734896222930331621)
  ·
    refine ⟨541485512793041799437179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2887922734896222930331621 541485512793041799437179)
    ·
      refine ⟨812228269189562699155769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 541485512793041799437179 812228269189562699155769)
      ·
        refine ⟨609171201892172024366827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 812228269189562699155769 609171201892172024366827)
        ·
          refine ⟨913756802838258036550241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 609171201892172024366827 913756802838258036550241)
          ·
            refine ⟨685317602128693527412681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 913756802838258036550241 685317602128693527412681)
            ·
              refine ⟨513988201596520145559511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 685317602128693527412681 513988201596520145559511)
              ·
                refine ⟨770982302394780218339267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 513988201596520145559511 770982302394780218339267)
                ·
                  refine ⟨1156473453592170327508901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 770982302394780218339267 1156473453592170327508901)
                  ·
                    refine ⟨216838772548531936407919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1156473453592170327508901 216838772548531936407919)
                    ·
                      rfl

theorem cell22_633438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 2, 2, 1, 1, 4].length) (baseStart_633438 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_633438 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_633438 prefixEnd_633438 := by exact prefixLift 633438
  have htrace : WordTrace (prefixWord ++ tailWord_633438) baseStart_633438 baseEnd_633438 := by
    simpa [prefixWord, tailWord_633438, baseEnd_633438] using wordTrace_append hprefix tailTrace_633438
  have hstable : (prefixWord ++ tailWord_633438).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_633438).length < 2 ^ (prefixWord ++ tailWord_633438).sum := by decide
  have hdescent : baseEnd_633438 < baseStart_633438 := by decide
  rcases family_descends (prefixWord ++ tailWord_633438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_633471 : List Nat := [1, 1, 2, 2, 1, 1, 1, 3, 2, 8]
def baseStart_633471 : Nat := 118140960795 + 633471 * 2 ^ 59
def prefixEnd_633471 : Nat := 4983230072969 + 3 ^ 40 * 633471 * 2
def baseEnd_633471 : Nat := 216850069122930850332817

theorem tailTrace_633471 : CollatzResearch.WordTrace tailWord_633471 prefixEnd_633471 216850069122930850332817 := by
  unfold tailWord_633471
  simp only [CollatzResearch.WordTrace]
  refine ⟨23104585488050230078604267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15403056992033486719069511 23104585488050230078604267)
  ·
    refine ⟨34656878232075345117906401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23104585488050230078604267 34656878232075345117906401)
    ·
      refine ⟨25992658674056508838429801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34656878232075345117906401 25992658674056508838429801)
      ·
        refine ⟨19494494005542381628822351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25992658674056508838429801 19494494005542381628822351)
        ·
          refine ⟨29241741008313572443233527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19494494005542381628822351 29241741008313572443233527)
          ·
            refine ⟨43862611512470358664850291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29241741008313572443233527 43862611512470358664850291)
            ·
              refine ⟨65793917268705537997275437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43862611512470358664850291 65793917268705537997275437)
              ·
                refine ⟨24672718975764576748978289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 65793917268705537997275437 24672718975764576748978289)
                ·
                  refine ⟨18504539231823432561733717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24672718975764576748978289 18504539231823432561733717)
                  ·
                    refine ⟨216850069122930850332817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 18504539231823432561733717 216850069122930850332817)
                    ·
                      rfl

theorem cell22_633471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 3, 2, 8].length) (baseStart_633471 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_633471 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_633471 prefixEnd_633471 := by exact prefixLift 633471
  have htrace : WordTrace (prefixWord ++ tailWord_633471) baseStart_633471 baseEnd_633471 := by
    simpa [prefixWord, tailWord_633471, baseEnd_633471] using wordTrace_append hprefix tailTrace_633471
  have hstable : (prefixWord ++ tailWord_633471).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_633471).length < 2 ^ (prefixWord ++ tailWord_633471).sum := by decide
  have hdescent : baseEnd_633471 < baseStart_633471 := by decide
  rcases family_descends (prefixWord ++ tailWord_633471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_633473 : List Nat := [1, 2, 4, 2, 1, 1, 1, 3, 2, 5]
def baseStart_633473 : Nat := 118140960795 + 633473 * 2 ^ 59
def prefixEnd_633473 : Nat := 4983230072969 + 3 ^ 40 * 633473 * 2
def baseEnd_633473 : Nat := 216850753763803511782811

theorem tailTrace_633473 : CollatzResearch.WordTrace tailWord_633473 prefixEnd_633473 216850753763803511782811 := by
  unfold tailWord_633473
  simp only [CollatzResearch.WordTrace]
  refine ⟨23104658434042984420177073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15403105622695322946784715 23104658434042984420177073)
  ·
    refine ⟨17328493825532238315132805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23104658434042984420177073 17328493825532238315132805)
    ·
      refine ⟨3249092592287294684087401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17328493825532238315132805 3249092592287294684087401)
      ·
        refine ⟨2436819444215471013065551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3249092592287294684087401 2436819444215471013065551)
        ·
          refine ⟨3655229166323206519598327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2436819444215471013065551 3655229166323206519598327)
          ·
            refine ⟨5482843749484809779397491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3655229166323206519598327 5482843749484809779397491)
            ·
              refine ⟨8224265624227214669096237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5482843749484809779397491 8224265624227214669096237)
              ·
                refine ⟨3084099609085205500911089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8224265624227214669096237 3084099609085205500911089)
                ·
                  refine ⟨2313074706813904125683317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3084099609085205500911089 2313074706813904125683317)
                  ·
                    refine ⟨216850753763803511782811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2313074706813904125683317 216850753763803511782811)
                    ·
                      rfl

theorem cell22_633473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 3, 2, 5].length) (baseStart_633473 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_633473 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_633473 prefixEnd_633473 := by exact prefixLift 633473
  have htrace : WordTrace (prefixWord ++ tailWord_633473) baseStart_633473 baseEnd_633473 := by
    simpa [prefixWord, tailWord_633473, baseEnd_633473] using wordTrace_append hprefix tailTrace_633473
  have hstable : (prefixWord ++ tailWord_633473).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_633473).length < 2 ^ (prefixWord ++ tailWord_633473).sum := by decide
  have hdescent : baseEnd_633473 < baseStart_633473 := by decide
  rcases family_descends (prefixWord ++ tailWord_633473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_633526 : List Nat := [5, 1, 3, 1, 2, 2, 2, 1, 5]
def baseStart_633526 : Nat := 118140960795 + 633526 * 2 ^ 59
def prefixEnd_633526 : Nat := 4983230072969 + 3 ^ 40 * 633526 * 2
def baseEnd_633526 : Nat := 72289632248976346735883

theorem tailTrace_633526 : CollatzResearch.WordTrace tailWord_633526 prefixEnd_633526 72289632248976346735883 := by
  unfold tailWord_633526
  simp only [CollatzResearch.WordTrace]
  refine ⟨1444161968928185904491027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 15404394335233982981237621 1444161968928185904491027)
  ·
    refine ⟨2166242953392278856736541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1444161968928185904491027 2166242953392278856736541)
    ·
      refine ⟨812341107522104571276203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2166242953392278856736541 812341107522104571276203)
      ·
        refine ⟨1218511661283156856914305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 812341107522104571276203 1218511661283156856914305)
        ·
          refine ⟨913883745962367642685729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1218511661283156856914305 913883745962367642685729)
          ·
            refine ⟨685412809471775732014297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 913883745962367642685729 685412809471775732014297)
            ·
              refine ⟨514059607103831799010723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 685412809471775732014297 514059607103831799010723)
              ·
                refine ⟨771089410655747698516085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 514059607103831799010723 771089410655747698516085)
                ·
                  refine ⟨72289632248976346735883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 771089410655747698516085 72289632248976346735883)
                  ·
                    rfl

theorem cell22_633526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 2, 2, 1, 5].length) (baseStart_633526 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_633526 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_633526 prefixEnd_633526 := by exact prefixLift 633526
  have htrace : WordTrace (prefixWord ++ tailWord_633526) baseStart_633526 baseEnd_633526 := by
    simpa [prefixWord, tailWord_633526, baseEnd_633526] using wordTrace_append hprefix tailTrace_633526
  have hstable : (prefixWord ++ tailWord_633526).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_633526).length < 2 ^ (prefixWord ++ tailWord_633526).sum := by decide
  have hdescent : baseEnd_633526 < baseStart_633526 := by decide
  rcases family_descends (prefixWord ++ tailWord_633526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_633550 : List Nat := [4, 1, 1, 1, 3, 2, 1, 3, 2, 4]
def baseStart_633550 : Nat := 118140960795 + 633550 * 2 ^ 59
def prefixEnd_633550 : Nat := 4983230072969 + 3 ^ 40 * 633550 * 2
def baseEnd_633550 : Nat := 216877112437400977607575

theorem tailTrace_633550 : CollatzResearch.WordTrace tailWord_633550 prefixEnd_633550 216877112437400977607575 := by
  unfold tailWord_633550
  simp only [CollatzResearch.WordTrace]
  refine ⟨2888433356845503321341263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15404977903176017713820069 2888433356845503321341263)
  ·
    refine ⟨4332650035268254982011895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2888433356845503321341263 4332650035268254982011895)
    ·
      refine ⟨6498975052902382473017843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4332650035268254982011895 6498975052902382473017843)
      ·
        refine ⟨9748462579353573709526765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6498975052902382473017843 9748462579353573709526765)
        ·
          refine ⟨3655673467257590141072537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9748462579353573709526765 3655673467257590141072537)
          ·
            refine ⟨2741755100443192605804403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3655673467257590141072537 2741755100443192605804403)
            ·
              refine ⟨4112632650664788908706605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2741755100443192605804403 4112632650664788908706605)
              ·
                refine ⟨1542237243999295840764977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4112632650664788908706605 1542237243999295840764977)
                ·
                  refine ⟨1156677932999471880573733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1542237243999295840764977 1156677932999471880573733)
                  ·
                    refine ⟨216877112437400977607575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1156677932999471880573733 216877112437400977607575)
                    ·
                      rfl

theorem cell22_633550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 1, 3, 2, 4].length) (baseStart_633550 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_633550 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_633550 prefixEnd_633550 := by exact prefixLift 633550
  have htrace : WordTrace (prefixWord ++ tailWord_633550) baseStart_633550 baseEnd_633550 := by
    simpa [prefixWord, tailWord_633550, baseEnd_633550] using wordTrace_append hprefix tailTrace_633550
  have hstable : (prefixWord ++ tailWord_633550).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_633550).length < 2 ^ (prefixWord ++ tailWord_633550).sum := by decide
  have hdescent : baseEnd_633550 < baseStart_633550 := by decide
  rcases family_descends (prefixWord ++ tailWord_633550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_633580 : List Nat := [2, 2, 1, 1, 2, 2, 1, 5, 3, 3]
def baseStart_633580 : Nat := 118140960795 + 633580 * 2 ^ 59
def prefixEnd_633580 : Nat := 4983230072969 + 3 ^ 40 * 633580 * 2
def baseEnd_633580 : Nat := 216887382050490899357483

theorem tailTrace_633580 : CollatzResearch.WordTrace tailWord_633580 prefixEnd_633580 216887382050490899357483 := by
  unfold tailWord_633580
  simp only [CollatzResearch.WordTrace]
  refine ⟨11554280522327670847161097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15405707363103561129548129 11554280522327670847161097)
  ·
    refine ⟨8665710391745753135370823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11554280522327670847161097 8665710391745753135370823)
    ·
      refine ⟨12998565587618629703056235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8665710391745753135370823 12998565587618629703056235)
      ·
        refine ⟨19497848381427944554584353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12998565587618629703056235 19497848381427944554584353)
        ·
          refine ⟨14623386286070958415938265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19497848381427944554584353 14623386286070958415938265)
          ·
            refine ⟨10967539714553218811953699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14623386286070958415938265 10967539714553218811953699)
            ·
              refine ⟨16451309571829828217930549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10967539714553218811953699 16451309571829828217930549)
              ·
                refine ⟨1542310272359046395430989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16451309571829828217930549 1542310272359046395430989)
                ·
                  refine ⟨578366352134642398286621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1542310272359046395430989 578366352134642398286621)
                  ·
                    refine ⟨216887382050490899357483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 578366352134642398286621 216887382050490899357483)
                    ·
                      rfl

theorem cell22_633580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 3, 3].length) (baseStart_633580 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_633580 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_633580 prefixEnd_633580 := by exact prefixLift 633580
  have htrace : WordTrace (prefixWord ++ tailWord_633580) baseStart_633580 baseEnd_633580 := by
    simpa [prefixWord, tailWord_633580, baseEnd_633580] using wordTrace_append hprefix tailTrace_633580
  have hstable : (prefixWord ++ tailWord_633580).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_633580).length < 2 ^ (prefixWord ++ tailWord_633580).sum := by decide
  have hdescent : baseEnd_633580 < baseStart_633580 := by decide
  rcases family_descends (prefixWord ++ tailWord_633580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_633665 : List Nat := [1, 2, 5, 3, 2, 1, 1, 3, 1, 3]
def baseStart_633665 : Nat := 118140960795 + 633665 * 2 ^ 59
def prefixEnd_633665 : Nat := 4983230072969 + 3 ^ 40 * 633665 * 2
def baseEnd_633665 : Nat := 216916479287579010982223

theorem tailTrace_633665 : CollatzResearch.WordTrace tailWord_633665 prefixEnd_633665 216916479287579010982223 := by
  unfold tailWord_633665
  simp only [CollatzResearch.WordTrace]
  refine ⟨23111661249347401211166449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15407774166231600807444299 23111661249347401211166449)
  ·
    refine ⟨17333745937010550908374837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23111661249347401211166449 17333745937010550908374837)
    ·
      refine ⟨1625038681594739147660141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 17333745937010550908374837 1625038681594739147660141)
      ·
        refine ⟨609389505598027180372553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1625038681594739147660141 609389505598027180372553)
        ·
          refine ⟨457042129198520385279415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 609389505598027180372553 457042129198520385279415)
          ·
            refine ⟨685563193797780577919123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 457042129198520385279415 685563193797780577919123)
            ·
              refine ⟨1028344790696670866878685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 685563193797780577919123 1028344790696670866878685)
              ·
                refine ⟨385629296511251575079507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1028344790696670866878685 385629296511251575079507)
                ·
                  refine ⟨578443944766877362619261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 385629296511251575079507 578443944766877362619261)
                  ·
                    refine ⟨216916479287579010982223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 578443944766877362619261 216916479287579010982223)
                    ·
                      rfl

theorem cell22_633665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 2, 1, 1, 3, 1, 3].length) (baseStart_633665 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_633665 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_633665 prefixEnd_633665 := by exact prefixLift 633665
  have htrace : WordTrace (prefixWord ++ tailWord_633665) baseStart_633665 baseEnd_633665 := by
    simpa [prefixWord, tailWord_633665, baseEnd_633665] using wordTrace_append hprefix tailTrace_633665
  have hstable : (prefixWord ++ tailWord_633665).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_633665).length < 2 ^ (prefixWord ++ tailWord_633665).sum := by decide
  have hdescent : baseEnd_633665 < baseStart_633665 := by decide
  rcases family_descends (prefixWord ++ tailWord_633665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_633687 : List Nat := [1, 1, 3, 2, 4, 1, 2, 1, 4, 3]
def baseStart_633687 : Nat := 118140960795 + 633687 * 2 ^ 59
def prefixEnd_633687 : Nat := 4983230072969 + 3 ^ 40 * 633687 * 2
def baseEnd_633687 : Nat := 216924010337178286932155

theorem tailTrace_633687 : CollatzResearch.WordTrace tailWord_633687 prefixEnd_633687 216924010337178286932155 := by
  unfold tailWord_633687
  simp only [CollatzResearch.WordTrace]
  refine ⟨23112463655267698968467315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15408309103511799312311543 23112463655267698968467315)
  ·
    refine ⟨34668695482901548452700973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23112463655267698968467315 34668695482901548452700973)
    ·
      refine ⟨13000760806088080669762865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34668695482901548452700973 13000760806088080669762865)
      ·
        refine ⟨9750570604566060502322149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13000760806088080669762865 9750570604566060502322149)
        ·
          refine ⟨1828231988356136344185403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9750570604566060502322149 1828231988356136344185403)
          ·
            refine ⟨2742347982534204516278105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1828231988356136344185403 2742347982534204516278105)
            ·
              refine ⟨2056760986900653387208579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2742347982534204516278105 2056760986900653387208579)
              ·
                refine ⟨3085141480350980080812869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2056760986900653387208579 3085141480350980080812869)
                ·
                  refine ⟨578464027565808765152413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3085141480350980080812869 578464027565808765152413)
                  ·
                    refine ⟨216924010337178286932155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 578464027565808765152413 216924010337178286932155)
                    ·
                      rfl

theorem cell22_633687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 2, 1, 4, 3].length) (baseStart_633687 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_633687 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_633687 prefixEnd_633687 := by exact prefixLift 633687
  have htrace : WordTrace (prefixWord ++ tailWord_633687) baseStart_633687 baseEnd_633687 := by
    simpa [prefixWord, tailWord_633687, baseEnd_633687] using wordTrace_append hprefix tailTrace_633687
  have hstable : (prefixWord ++ tailWord_633687).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_633687).length < 2 ^ (prefixWord ++ tailWord_633687).sum := by decide
  have hdescent : baseEnd_633687 < baseStart_633687 := by decide
  rcases family_descends (prefixWord ++ tailWord_633687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_633689 : List Nat := [1, 2, 1, 2, 2, 5, 3, 2, 4]
def baseStart_633689 : Nat := 118140960795 + 633689 * 2 ^ 59
def prefixEnd_633689 : Nat := 4983230072969 + 3 ^ 40 * 633689 * 2
def baseEnd_633689 : Nat := 72308231659350316127383

theorem tailTrace_633689 : CollatzResearch.WordTrace tailWord_633689 prefixEnd_633689 72308231659350316127383 := by
  unfold tailWord_633689
  simp only [CollatzResearch.WordTrace]
  refine ⟨23112536601260453310040121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15408357734173635540026747 23112536601260453310040121)
  ·
    refine ⟨17334402450945339982530091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23112536601260453310040121 17334402450945339982530091)
    ·
      refine ⟨26001603676418009973795137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17334402450945339982530091 26001603676418009973795137)
      ·
        refine ⟨19501202757313507480346353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26001603676418009973795137 19501202757313507480346353)
        ·
          refine ⟨14625902067985130610259765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19501202757313507480346353 14625902067985130610259765)
          ·
            refine ⟨1371178318873605994711853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 14625902067985130610259765 1371178318873605994711853)
            ·
              refine ⟨514191869577602248016945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1371178318873605994711853 514191869577602248016945)
              ·
                refine ⟨385643902183201686012709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 514191869577602248016945 385643902183201686012709)
                ·
                  refine ⟨72308231659350316127383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 385643902183201686012709 72308231659350316127383)
                  ·
                    rfl

theorem cell22_633689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 3, 2, 4].length) (baseStart_633689 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_633689 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_633689 prefixEnd_633689 := by exact prefixLift 633689
  have htrace : WordTrace (prefixWord ++ tailWord_633689) baseStart_633689 baseEnd_633689 := by
    simpa [prefixWord, tailWord_633689, baseEnd_633689] using wordTrace_append hprefix tailTrace_633689
  have hstable : (prefixWord ++ tailWord_633689).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_633689).length < 2 ^ (prefixWord ++ tailWord_633689).sum := by decide
  have hdescent : baseEnd_633689 < baseStart_633689 := by decide
  rcases family_descends (prefixWord ++ tailWord_633689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_633700 : List Nat := [2, 3, 1, 1, 4, 1, 1, 9]
def baseStart_633700 : Nat := 118140960795 + 633700 * 2 ^ 59
def prefixEnd_633700 : Nat := 4983230072969 + 3 ^ 40 * 633700 * 2
def baseEnd_633700 : Nat := 24103162278094509595235

theorem tailTrace_633700 : CollatzResearch.WordTrace tailWord_633700 prefixEnd_633700 24103162278094509595235 := by
  unfold tailWord_633700
  simp only [CollatzResearch.WordTrace]
  refine ⟨11556468902110301094345277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15408625202813734792460369 11556468902110301094345277)
  ·
    refine ⟨4333675838291362910379479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11556468902110301094345277 4333675838291362910379479)
    ·
      refine ⟨6500513757437044365569219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4333675838291362910379479 6500513757437044365569219)
      ·
        refine ⟨9750770636155566548353829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6500513757437044365569219 9750770636155566548353829)
        ·
          refine ⟨1828269494279168727816343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9750770636155566548353829 1828269494279168727816343)
          ·
            refine ⟨2742404241418753091724515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1828269494279168727816343 2742404241418753091724515)
            ·
              refine ⟨4113606362128129637586773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2742404241418753091724515 4113606362128129637586773)
              ·
                refine ⟨24103162278094509595235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 4113606362128129637586773 24103162278094509595235)
                ·
                  rfl

theorem cell22_633700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 1, 9].length) (baseStart_633700 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_633700 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_633700 prefixEnd_633700 := by exact prefixLift 633700
  have htrace : WordTrace (prefixWord ++ tailWord_633700) baseStart_633700 baseEnd_633700 := by
    simpa [prefixWord, tailWord_633700, baseEnd_633700] using wordTrace_append hprefix tailTrace_633700
  have hstable : (prefixWord ++ tailWord_633700).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_633700).length < 2 ^ (prefixWord ++ tailWord_633700).sum := by decide
  have hdescent : baseEnd_633700 < baseStart_633700 := by decide
  rcases family_descends (prefixWord ++ tailWord_633700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_633704 : List Nat := [2, 1, 4, 2, 1, 3, 1, 3, 2, 3]
def baseStart_633704 : Nat := 118140960795 + 633704 * 2 ^ 59
def prefixEnd_633704 : Nat := 4983230072969 + 3 ^ 40 * 633704 * 2
def baseEnd_633704 : Nat := 216929829784595909257103

theorem tailTrace_633704 : CollatzResearch.WordTrace tailWord_633704 prefixEnd_633704 216929829784595909257103 := by
  unfold tailWord_633704
  simp only [CollatzResearch.WordTrace]
  refine ⟨11556541848103055435918083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15408722464137407247890777 11556541848103055435918083)
  ·
    refine ⟨17334812772154583153877125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11556541848103055435918083 17334812772154583153877125)
    ·
      refine ⟨3250277394778984341351961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17334812772154583153877125 3250277394778984341351961)
      ·
        refine ⟨2437708046084238256013971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3250277394778984341351961 2437708046084238256013971)
        ·
          refine ⟨3656562069126357384020957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2437708046084238256013971 3656562069126357384020957)
          ·
            refine ⟨1371210775922384019007859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3656562069126357384020957 1371210775922384019007859)
            ·
              refine ⟨2056816163883576028511789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1371210775922384019007859 2056816163883576028511789)
              ·
                refine ⟨771306061456341010691921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2056816163883576028511789 771306061456341010691921)
                ·
                  refine ⟨578479546092255758018941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 771306061456341010691921 578479546092255758018941)
                  ·
                    refine ⟨216929829784595909257103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 578479546092255758018941 216929829784595909257103)
                    ·
                      rfl

theorem cell22_633704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 1, 3, 2, 3].length) (baseStart_633704 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_633704 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_633704 prefixEnd_633704 := by exact prefixLift 633704
  have htrace : WordTrace (prefixWord ++ tailWord_633704) baseStart_633704 baseEnd_633704 := by
    simpa [prefixWord, tailWord_633704, baseEnd_633704] using wordTrace_append hprefix tailTrace_633704
  have hstable : (prefixWord ++ tailWord_633704).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_633704).length < 2 ^ (prefixWord ++ tailWord_633704).sum := by decide
  have hdescent : baseEnd_633704 < baseStart_633704 := by decide
  rcases family_descends (prefixWord ++ tailWord_633704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_633760 : List Nat := [2, 1, 1, 4, 1, 1, 3, 1, 1, 7]
def baseStart_633760 : Nat := 118140960795 + 633760 * 2 ^ 59
def prefixEnd_633760 : Nat := 4983230072969 + 3 ^ 40 * 633760 * 2
def baseEnd_633760 : Nat := 216948999729030429856931

theorem tailTrace_633760 : CollatzResearch.WordTrace tailWord_633760 prefixEnd_633760 216948999729030429856931 := by
  unfold tailWord_633760
  simp only [CollatzResearch.WordTrace]
  refine ⟨11557563092001616217937367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15410084122668821623916489 11557563092001616217937367)
  ·
    refine ⟨17336344638002424326906051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11557563092001616217937367 17336344638002424326906051)
    ·
      refine ⟨26004516957003636490359077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17336344638002424326906051 26004516957003636490359077)
      ·
        refine ⟨4875846929438181841942327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26004516957003636490359077 4875846929438181841942327)
        ·
          refine ⟨7313770394157272762913491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4875846929438181841942327 7313770394157272762913491)
          ·
            refine ⟨10970655591235909144370237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7313770394157272762913491 10970655591235909144370237)
            ·
              refine ⟨4113995846713465929138839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10970655591235909144370237 4113995846713465929138839)
              ·
                refine ⟨6170993770070198893708259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4113995846713465929138839 6170993770070198893708259)
                ·
                  refine ⟨9256490655105298340562389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6170993770070198893708259 9256490655105298340562389)
                  ·
                    refine ⟨216948999729030429856931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 9256490655105298340562389 216948999729030429856931)
                    ·
                      rfl

theorem cell22_633760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 3, 1, 1, 7].length) (baseStart_633760 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_633760 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_633760 prefixEnd_633760 := by exact prefixLift 633760
  have htrace : WordTrace (prefixWord ++ tailWord_633760) baseStart_633760 baseEnd_633760 := by
    simpa [prefixWord, tailWord_633760, baseEnd_633760] using wordTrace_append hprefix tailTrace_633760
  have hstable : (prefixWord ++ tailWord_633760).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_633760).length < 2 ^ (prefixWord ++ tailWord_633760).sum := by decide
  have hdescent : baseEnd_633760 < baseStart_633760 := by decide
  rcases family_descends (prefixWord ++ tailWord_633760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_633807 : List Nat := [1, 1, 2, 1, 1, 7, 2, 1, 6]
def baseStart_633807 : Nat := 118140960795 + 633807 * 2 ^ 59
def prefixEnd_633807 : Nat := 4983230072969 + 3 ^ 40 * 633807 * 2
def baseEnd_633807 : Nat := 72321696263179324643929

theorem tailTrace_633807 : CollatzResearch.WordTrace tailWord_633807 prefixEnd_633807 72321696263179324643929 := by
  unfold tailWord_633807
  simp only [CollatzResearch.WordTrace]
  refine ⟨23116840414832959462835675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15411226943221972975223783 23116840414832959462835675)
  ·
    refine ⟨34675260622249439194253513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23116840414832959462835675 34675260622249439194253513)
    ·
      refine ⟨26006445466687079395690135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34675260622249439194253513 26006445466687079395690135)
      ·
        refine ⟨39009668200030619093535203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26006445466687079395690135 39009668200030619093535203)
        ·
          refine ⟨58514502300045928640302805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39009668200030619093535203 58514502300045928640302805)
          ·
            refine ⟨1371433647657326452507097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 58514502300045928640302805 1371433647657326452507097)
            ·
              refine ⟨1028575235742994839380323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1371433647657326452507097 1028575235742994839380323)
              ·
                refine ⟨1542862853614492259070485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1028575235742994839380323 1542862853614492259070485)
                ·
                  refine ⟨72321696263179324643929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1542862853614492259070485 72321696263179324643929)
                  ·
                    rfl

theorem cell22_633807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 2, 1, 6].length) (baseStart_633807 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_633807 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_633807 prefixEnd_633807 := by exact prefixLift 633807
  have htrace : WordTrace (prefixWord ++ tailWord_633807) baseStart_633807 baseEnd_633807 := by
    simpa [prefixWord, tailWord_633807, baseEnd_633807] using wordTrace_append hprefix tailTrace_633807
  have hstable : (prefixWord ++ tailWord_633807).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_633807).length < 2 ^ (prefixWord ++ tailWord_633807).sum := by decide
  have hdescent : baseEnd_633807 < baseStart_633807 := by decide
  rcases family_descends (prefixWord ++ tailWord_633807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_633826 : List Nat := [3, 3, 3, 1, 1, 1, 1, 4, 1, 4]
def baseStart_633826 : Nat := 118140960795 + 633826 * 2 ^ 59
def prefixEnd_633826 : Nat := 4983230072969 + 3 ^ 40 * 633826 * 2
def baseEnd_633826 : Nat := 216971592877828257706729

theorem tailTrace_633826 : CollatzResearch.WordTrace tailWord_633826 prefixEnd_633826 216971592877828257706729 := by
  unfold tailWord_633826
  simp only [CollatzResearch.WordTrace]
  refine ⟨5779383350441031426944333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15411688934509417138518221 5779383350441031426944333)
  ·
    refine ⟨2167268756415386785104125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5779383350441031426944333 2167268756415386785104125)
    ·
      refine ⟨812725783655770044414047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2167268756415386785104125 812725783655770044414047)
      ·
        refine ⟨1219088675483655066621071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 812725783655770044414047 1219088675483655066621071)
        ·
          refine ⟨1828633013225482599931607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1219088675483655066621071 1828633013225482599931607)
          ·
            refine ⟨2742949519838223899897411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1828633013225482599931607 2742949519838223899897411)
            ·
              refine ⟨4114424279757335849846117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2742949519838223899897411 4114424279757335849846117)
              ·
                refine ⟨771454552454500471846147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4114424279757335849846117 771454552454500471846147)
                ·
                  refine ⟨1157181828681750707769221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 771454552454500471846147 1157181828681750707769221)
                  ·
                    refine ⟨216971592877828257706729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1157181828681750707769221 216971592877828257706729)
                    ·
                      rfl

theorem cell22_633826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 1, 4, 1, 4].length) (baseStart_633826 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_633826 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_633826 prefixEnd_633826 := by exact prefixLift 633826
  have htrace : WordTrace (prefixWord ++ tailWord_633826) baseStart_633826 baseEnd_633826 := by
    simpa [prefixWord, tailWord_633826, baseEnd_633826] using wordTrace_append hprefix tailTrace_633826
  have hstable : (prefixWord ++ tailWord_633826).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_633826).length < 2 ^ (prefixWord ++ tailWord_633826).sum := by decide
  have hdescent : baseEnd_633826 < baseStart_633826 := by decide
  rcases family_descends (prefixWord ++ tailWord_633826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_633841 : List Nat := [1, 2, 2, 2, 4, 3, 1, 3, 4]
def baseStart_633841 : Nat := 118140960795 + 633841 * 2 ^ 59
def prefixEnd_633841 : Nat := 4983230072969 + 3 ^ 40 * 633841 * 2
def baseEnd_633841 : Nat := 72325575894791072860561

theorem tailTrace_633841 : CollatzResearch.WordTrace tailWord_633841 prefixEnd_633841 72325575894791072860561 := by
  unfold tailWord_633841
  simp only [CollatzResearch.WordTrace]
  refine ⟨23118080496709783269573377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15412053664473188846382251 23118080496709783269573377)
  ·
    refine ⟨17338560372532337452180033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23118080496709783269573377 17338560372532337452180033)
    ·
      refine ⟨13003920279399253089135025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17338560372532337452180033 13003920279399253089135025)
      ·
        refine ⟨9752940209549439816851269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13003920279399253089135025 9752940209549439816851269)
        ·
          refine ⟨1828676289290519965659613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9752940209549439816851269 1828676289290519965659613)
          ·
            refine ⟨685753608483944987122355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1828676289290519965659613 685753608483944987122355)
            ·
              refine ⟨1028630412725917480683533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 685753608483944987122355 1028630412725917480683533)
              ·
                refine ⟨385736404772219055256325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1028630412725917480683533 385736404772219055256325)
                ·
                  refine ⟨72325575894791072860561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 385736404772219055256325 72325575894791072860561)
                  ·
                    rfl

theorem cell22_633841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 3, 1, 3, 4].length) (baseStart_633841 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_633841 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_633841 prefixEnd_633841 := by exact prefixLift 633841
  have htrace : WordTrace (prefixWord ++ tailWord_633841) baseStart_633841 baseEnd_633841 := by
    simpa [prefixWord, tailWord_633841, baseEnd_633841] using wordTrace_append hprefix tailTrace_633841
  have hstable : (prefixWord ++ tailWord_633841).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_633841).length < 2 ^ (prefixWord ++ tailWord_633841).sum := by decide
  have hdescent : baseEnd_633841 < baseStart_633841 := by decide
  rcases family_descends (prefixWord ++ tailWord_633841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_633852 : List Nat := [2, 2, 2, 1, 2, 5, 8]
def baseStart_633852 : Nat := 118140960795 + 633852 * 2 ^ 59
def prefixEnd_633852 : Nat := 4983230072969 + 3 ^ 40 * 633852 * 2
def baseEnd_633852 : Nat := 8036314563302698390987

theorem tailTrace_633852 : CollatzResearch.WordTrace tailWord_633852 prefixEnd_633852 8036314563302698390987 := by
  unfold tailWord_633852
  simp only [CollatzResearch.WordTrace]
  refine ⟨11559240849834966074111905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15412321133113288098815873 11559240849834966074111905)
  ·
    refine ⟨8669430637376224555583929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11559240849834966074111905 8669430637376224555583929)
    ·
      refine ⟨6502072978032168416687947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8669430637376224555583929 6502072978032168416687947)
      ·
        refine ⟨9753109467048252625031921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6502072978032168416687947 9753109467048252625031921)
        ·
          refine ⟨7314832100286189468773941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9753109467048252625031921 7314832100286189468773941)
          ·
            refine ⟨685765509401830262697557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 7314832100286189468773941 685765509401830262697557)
            ·
              refine ⟨8036314563302698390987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 685765509401830262697557 8036314563302698390987)
              ·
                rfl

theorem cell22_633852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 5, 8].length) (baseStart_633852 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_633852 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_633852 prefixEnd_633852 := by exact prefixLift 633852
  have htrace : WordTrace (prefixWord ++ tailWord_633852) baseStart_633852 baseEnd_633852 := by
    simpa [prefixWord, tailWord_633852, baseEnd_633852] using wordTrace_append hprefix tailTrace_633852
  have hstable : (prefixWord ++ tailWord_633852).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_633852).length < 2 ^ (prefixWord ++ tailWord_633852).sum := by decide
  have hdescent : baseEnd_633852 < baseStart_633852 := by decide
  rcases family_descends (prefixWord ++ tailWord_633852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_633858 : List Nat := [3, 4, 1, 3, 1, 2, 1, 1, 6]
def baseStart_633858 : Nat := 118140960795 + 633858 * 2 ^ 59
def prefixEnd_633858 : Nat := 4983230072969 + 3 ^ 40 * 633858 * 2
def baseEnd_633858 : Nat := 72327515710596946968877

theorem tailTrace_633858 : CollatzResearch.WordTrace tailWord_633858 prefixEnd_633858 72327515710596946968877 := by
  unfold tailWord_633858
  simp only [CollatzResearch.WordTrace]
  refine ⟨5779675134412048793235557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15412467025098796781961485 5779675134412048793235557)
  ·
    refine ⟨1083689087702259148731667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5779675134412048793235557 1083689087702259148731667)
    ·
      refine ⟨1625533631553388723097501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1083689087702259148731667 1625533631553388723097501)
      ·
        refine ⟨609575111832520771161563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1625533631553388723097501 609575111832520771161563)
        ·
          refine ⟨914362667748781156742345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 609575111832520771161563 914362667748781156742345)
          ·
            refine ⟨685772000811585867556759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 914362667748781156742345 685772000811585867556759)
            ·
              refine ⟨1028658001217378801335139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 685772000811585867556759 1028658001217378801335139)
              ·
                refine ⟨1542987001826068202002709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1028658001217378801335139 1542987001826068202002709)
                ·
                  refine ⟨72327515710596946968877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1542987001826068202002709 72327515710596946968877)
                  ·
                    rfl

theorem cell22_633858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 2, 1, 1, 6].length) (baseStart_633858 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_633858 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_633858 prefixEnd_633858 := by exact prefixLift 633858
  have htrace : WordTrace (prefixWord ++ tailWord_633858) baseStart_633858 baseEnd_633858 := by
    simpa [prefixWord, tailWord_633858, baseEnd_633858] using wordTrace_append hprefix tailTrace_633858
  have hstable : (prefixWord ++ tailWord_633858).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_633858).length < 2 ^ (prefixWord ++ tailWord_633858).sum := by decide
  have hdescent : baseEnd_633858 < baseStart_633858 := by decide
  rcases family_descends (prefixWord ++ tailWord_633858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_633944 : List Nat := [2, 1, 2, 2, 1, 3, 2, 4, 1, 4]
def baseStart_633944 : Nat := 118140960795 + 633944 * 2 ^ 59
def prefixEnd_633944 : Nat := 4983230072969 + 3 ^ 40 * 633944 * 2
def baseEnd_633944 : Nat := 217011986689315283256367

theorem tailTrace_633944 : CollatzResearch.WordTrace tailWord_633944 prefixEnd_633944 217011986689315283256367 := by
  unfold tailWord_633944
  simp only [CollatzResearch.WordTrace]
  refine ⟨11560918607668315930286443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15414558143557754573715257 11560918607668315930286443)
  ·
    refine ⟨17341377911502473895429665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11560918607668315930286443 17341377911502473895429665)
    ·
      refine ⟨13006033433626855421572249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17341377911502473895429665 13006033433626855421572249)
      ·
        refine ⟨9754525075220141566179187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13006033433626855421572249 9754525075220141566179187)
        ·
          refine ⟨14631787612830212349268781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9754525075220141566179187 14631787612830212349268781)
          ·
            refine ⟨5486920354811329630975793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14631787612830212349268781 5486920354811329630975793)
            ·
              refine ⟨4115190266108497223231845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5486920354811329630975793 4115190266108497223231845)
              ·
                refine ⟨771598174895343229355971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4115190266108497223231845 771598174895343229355971)
                ·
                  refine ⟨1157397262343014844033957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 771598174895343229355971 1157397262343014844033957)
                  ·
                    refine ⟨217011986689315283256367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1157397262343014844033957 217011986689315283256367)
                    ·
                      rfl

theorem cell22_633944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 2, 4, 1, 4].length) (baseStart_633944 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_633944 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_633944 prefixEnd_633944 := by exact prefixLift 633944
  have htrace : WordTrace (prefixWord ++ tailWord_633944) baseStart_633944 baseEnd_633944 := by
    simpa [prefixWord, tailWord_633944, baseEnd_633944] using wordTrace_append hprefix tailTrace_633944
  have hstable : (prefixWord ++ tailWord_633944).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_633944).length < 2 ^ (prefixWord ++ tailWord_633944).sum := by decide
  have hdescent : baseEnd_633944 < baseStart_633944 := by decide
  rcases family_descends (prefixWord ++ tailWord_633944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_633961 : List Nat := [1, 2, 1, 1, 1, 6, 4, 1, 1, 4]
def baseStart_633961 : Nat := 118140960795 + 633961 * 2 ^ 59
def prefixEnd_633961 : Nat := 4983230072969 + 3 ^ 40 * 633961 * 2
def baseEnd_633961 : Nat := 217017806136732905581315

theorem tailTrace_633961 : CollatzResearch.WordTrace tailWord_633961 prefixEnd_633961 217017806136732905581315 := by
  unfold tailWord_633961
  simp only [CollatzResearch.WordTrace]
  refine ⟨23122457256275043763941737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15414971504183362509294491 23122457256275043763941737)
  ·
    refine ⟨17341842942206282822956303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23122457256275043763941737 17341842942206282822956303)
    ·
      refine ⟨26012764413309424234434455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17341842942206282822956303 26012764413309424234434455)
      ·
        refine ⟨39019146619964136351651683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26012764413309424234434455 39019146619964136351651683)
        ·
          refine ⟨58528719929946204527477525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39019146619964136351651683 58528719929946204527477525)
          ·
            refine ⟨2743533746716228337225509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 58528719929946204527477525 2743533746716228337225509)
            ·
              refine ⟨514412577509292813229783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2743533746716228337225509 514412577509292813229783)
              ·
                refine ⟨771618866263939219844675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 514412577509292813229783 771618866263939219844675)
                ·
                  refine ⟨1157428299395908829767013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 771618866263939219844675 1157428299395908829767013)
                  ·
                    refine ⟨217017806136732905581315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1157428299395908829767013 217017806136732905581315)
                    ·
                      rfl

theorem cell22_633961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 4, 1, 1, 4].length) (baseStart_633961 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_633961 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_633961 prefixEnd_633961 := by exact prefixLift 633961
  have htrace : WordTrace (prefixWord ++ tailWord_633961) baseStart_633961 baseEnd_633961 := by
    simpa [prefixWord, tailWord_633961, baseEnd_633961] using wordTrace_append hprefix tailTrace_633961
  have hstable : (prefixWord ++ tailWord_633961).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_633961).length < 2 ^ (prefixWord ++ tailWord_633961).sum := by decide
  have hdescent : baseEnd_633961 < baseStart_633961 := by decide
  rcases family_descends (prefixWord ++ tailWord_633961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_633982 : List Nat := [4, 2, 4, 1, 1, 1, 3, 1, 5]
def baseStart_633982 : Nat := 118140960795 + 633982 * 2 ^ 59
def prefixEnd_633982 : Nat := 4983230072969 + 3 ^ 40 * 633982 * 2
def baseEnd_633982 : Nat := 72341664955298616935417

theorem tailTrace_633982 : CollatzResearch.WordTrace tailWord_633982 prefixEnd_633982 72341664955298616935417 := by
  unfold tailWord_633982
  simp only [CollatzResearch.WordTrace]
  refine ⟨2890402898649870543807025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15415482126132642900304133 2890402898649870543807025)
  ·
    refine ⟨2167802173987402907855269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2890402898649870543807025 2167802173987402907855269)
    ·
      refine ⟨406462907622638045222863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2167802173987402907855269 406462907622638045222863)
      ·
        refine ⟨609694361433957067834295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 406462907622638045222863 609694361433957067834295)
        ·
          refine ⟨914541542150935601751443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 609694361433957067834295 914541542150935601751443)
          ·
            refine ⟨1371812313226403402627165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 914541542150935601751443 1371812313226403402627165)
            ·
              refine ⟨514429617459901275985187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1371812313226403402627165 514429617459901275985187)
              ·
                refine ⟨771644426189851913977781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 514429617459901275985187 771644426189851913977781)
                ·
                  refine ⟨72341664955298616935417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 771644426189851913977781 72341664955298616935417)
                  ·
                    rfl

theorem cell22_633982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 3, 1, 5].length) (baseStart_633982 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_633982 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_633982 prefixEnd_633982 := by exact prefixLift 633982
  have htrace : WordTrace (prefixWord ++ tailWord_633982) baseStart_633982 baseEnd_633982 := by
    simpa [prefixWord, tailWord_633982, baseEnd_633982] using wordTrace_append hprefix tailTrace_633982
  have hstable : (prefixWord ++ tailWord_633982).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_633982).length < 2 ^ (prefixWord ++ tailWord_633982).sum := by decide
  have hdescent : baseEnd_633982 < baseStart_633982 := by decide
  rcases family_descends (prefixWord ++ tailWord_633982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_633987 : List Nat := [1, 1, 1, 3, 3, 2, 2, 9]
def baseStart_633987 : Nat := 118140960795 + 633987 * 2 ^ 59
def prefixEnd_633987 : Nat := 4983230072969 + 3 ^ 40 * 633987 * 2
def baseEnd_633987 : Nat := 24114078496453056047915

theorem tailTrace_633987 : CollatzResearch.WordTrace tailWord_633987 prefixEnd_633987 24114078496453056047915 := by
  unfold tailWord_633987
  simp only [CollatzResearch.WordTrace]
  refine ⟨23123405554180850204388215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15415603702787233469592143 23123405554180850204388215)
  ·
    refine ⟨34685108331271275306582323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23123405554180850204388215 34685108331271275306582323)
    ·
      refine ⟨52027662496906912959873485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34685108331271275306582323 52027662496906912959873485)
      ·
        refine ⟨19510373436340092359952557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52027662496906912959873485 19510373436340092359952557)
        ·
          refine ⟨7316390038627534634982209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19510373436340092359952557 7316390038627534634982209)
          ·
            refine ⟨5487292528970650976236657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7316390038627534634982209 5487292528970650976236657)
            ·
              refine ⟨4115469396727988232177493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5487292528970650976236657 4115469396727988232177493)
              ·
                refine ⟨24114078496453056047915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 4115469396727988232177493 24114078496453056047915)
                ·
                  rfl

theorem cell22_633987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 2, 9].length) (baseStart_633987 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_633987 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_633987 prefixEnd_633987 := by exact prefixLift 633987
  have htrace : WordTrace (prefixWord ++ tailWord_633987) baseStart_633987 baseEnd_633987 := by
    simpa [prefixWord, tailWord_633987, baseEnd_633987] using wordTrace_append hprefix tailTrace_633987
  have hstable : (prefixWord ++ tailWord_633987).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_633987).length < 2 ^ (prefixWord ++ tailWord_633987).sum := by decide
  have hdescent : baseEnd_633987 < baseStart_633987 := by decide
  rcases family_descends (prefixWord ++ tailWord_633987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_634019 : List Nat := [1, 1, 1, 4, 1, 1, 1, 4, 5, 3]
def baseStart_634019 : Nat := 118140960795 + 634019 * 2 ^ 59
def prefixEnd_634019 : Nat := 4983230072969 + 3 ^ 40 * 634019 * 2
def baseEnd_634019 : Nat := 217037660722040087631137

theorem tailTrace_634019 : CollatzResearch.WordTrace tailWord_634019 prefixEnd_634019 217037660722040087631137 := by
  unfold tailWord_634019
  simp only [CollatzResearch.WordTrace]
  refine ⟨23124572690064919669553111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15416381793376613113035407 23124572690064919669553111)
  ·
    refine ⟨34686859035097379504329667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23124572690064919669553111 34686859035097379504329667)
    ·
      refine ⟨52030288552646069256494501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34686859035097379504329667 52030288552646069256494501)
      ·
        refine ⟨9755679103621137985592719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 52030288552646069256494501 9755679103621137985592719)
        ·
          refine ⟨14633518655431706978389079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9755679103621137985592719 14633518655431706978389079)
          ·
            refine ⟨21950277983147560467583619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14633518655431706978389079 21950277983147560467583619)
            ·
              refine ⟨32925416974721340701375429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21950277983147560467583619 32925416974721340701375429)
              ·
                refine ⟨6173515682760251381507893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32925416974721340701375429 6173515682760251381507893)
                ·
                  refine ⟨578767095258773567016365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 6173515682760251381507893 578767095258773567016365)
                  ·
                    refine ⟨217037660722040087631137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 578767095258773567016365 217037660722040087631137)
                    ·
                      rfl

theorem cell22_634019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 4, 5, 3].length) (baseStart_634019 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_634019 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_634019 prefixEnd_634019 := by exact prefixLift 634019
  have htrace : WordTrace (prefixWord ++ tailWord_634019) baseStart_634019 baseEnd_634019 := by
    simpa [prefixWord, tailWord_634019, baseEnd_634019] using wordTrace_append hprefix tailTrace_634019
  have hstable : (prefixWord ++ tailWord_634019).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_634019).length < 2 ^ (prefixWord ++ tailWord_634019).sum := by decide
  have hdescent : baseEnd_634019 < baseStart_634019 := by decide
  rcases family_descends (prefixWord ++ tailWord_634019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_634126 : List Nat := [4, 1, 1, 2, 1, 3, 2, 2, 1, 5]
def baseStart_634126 : Nat := 118140960795 + 634126 * 2 ^ 59
def prefixEnd_634126 : Nat := 4983230072969 + 3 ^ 40 * 634126 * 2
def baseEnd_634126 : Nat := 217074289008727475205809

theorem tailTrace_634126 : CollatzResearch.WordTrace tailWord_634126 prefixEnd_634126 217074289008727475205809 := by
  unfold tailWord_634126
  simp only [CollatzResearch.WordTrace]
  refine ⟨2891059412584659617962279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15418983533784851295798821 2891059412584659617962279)
  ·
    refine ⟨4336589118876989426943419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2891059412584659617962279 4336589118876989426943419)
    ·
      refine ⟨6504883678315484140415129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4336589118876989426943419 6504883678315484140415129)
      ·
        refine ⟨4878662758736613105311347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6504883678315484140415129 4878662758736613105311347)
        ·
          refine ⟨7317994138104919657967021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4878662758736613105311347 7317994138104919657967021)
          ·
            refine ⟨2744247801789344871737633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7317994138104919657967021 2744247801789344871737633)
            ·
              refine ⟨2058185851342008653803225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2744247801789344871737633 2058185851342008653803225)
              ·
                refine ⟨1543639388506506490352419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2058185851342008653803225 1543639388506506490352419)
                ·
                  refine ⟨2315459082759759735528629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1543639388506506490352419 2315459082759759735528629)
                  ·
                    refine ⟨217074289008727475205809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2315459082759759735528629 217074289008727475205809)
                    ·
                      rfl

theorem cell22_634126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 2, 2, 1, 5].length) (baseStart_634126 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_634126 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_634126 prefixEnd_634126 := by exact prefixLift 634126
  have htrace : WordTrace (prefixWord ++ tailWord_634126) baseStart_634126 baseEnd_634126 := by
    simpa [prefixWord, tailWord_634126, baseEnd_634126] using wordTrace_append hprefix tailTrace_634126
  have hstable : (prefixWord ++ tailWord_634126).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_634126).length < 2 ^ (prefixWord ++ tailWord_634126).sum := by decide
  have hdescent : baseEnd_634126 < baseStart_634126 := by decide
  rcases family_descends (prefixWord ++ tailWord_634126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_634143 : List Nat := [1, 1, 2, 4, 4, 1, 1, 1, 4, 3]
def baseStart_634143 : Nat := 118140960795 + 634143 * 2 ^ 59
def prefixEnd_634143 : Nat := 4983230072969 + 3 ^ 40 * 634143 * 2
def baseEnd_634143 : Nat := 217080108456145097530757

theorem tailTrace_634143 : CollatzResearch.WordTrace tailWord_634143 prefixEnd_634143 217080108456145097530757 := by
  unfold tailWord_634143
  simp only [CollatzResearch.WordTrace]
  refine ⟨23129095341615688847067083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15419396894410459231378055 23129095341615688847067083)
  ·
    refine ⟨34693643012423533270600625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23129095341615688847067083 34693643012423533270600625)
    ·
      refine ⟨26020232259317649952950469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34693643012423533270600625 26020232259317649952950469)
      ·
        refine ⟨4878793548622059366178213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26020232259317649952950469 4878793548622059366178213)
        ·
          refine ⟨914773790366636131158415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4878793548622059366178213 914773790366636131158415)
          ·
            refine ⟨1372160685549954196737623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 914773790366636131158415 1372160685549954196737623)
            ·
              refine ⟨2058241028324931295106435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1372160685549954196737623 2058241028324931295106435)
              ·
                refine ⟨3087361542487396942659653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2058241028324931295106435 3087361542487396942659653)
                ·
                  refine ⟨578880289216386926748685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3087361542487396942659653 578880289216386926748685)
                  ·
                    refine ⟨217080108456145097530757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 578880289216386926748685 217080108456145097530757)
                    ·
                      rfl

theorem cell22_634143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 1, 1, 4, 3].length) (baseStart_634143 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_634143 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_634143 prefixEnd_634143 := by exact prefixLift 634143
  have htrace : WordTrace (prefixWord ++ tailWord_634143) baseStart_634143 baseEnd_634143 := by
    simpa [prefixWord, tailWord_634143, baseEnd_634143] using wordTrace_append hprefix tailTrace_634143
  have hstable : (prefixWord ++ tailWord_634143).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_634143).length < 2 ^ (prefixWord ++ tailWord_634143).sum := by decide
  have hdescent : baseEnd_634143 < baseStart_634143 := by decide
  rcases family_descends (prefixWord ++ tailWord_634143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_634173 : List Nat := [1, 4, 1, 5, 1, 1, 1, 8]
def baseStart_634173 : Nat := 118140960795 + 634173 * 2 ^ 59
def prefixEnd_634173 : Nat := 4983230072969 + 3 ^ 40 * 634173 * 2
def baseEnd_634173 : Nat := 24121153118803891031185

theorem tailTrace_634173 : CollatzResearch.WordTrace tailWord_634173 prefixEnd_634173 24121153118803891031185 := by
  unfold tailWord_634173
  simp only [CollatzResearch.WordTrace]
  refine ⟨23130189531507003970659173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15420126354338002647106115 23130189531507003970659173)
  ·
    refine ⟨4336910537157563244498595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23130189531507003970659173 4336910537157563244498595)
    ·
      refine ⟨6505365805736344866747893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4336910537157563244498595 6505365805736344866747893)
      ·
        refine ⟨609878044287782331257615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 6505365805736344866747893 609878044287782331257615)
        ·
          refine ⟨914817066431673496886423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 609878044287782331257615 914817066431673496886423)
          ·
            refine ⟨1372225599647510245329635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 914817066431673496886423 1372225599647510245329635)
            ·
              refine ⟨2058338399471265367994453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1372225599647510245329635 2058338399471265367994453)
              ·
                refine ⟨24121153118803891031185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2058338399471265367994453 24121153118803891031185)
                ·
                  rfl

theorem cell22_634173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 1, 8].length) (baseStart_634173 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_634173 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_634173 prefixEnd_634173 := by exact prefixLift 634173
  have htrace : WordTrace (prefixWord ++ tailWord_634173) baseStart_634173 baseEnd_634173 := by
    simpa [prefixWord, tailWord_634173, baseEnd_634173] using wordTrace_append hprefix tailTrace_634173
  have hstable : (prefixWord ++ tailWord_634173).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_634173).length < 2 ^ (prefixWord ++ tailWord_634173).sum := by decide
  have hdescent : baseEnd_634173 < baseStart_634173 := by decide
  rcases family_descends (prefixWord ++ tailWord_634173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_634231 : List Nat := [1, 1, 3, 1, 1, 2, 5, 1, 3, 4]
def baseStart_634231 : Nat := 118140960795 + 634231 * 2 ^ 59
def prefixEnd_634231 : Nat := 4983230072969 + 3 ^ 40 * 634231 * 2
def baseEnd_634231 : Nat := 217110232654542201330487

theorem tailTrace_634231 : CollatzResearch.WordTrace tailWord_634231 prefixEnd_634231 217110232654542201330487 := by
  unfold tailWord_634231
  simp only [CollatzResearch.WordTrace]
  refine ⟨23132304965296879876270547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15421536643531253250847031 23132304965296879876270547)
  ·
    refine ⟨34698457447945319814405821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23132304965296879876270547 34698457447945319814405821)
    ·
      refine ⟨13011921542979494930402183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34698457447945319814405821 13011921542979494930402183)
      ·
        refine ⟨19517882314469242395603275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13011921542979494930402183 19517882314469242395603275)
        ·
          refine ⟨29276823471703863593404913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19517882314469242395603275 29276823471703863593404913)
          ·
            refine ⟨21957617603777897695053685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29276823471703863593404913 21957617603777897695053685)
            ·
              refine ⟨2058526650354177908911283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 21957617603777897695053685 2058526650354177908911283)
              ·
                refine ⟨3087789975531266863366925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2058526650354177908911283 3087789975531266863366925)
                ·
                  refine ⟨1157921240824225073762597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3087789975531266863366925 1157921240824225073762597)
                  ·
                    refine ⟨217110232654542201330487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1157921240824225073762597 217110232654542201330487)
                    ·
                      rfl

theorem cell22_634231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 5, 1, 3, 4].length) (baseStart_634231 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_634231 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_634231 prefixEnd_634231 := by exact prefixLift 634231
  have htrace : WordTrace (prefixWord ++ tailWord_634231) baseStart_634231 baseEnd_634231 := by
    simpa [prefixWord, tailWord_634231, baseEnd_634231] using wordTrace_append hprefix tailTrace_634231
  have hstable : (prefixWord ++ tailWord_634231).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_634231).length < 2 ^ (prefixWord ++ tailWord_634231).sum := by decide
  have hdescent : baseEnd_634231 < baseStart_634231 := by decide
  rcases family_descends (prefixWord ++ tailWord_634231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_634276 : List Nat := [2, 3, 1, 2, 1, 1, 1, 4, 1, 6]
def baseStart_634276 : Nat := 118140960795 + 634276 * 2 ^ 59
def prefixEnd_634276 : Nat := 4983230072969 + 3 ^ 40 * 634276 * 2
def baseEnd_634276 : Nat := 217125637074177083955349

theorem tailTrace_634276 : CollatzResearch.WordTrace tailWord_634276 prefixEnd_634276 217125637074177083955349 := by
  unfold tailWord_634276
  simp only [CollatzResearch.WordTrace]
  refine ⟨11566973125066926280829341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15422630833422568374439121 11566973125066926280829341)
  ·
    refine ⟨4337614921900097355311003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11566973125066926280829341 4337614921900097355311003)
    ·
      refine ⟨6506422382850146032966505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4337614921900097355311003 6506422382850146032966505)
      ·
        refine ⟨4879816787137609524724879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6506422382850146032966505 4879816787137609524724879)
        ·
          refine ⟨7319725180706414287087319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4879816787137609524724879 7319725180706414287087319)
          ·
            refine ⟨10979587771059621430630979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7319725180706414287087319 10979587771059621430630979)
            ·
              refine ⟨16469381656589432145946469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10979587771059621430630979 16469381656589432145946469)
              ·
                refine ⟨3088009060610518527364963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16469381656589432145946469 3088009060610518527364963)
                ·
                  refine ⟨4632013590915777791047445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3088009060610518527364963 4632013590915777791047445)
                  ·
                    refine ⟨217125637074177083955349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4632013590915777791047445 217125637074177083955349)
                    ·
                      rfl

theorem cell22_634276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 4, 1, 6].length) (baseStart_634276 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_634276 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_634276 prefixEnd_634276 := by exact prefixLift 634276
  have htrace : WordTrace (prefixWord ++ tailWord_634276) baseStart_634276 baseEnd_634276 := by
    simpa [prefixWord, tailWord_634276, baseEnd_634276] using wordTrace_append hprefix tailTrace_634276
  have hstable : (prefixWord ++ tailWord_634276).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_634276).length < 2 ^ (prefixWord ++ tailWord_634276).sum := by decide
  have hdescent : baseEnd_634276 < baseStart_634276 := by decide
  rcases family_descends (prefixWord ++ tailWord_634276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_634280 : List Nat := [2, 1, 6, 1, 2, 1, 1, 2, 6]
def baseStart_634280 : Nat := 118140960795 + 634280 * 2 ^ 59
def prefixEnd_634280 : Nat := 4983230072969 + 3 ^ 40 * 634280 * 2
def baseEnd_634280 : Nat := 72375668785307468951779

theorem tailTrace_634280 : CollatzResearch.WordTrace tailWord_634280 prefixEnd_634280 72375668785307468951779 := by
  unfold tailWord_634280
  simp only [CollatzResearch.WordTrace]
  refine ⟨11567046071059680622402147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15422728094746240829869529 11567046071059680622402147)
  ·
    refine ⟨17350569106589520933603221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11567046071059680622402147 17350569106589520933603221)
    ·
      refine ⟨813307926871383793762651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 17350569106589520933603221 813307926871383793762651)
      ·
        refine ⟨1219961890307075690643977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 813307926871383793762651 1219961890307075690643977)
        ·
          refine ⟨914971417730306767982983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1219961890307075690643977 914971417730306767982983)
          ·
            refine ⟨1372457126595460151974475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 914971417730306767982983 1372457126595460151974475)
            ·
              refine ⟨2058685689893190227961713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1372457126595460151974475 2058685689893190227961713)
              ·
                refine ⟨1544014267419892670971285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2058685689893190227961713 1544014267419892670971285)
                ·
                  refine ⟨72375668785307468951779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1544014267419892670971285 72375668785307468951779)
                  ·
                    rfl

theorem cell22_634280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 1, 2, 6].length) (baseStart_634280 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_634280 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_634280 prefixEnd_634280 := by exact prefixLift 634280
  have htrace : WordTrace (prefixWord ++ tailWord_634280) baseStart_634280 baseEnd_634280 := by
    simpa [prefixWord, tailWord_634280, baseEnd_634280] using wordTrace_append hprefix tailTrace_634280
  have hstable : (prefixWord ++ tailWord_634280).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_634280).length < 2 ^ (prefixWord ++ tailWord_634280).sum := by decide
  have hdescent : baseEnd_634280 < baseStart_634280 := by decide
  rcases family_descends (prefixWord ++ tailWord_634280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_634293 : List Nat := [1, 3, 3, 2, 2, 2, 1, 1, 1, 6]
def baseStart_634293 : Nat := 118140960795 + 634293 * 2 ^ 59
def prefixEnd_634293 : Nat := 4983230072969 + 3 ^ 40 * 634293 * 2
def baseEnd_634293 : Nat := 217131456521594706280297

theorem tailTrace_634293 : CollatzResearch.WordTrace tailWord_634293 prefixEnd_634293 217131456521594706280297 := by
  unfold tailWord_634293
  simp only [CollatzResearch.WordTrace]
  refine ⟨23134566291072264465027533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15423044194048176310018355 23134566291072264465027533)
  ·
    refine ⟨8675462359152099174385325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23134566291072264465027533 8675462359152099174385325)
    ·
      refine ⟨3253298384682037190394497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8675462359152099174385325 3253298384682037190394497)
      ·
        refine ⟨2439973788511527892795873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3253298384682037190394497 2439973788511527892795873)
        ·
          refine ⟨1829980341383645919596905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2439973788511527892795873 1829980341383645919596905)
          ·
            refine ⟨1372485256037734439697679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1829980341383645919596905 1372485256037734439697679)
            ·
              refine ⟨2058727884056601659546519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1372485256037734439697679 2058727884056601659546519)
              ·
                refine ⟨3088091826084902489319779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2058727884056601659546519 3088091826084902489319779)
                ·
                  refine ⟨4632137739127353733979669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3088091826084902489319779 4632137739127353733979669)
                  ·
                    refine ⟨217131456521594706280297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4632137739127353733979669 217131456521594706280297)
                    ·
                      rfl

theorem cell22_634293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 1, 1, 1, 6].length) (baseStart_634293 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_634293 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_634293 prefixEnd_634293 := by exact prefixLift 634293
  have htrace : WordTrace (prefixWord ++ tailWord_634293) baseStart_634293 baseEnd_634293 := by
    simpa [prefixWord, tailWord_634293, baseEnd_634293] using wordTrace_append hprefix tailTrace_634293
  have hstable : (prefixWord ++ tailWord_634293).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_634293).length < 2 ^ (prefixWord ++ tailWord_634293).sum := by decide
  have hdescent : baseEnd_634293 < baseStart_634293 := by decide
  rcases family_descends (prefixWord ++ tailWord_634293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_634308 : List Nat := [2, 3, 3, 2, 1, 2, 9]
def baseStart_634308 : Nat := 118140960795 + 634308 * 2 ^ 59
def prefixEnd_634308 : Nat := 4983230072969 + 3 ^ 40 * 634308 * 2
def baseEnd_634308 : Nat := 8042095975116283968713

theorem tailTrace_634308 : CollatzResearch.WordTrace tailWord_634308 prefixEnd_634308 8042095975116283968713 := by
  unfold tailWord_634308
  simp only [CollatzResearch.WordTrace]
  refine ⟨11567556693008961013411789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15423408924011948017882385 11567556693008961013411789)
  ·
    refine ⟨4337833759878360380029421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11567556693008961013411789 4337833759878360380029421)
    ·
      refine ⟨1626687659954385142511033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4337833759878360380029421 1626687659954385142511033)
      ·
        refine ⟨1220015744965788856883275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1626687659954385142511033 1220015744965788856883275)
        ·
          refine ⟨1830023617448683285324913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1220015744965788856883275 1830023617448683285324913)
          ·
            refine ⟨1372517713086512463993685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1830023617448683285324913 1372517713086512463993685)
            ·
              refine ⟨8042095975116283968713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1372517713086512463993685 8042095975116283968713)
              ·
                rfl

theorem cell22_634308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 9].length) (baseStart_634308 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_634308 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_634308 prefixEnd_634308 := by exact prefixLift 634308
  have htrace : WordTrace (prefixWord ++ tailWord_634308) baseStart_634308 baseEnd_634308 := by
    simpa [prefixWord, tailWord_634308, baseEnd_634308] using wordTrace_append hprefix tailTrace_634308
  have hstable : (prefixWord ++ tailWord_634308).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_634308).length < 2 ^ (prefixWord ++ tailWord_634308).sum := by decide
  have hdescent : baseEnd_634308 < baseStart_634308 := by decide
  rcases family_descends (prefixWord ++ tailWord_634308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_634351 : List Nat := [1, 1, 2, 1, 4, 1, 2, 2, 1, 7]
def baseStart_634351 : Nat := 118140960795 + 634351 * 2 ^ 59
def prefixEnd_634351 : Nat := 4983230072969 + 3 ^ 40 * 634351 * 2
def baseEnd_634351 : Nat := 217151311106901888330119

theorem tailTrace_634351 : CollatzResearch.WordTrace tailWord_634351 prefixEnd_634351 217151311106901888330119 := by
  unfold tailWord_634351
  simp only [CollatzResearch.WordTrace]
  refine ⟨23136681724862140370638907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15424454483241426913759271 23136681724862140370638907)
  ·
    refine ⟨34705022587293210555958361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23136681724862140370638907 34705022587293210555958361)
    ·
      refine ⟨26028766940469907916968771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34705022587293210555958361 26028766940469907916968771)
      ·
        refine ⟨39043150410704861875453157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26028766940469907916968771 39043150410704861875453157)
        ·
          refine ⟨7320590702007161601647467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39043150410704861875453157 7320590702007161601647467)
          ·
            refine ⟨10980886053010742402471201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7320590702007161601647467 10980886053010742402471201)
            ·
              refine ⟨8235664539758056801853401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10980886053010742402471201 8235664539758056801853401)
              ·
                refine ⟨6176748404818542601390051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8235664539758056801853401 6176748404818542601390051)
                ·
                  refine ⟨9265122607227813902085077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6176748404818542601390051 9265122607227813902085077)
                  ·
                    refine ⟨217151311106901888330119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 9265122607227813902085077 217151311106901888330119)
                    ·
                      rfl

theorem cell22_634351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 2, 1, 7].length) (baseStart_634351 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_634351 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_634351 prefixEnd_634351 := by exact prefixLift 634351
  have htrace : WordTrace (prefixWord ++ tailWord_634351) baseStart_634351 baseEnd_634351 := by
    simpa [prefixWord, tailWord_634351, baseEnd_634351] using wordTrace_append hprefix tailTrace_634351
  have hstable : (prefixWord ++ tailWord_634351).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_634351).length < 2 ^ (prefixWord ++ tailWord_634351).sum := by decide
  have hdescent : baseEnd_634351 < baseStart_634351 := by decide
  rcases family_descends (prefixWord ++ tailWord_634351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_634370 : List Nat := [3, 4, 1, 2, 1, 1, 2, 1, 7]
def baseStart_634370 : Nat := 118140960795 + 634370 * 2 ^ 59
def prefixEnd_634370 : Nat := 4983230072969 + 3 ^ 40 * 634370 * 2
def baseEnd_634370 : Nat := 72385938398397390701687

theorem tailTrace_634370 : CollatzResearch.WordTrace tailWord_634370 prefixEnd_634370 72385938398397390701687 := by
  unfold tailWord_634370
  simp only [CollatzResearch.WordTrace]
  refine ⟨5784343677948326653895141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15424916474528871077053709 5784343677948326653895141)
  ·
    refine ⟨1084564439615311247605339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5784343677948326653895141 1084564439615311247605339)
    ·
      refine ⟨1626846659422966871408009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1084564439615311247605339 1626846659422966871408009)
      ·
        refine ⟨1220134994567225153556007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1626846659422966871408009 1220134994567225153556007)
        ·
          refine ⟨1830202491850837730334011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1220134994567225153556007 1830202491850837730334011)
          ·
            refine ⟨2745303737776256595501017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1830202491850837730334011 2745303737776256595501017)
            ·
              refine ⟨2058977803332192446625763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2745303737776256595501017 2058977803332192446625763)
              ·
                refine ⟨3088466704998288669938645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2058977803332192446625763 3088466704998288669938645)
                ·
                  refine ⟨72385938398397390701687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3088466704998288669938645 72385938398397390701687)
                  ·
                    rfl

theorem cell22_634370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 2, 1, 7].length) (baseStart_634370 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_634370 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_634370 prefixEnd_634370 := by exact prefixLift 634370
  have htrace : WordTrace (prefixWord ++ tailWord_634370) baseStart_634370 baseEnd_634370 := by
    simpa [prefixWord, tailWord_634370, baseEnd_634370] using wordTrace_append hprefix tailTrace_634370
  have hstable : (prefixWord ++ tailWord_634370).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_634370).length < 2 ^ (prefixWord ++ tailWord_634370).sum := by decide
  have hdescent : baseEnd_634370 < baseStart_634370 := by decide
  rcases family_descends (prefixWord ++ tailWord_634370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_634400 : List Nat := [2, 1, 1, 6, 1, 2, 1, 1, 3, 4]
def baseStart_634400 : Nat := 118140960795 + 634400 * 2 ^ 59
def prefixEnd_634400 : Nat := 4983230072969 + 3 ^ 40 * 634400 * 2
def baseEnd_634400 : Nat := 217168084808282093854969

theorem tailTrace_634400 : CollatzResearch.WordTrace tailWord_634400 prefixEnd_634400 217168084808282093854969 := by
  unfold tailWord_634400
  simp only [CollatzResearch.WordTrace]
  refine ⟨11569234450842310869586327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15425645934456414492781769 11569234450842310869586327)
  ·
    refine ⟨17353851676263466304379491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11569234450842310869586327 17353851676263466304379491)
    ·
      refine ⟨26030777514395199456569237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17353851676263466304379491 26030777514395199456569237)
      ·
        refine ⟨1220192695987274974526683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 26030777514395199456569237 1220192695987274974526683)
        ·
          refine ⟨1830289043980912461790025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1220192695987274974526683 1830289043980912461790025)
          ·
            refine ⟨1372716782985684346342519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1830289043980912461790025 1372716782985684346342519)
            ·
              refine ⟨2059075174478526519513779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1372716782985684346342519 2059075174478526519513779)
              ·
                refine ⟨3088612761717789779270669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2059075174478526519513779 3088612761717789779270669)
                ·
                  refine ⟨1158229785644171167226501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3088612761717789779270669 1158229785644171167226501)
                  ·
                    refine ⟨217168084808282093854969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1158229785644171167226501 217168084808282093854969)
                    ·
                      rfl

theorem cell22_634400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 1, 1, 3, 4].length) (baseStart_634400 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_634400 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_634400 prefixEnd_634400 := by exact prefixLift 634400
  have htrace : WordTrace (prefixWord ++ tailWord_634400) baseStart_634400 baseEnd_634400 := by
    simpa [prefixWord, tailWord_634400, baseEnd_634400] using wordTrace_append hprefix tailTrace_634400
  have hstable : (prefixWord ++ tailWord_634400).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_634400).length < 2 ^ (prefixWord ++ tailWord_634400).sum := by decide
  have hdescent : baseEnd_634400 < baseStart_634400 := by decide
  rcases family_descends (prefixWord ++ tailWord_634400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_634526 : List Nat := [4, 3, 1, 1, 1, 2, 3, 3, 1, 3]
def baseStart_634526 : Nat := 118140960795 + 634526 * 2 ^ 59
def prefixEnd_634526 : Nat := 4983230072969 + 3 ^ 40 * 634526 * 2
def baseEnd_634526 : Nat := 217211217183259765204583

theorem tailTrace_634526 : CollatzResearch.WordTrace tailWord_634526 prefixEnd_634526 217211217183259765204583 := by
  unfold tailWord_634526
  simp only [CollatzResearch.WordTrace]
  refine ⟨2892883062403518157282429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15428709666152096838839621 2892883062403518157282429)
  ·
    refine ⟨1084831148401319308980911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2892883062403518157282429 1084831148401319308980911)
    ·
      refine ⟨1627246722601978963471367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1084831148401319308980911 1627246722601978963471367)
      ·
        refine ⟨2440870083902968445207051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1627246722601978963471367 2440870083902968445207051)
        ·
          refine ⟨3661305125854452667810577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2440870083902968445207051 3661305125854452667810577)
          ·
            refine ⟨2745978844390839500857933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3661305125854452667810577 2745978844390839500857933)
            ·
              refine ⟨1029742066646564812821725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2745978844390839500857933 1029742066646564812821725)
              ·
                refine ⟨386153274992461804808147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1029742066646564812821725 386153274992461804808147)
                ·
                  refine ⟨579229912488692707212221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 386153274992461804808147 579229912488692707212221)
                  ·
                    refine ⟨217211217183259765204583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 579229912488692707212221 217211217183259765204583)
                    ·
                      rfl

theorem cell22_634526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 3, 3, 1, 3].length) (baseStart_634526 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_634526 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_634526 prefixEnd_634526 := by exact prefixLift 634526
  have htrace : WordTrace (prefixWord ++ tailWord_634526) baseStart_634526 baseEnd_634526 := by
    simpa [prefixWord, tailWord_634526, baseEnd_634526] using wordTrace_append hprefix tailTrace_634526
  have hstable : (prefixWord ++ tailWord_634526).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_634526).length < 2 ^ (prefixWord ++ tailWord_634526).sum := by decide
  have hdescent : baseEnd_634526 < baseStart_634526 := by decide
  rcases family_descends (prefixWord ++ tailWord_634526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_634533 : List Nat := [1, 3, 1, 2, 1, 2, 2, 2, 8]
def baseStart_634533 : Nat := 118140960795 + 634533 * 2 ^ 59
def prefixEnd_634533 : Nat := 4983230072969 + 3 ^ 40 * 634533 * 2
def baseEnd_634533 : Nat := 72404537808771360093187

theorem tailTrace_634533 : CollatzResearch.WordTrace tailWord_634533 prefixEnd_634533 72404537808771360093187 := by
  unfold tailWord_634533
  simp only [CollatzResearch.WordTrace]
  refine ⟨23143319810202785453764253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15428879873468523635842835 23143319810202785453764253)
  ·
    refine ⟨8678744928826044545161595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23143319810202785453764253 8678744928826044545161595)
    ·
      refine ⟨13018117393239066817742393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8678744928826044545161595 13018117393239066817742393)
      ·
        refine ⟨9763588044929300113306795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13018117393239066817742393 9763588044929300113306795)
        ·
          refine ⟨14645382067393950169960193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9763588044929300113306795 14645382067393950169960193)
          ·
            refine ⟨10984036550545462627470145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14645382067393950169960193 10984036550545462627470145)
            ·
              refine ⟨8238027412909096970602609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10984036550545462627470145 8238027412909096970602609)
              ·
                refine ⟨6178520559681822727951957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8238027412909096970602609 6178520559681822727951957)
                ·
                  refine ⟨72404537808771360093187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 6178520559681822727951957 72404537808771360093187)
                  ·
                    rfl

theorem cell22_634533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 2, 8].length) (baseStart_634533 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_634533 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_634533 prefixEnd_634533 := by exact prefixLift 634533
  have htrace : WordTrace (prefixWord ++ tailWord_634533) baseStart_634533 baseEnd_634533 := by
    simpa [prefixWord, tailWord_634533, baseEnd_634533] using wordTrace_append hprefix tailTrace_634533
  have hstable : (prefixWord ++ tailWord_634533).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_634533).length < 2 ^ (prefixWord ++ tailWord_634533).sum := by decide
  have hdescent : baseEnd_634533 < baseStart_634533 := by decide
  rcases family_descends (prefixWord ++ tailWord_634533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_634595 : List Nat := [1, 1, 1, 7, 2, 10]
def baseStart_634595 : Nat := 118140960795 + 634595 * 2 ^ 59
def prefixEnd_634595 : Nat := 4983230072969 + 3 ^ 40 * 634595 * 2
def baseEnd_634595 : Nat := 2681911571523044262091

theorem tailTrace_634595 : CollatzResearch.WordTrace tailWord_634595 prefixEnd_634595 2681911571523044262091 := by
  unfold tailWord_634595
  simp only [CollatzResearch.WordTrace]
  refine ⟨23145581135978170042521239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15430387423985446695014159 23145581135978170042521239)
  ·
    refine ⟨34718371703967255063781859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23145581135978170042521239 34718371703967255063781859)
    ·
      refine ⟨52077557555950882595672789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34718371703967255063781859 52077557555950882595672789)
      ·
        refine ⟨1220567755217598810836081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 52077557555950882595672789 1220567755217598810836081)
        ·
          refine ⟨915425816413199108127061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1220567755217598810836081 915425816413199108127061)
          ·
            refine ⟨2681911571523044262091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 915425816413199108127061 2681911571523044262091)
            ·
              rfl

theorem cell22_634595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 10].length) (baseStart_634595 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_634595 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_634595 prefixEnd_634595 := by exact prefixLift 634595
  have htrace : WordTrace (prefixWord ++ tailWord_634595) baseStart_634595 baseEnd_634595 := by
    simpa [prefixWord, tailWord_634595, baseEnd_634595] using wordTrace_append hprefix tailTrace_634595
  have hstable : (prefixWord ++ tailWord_634595).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_634595).length < 2 ^ (prefixWord ++ tailWord_634595).sum := by decide
  have hdescent : baseEnd_634595 < baseStart_634595 := by decide
  rcases family_descends (prefixWord ++ tailWord_634595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_634631 : List Nat := [1, 1, 4, 4, 3, 1, 1, 1, 2, 4]
def baseStart_634631 : Nat := 118140960795 + 634631 * 2 ^ 59
def prefixEnd_634631 : Nat := 4983230072969 + 3 ^ 40 * 634631 * 2
def baseEnd_634631 : Nat := 217247160829074491329261

theorem tailTrace_634631 : CollatzResearch.WordTrace tailWord_634631 prefixEnd_634631 217247160829074491329261 := by
  unfold tailWord_634631
  simp only [CollatzResearch.WordTrace]
  refine ⟨23146894163847748190831747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15431262775898498793887831 23146894163847748190831747)
  ·
    refine ⟨34720341245771622286247621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23146894163847748190831747 34720341245771622286247621)
    ·
      refine ⟨6510063983582179178671429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34720341245771622286247621 6510063983582179178671429)
      ·
        refine ⟨1220636996921658596000893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6510063983582179178671429 1220636996921658596000893)
        ·
          refine ⟨457738873845621973500335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1220636996921658596000893 457738873845621973500335)
          ·
            refine ⟨686608310768432960250503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 457738873845621973500335 686608310768432960250503)
            ·
              refine ⟨1029912466152649440375755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 686608310768432960250503 1029912466152649440375755)
              ·
                refine ⟨1544868699228974160563633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1029912466152649440375755 1544868699228974160563633)
                ·
                  refine ⟨1158651524421730620422725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1544868699228974160563633 1158651524421730620422725)
                  ·
                    refine ⟨217247160829074491329261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1158651524421730620422725 217247160829074491329261)
                    ·
                      rfl

theorem cell22_634631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 3, 1, 1, 1, 2, 4].length) (baseStart_634631 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_634631 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_634631 prefixEnd_634631 := by exact prefixLift 634631
  have htrace : WordTrace (prefixWord ++ tailWord_634631) baseStart_634631 baseEnd_634631 := by
    simpa [prefixWord, tailWord_634631, baseEnd_634631] using wordTrace_append hprefix tailTrace_634631
  have hstable : (prefixWord ++ tailWord_634631).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_634631).length < 2 ^ (prefixWord ++ tailWord_634631).sum := by decide
  have hdescent : baseEnd_634631 < baseStart_634631 := by decide
  rcases family_descends (prefixWord ++ tailWord_634631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_634637 : List Nat := [1, 7, 2, 1, 1, 2, 2, 1, 1, 4]
def baseStart_634637 : Nat := 118140960795 + 634637 * 2 ^ 59
def prefixEnd_634637 : Nat := 4983230072969 + 3 ^ 40 * 634637 * 2
def baseEnd_634637 : Nat := 217249214751692475679243

theorem tailTrace_634637 : CollatzResearch.WordTrace tailWord_634637 prefixEnd_634637 217249214751692475679243 := by
  unfold tailWord_634637
  simp only [CollatzResearch.WordTrace]
  refine ⟨23147113001826011215550165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15431408667884007477033443 23147113001826011215550165)
  ·
    refine ⟨542510460980297137864457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 23147113001826011215550165 542510460980297137864457)
    ·
      refine ⟨406882845735222853398343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 542510460980297137864457 406882845735222853398343)
      ·
        refine ⟨610324268602834280097515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 406882845735222853398343 610324268602834280097515)
        ·
          refine ⟨915486402904251420146273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 610324268602834280097515 915486402904251420146273)
          ·
            refine ⟨686614802178188565109705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 915486402904251420146273 686614802178188565109705)
            ·
              refine ⟨514961101633641423832279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 686614802178188565109705 514961101633641423832279)
              ·
                refine ⟨772441652450462135748419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 514961101633641423832279 772441652450462135748419)
                ·
                  refine ⟨1158662478675693203622629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 772441652450462135748419 1158662478675693203622629)
                  ·
                    refine ⟨217249214751692475679243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1158662478675693203622629 217249214751692475679243)
                    ·
                      rfl

theorem cell22_634637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 2, 2, 1, 1, 4].length) (baseStart_634637 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_634637 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_634637 prefixEnd_634637 := by exact prefixLift 634637
  have htrace : WordTrace (prefixWord ++ tailWord_634637) baseStart_634637 baseEnd_634637 := by
    simpa [prefixWord, tailWord_634637, baseEnd_634637] using wordTrace_append hprefix tailTrace_634637
  have hstable : (prefixWord ++ tailWord_634637).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_634637).length < 2 ^ (prefixWord ++ tailWord_634637).sum := by decide
  have hdescent : baseEnd_634637 < baseStart_634637 := by decide
  rcases family_descends (prefixWord ++ tailWord_634637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_634655 : List Nat := [1, 1, 2, 4, 2, 1, 1, 1, 4, 5]
def baseStart_634655 : Nat := 118140960795 + 634655 * 2 ^ 59
def prefixEnd_634655 : Nat := 4983230072969 + 3 ^ 40 * 634655 * 2
def baseEnd_634655 : Nat := 217255376519546428729187

theorem tailTrace_634655 : CollatzResearch.WordTrace tailWord_634655 prefixEnd_634655 217255376519546428729187 := by
  unfold tailWord_634655
  simp only [CollatzResearch.WordTrace]
  refine ⟨23147769515760800289705419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15431846343840533526470279 23147769515760800289705419)
  ·
    refine ⟨34721654273641200434558129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23147769515760800289705419 34721654273641200434558129)
    ·
      refine ⟨26041240705230900325918597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34721654273641200434558129 26041240705230900325918597)
      ·
        refine ⟨4882732632230793811109737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26041240705230900325918597 4882732632230793811109737)
        ·
          refine ⟨3662049474173095358332303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4882732632230793811109737 3662049474173095358332303)
          ·
            refine ⟨5493074211259643037498455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3662049474173095358332303 5493074211259643037498455)
            ·
              refine ⟨8239611316889464556247683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5493074211259643037498455 8239611316889464556247683)
              ·
                refine ⟨12359416975334196834371525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8239611316889464556247683 12359416975334196834371525)
                ·
                  refine ⟨2317390682875161906444661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12359416975334196834371525 2317390682875161906444661)
                  ·
                    refine ⟨217255376519546428729187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2317390682875161906444661 217255376519546428729187)
                    ·
                      rfl

theorem cell22_634655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 1, 4, 5].length) (baseStart_634655 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_634655 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_634655 prefixEnd_634655 := by exact prefixLift 634655
  have htrace : WordTrace (prefixWord ++ tailWord_634655) baseStart_634655 baseEnd_634655 := by
    simpa [prefixWord, tailWord_634655, baseEnd_634655] using wordTrace_append hprefix tailTrace_634655
  have hstable : (prefixWord ++ tailWord_634655).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_634655).length < 2 ^ (prefixWord ++ tailWord_634655).sum := by decide
  have hdescent : baseEnd_634655 < baseStart_634655 := by decide
  rcases family_descends (prefixWord ++ tailWord_634655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_634657 : List Nat := [1, 2, 3, 2, 1, 3, 3, 2, 5]
def baseStart_634657 : Nat := 118140960795 + 634657 * 2 ^ 59
def prefixEnd_634657 : Nat := 4983230072969 + 3 ^ 40 * 634657 * 2
def baseEnd_634657 : Nat := 72418687053473030059727

theorem tailTrace_634657 : CollatzResearch.WordTrace tailWord_634657 prefixEnd_634657 72418687053473030059727 := by
  unfold tailWord_634657
  simp only [CollatzResearch.WordTrace]
  refine ⟨23147842461753554631278225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15431894974502369754185483 23147842461753554631278225)
  ·
    refine ⟨17360881846315165973458669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23147842461753554631278225 17360881846315165973458669)
    ·
      refine ⟨6510330692368187240047001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17360881846315165973458669 6510330692368187240047001)
      ·
        refine ⟨4882748019276140430035251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6510330692368187240047001 4882748019276140430035251)
        ·
          refine ⟨7324122028914210645052877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4882748019276140430035251 7324122028914210645052877)
          ·
            refine ⟨2746545760842828991894829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7324122028914210645052877 2746545760842828991894829)
            ·
              refine ⟨1029954660316060871960561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2746545760842828991894829 1029954660316060871960561)
              ·
                refine ⟨772465995237045653970421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1029954660316060871960561 772465995237045653970421)
                ·
                  refine ⟨72418687053473030059727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 772465995237045653970421 72418687053473030059727)
                  ·
                    rfl

theorem cell22_634657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 3, 2, 5].length) (baseStart_634657 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_634657 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_634657 prefixEnd_634657 := by exact prefixLift 634657
  have htrace : WordTrace (prefixWord ++ tailWord_634657) baseStart_634657 baseEnd_634657 := by
    simpa [prefixWord, tailWord_634657, baseEnd_634657] using wordTrace_append hprefix tailTrace_634657
  have hstable : (prefixWord ++ tailWord_634657).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_634657).length < 2 ^ (prefixWord ++ tailWord_634657).sum := by decide
  have hdescent : baseEnd_634657 < baseStart_634657 := by decide
  rcases family_descends (prefixWord ++ tailWord_634657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_634674 : List Nat := [3, 2, 1, 1, 3, 3, 3, 1, 5]
def baseStart_634674 : Nat := 118140960795 + 634674 * 2 ^ 59
def prefixEnd_634674 : Nat := 4983230072969 + 3 ^ 40 * 634674 * 2
def baseEnd_634674 : Nat := 72420626869278904168043

theorem tailTrace_634674 : CollatzResearch.WordTrace tailWord_634674 prefixEnd_634674 72420626869278904168043 := by
  unfold tailWord_634674
  simp only [CollatzResearch.WordTrace]
  refine ⟨5787115625672991633661769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15432308335127977689764717 5787115625672991633661769)
  ·
    refine ⟨4340336719254743725246327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5787115625672991633661769 4340336719254743725246327)
    ·
      refine ⟨6510505078882115587869491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4340336719254743725246327 6510505078882115587869491)
      ·
        refine ⟨9765757618323173381804237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6510505078882115587869491 9765757618323173381804237)
        ·
          refine ⟨3662159106871190018176589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9765757618323173381804237 3662159106871190018176589)
          ·
            refine ⟨1373309665076696256816221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3662159106871190018176589 1373309665076696256816221)
            ·
              refine ⟨514991124403761096306083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1373309665076696256816221 514991124403761096306083)
              ·
                refine ⟨772486686605641644459125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 514991124403761096306083 772486686605641644459125)
                ·
                  refine ⟨72420626869278904168043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 772486686605641644459125 72420626869278904168043)
                  ·
                    rfl

theorem cell22_634674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 3, 1, 5].length) (baseStart_634674 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_634674 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_634674 prefixEnd_634674 := by exact prefixLift 634674
  have htrace : WordTrace (prefixWord ++ tailWord_634674) baseStart_634674 baseEnd_634674 := by
    simpa [prefixWord, tailWord_634674, baseEnd_634674] using wordTrace_append hprefix tailTrace_634674
  have hstable : (prefixWord ++ tailWord_634674).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_634674).length < 2 ^ (prefixWord ++ tailWord_634674).sum := by decide
  have hdescent : baseEnd_634674 < baseStart_634674 := by decide
  rcases family_descends (prefixWord ++ tailWord_634674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_634813 : List Nat := [1, 4, 1, 2, 3, 2, 2, 3, 1, 3]
def baseStart_634813 : Nat := 118140960795 + 634813 * 2 ^ 59
def prefixEnd_634813 : Nat := 4983230072969 + 3 ^ 40 * 634813 * 2
def baseEnd_634813 : Nat := 217309463148486683278703

theorem tailTrace_634813 : CollatzResearch.WordTrace tailWord_634813 prefixEnd_634813 217309463148486683278703 := by
  unfold tailWord_634813
  simp only [CollatzResearch.WordTrace]
  refine ⟨23153532249188393273957093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15435688166125595515971395 23153532249188393273957093)
  ·
    refine ⟨4341287296722823738866955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23153532249188393273957093 4341287296722823738866955)
    ·
      refine ⟨6511930945084235608300433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4341287296722823738866955 6511930945084235608300433)
      ·
        refine ⟨4883948208813176706225325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6511930945084235608300433 4883948208813176706225325)
        ·
          refine ⟨1831480578304941264834497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4883948208813176706225325 1831480578304941264834497)
          ·
            refine ⟨1373610433728705948625873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1831480578304941264834497 1373610433728705948625873)
            ·
              refine ⟨1030207825296529461469405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1373610433728705948625873 1030207825296529461469405)
              ·
                refine ⟨386327934486198548051027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1030207825296529461469405 386327934486198548051027)
                ·
                  refine ⟨579491901729297822076541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 386327934486198548051027 579491901729297822076541)
                  ·
                    refine ⟨217309463148486683278703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 579491901729297822076541 217309463148486683278703)
                    ·
                      rfl

theorem cell22_634813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 2, 3, 1, 3].length) (baseStart_634813 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_634813 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_634813 prefixEnd_634813 := by exact prefixLift 634813
  have htrace : WordTrace (prefixWord ++ tailWord_634813) baseStart_634813 baseEnd_634813 := by
    simpa [prefixWord, tailWord_634813, baseEnd_634813] using wordTrace_append hprefix tailTrace_634813
  have hstable : (prefixWord ++ tailWord_634813).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_634813).length < 2 ^ (prefixWord ++ tailWord_634813).sum := by decide
  have hdescent : baseEnd_634813 < baseStart_634813 := by decide
  rcases family_descends (prefixWord ++ tailWord_634813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_634867 : List Nat := [1, 1, 1, 2, 2, 2, 1, 2, 6, 4]
def baseStart_634867 : Nat := 118140960795 + 634867 * 2 ^ 59
def prefixEnd_634867 : Nat := 4983230072969 + 3 ^ 40 * 634867 * 2
def baseEnd_634867 : Nat := 217327948452048542428537

theorem tailTrace_634867 : CollatzResearch.WordTrace tailWord_634867 prefixEnd_634867 217327948452048542428537 := by
  unfold tailWord_634867
  simp only [CollatzResearch.WordTrace]
  refine ⟨23155501790992760496422855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15437001193995173664281903 23155501790992760496422855)
  ·
    refine ⟨34733252686489140744634283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23155501790992760496422855 34733252686489140744634283)
    ·
      refine ⟨52099879029733711116951425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34733252686489140744634283 52099879029733711116951425)
      ·
        refine ⟨39074909272300283337713569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52099879029733711116951425 39074909272300283337713569)
        ·
          refine ⟨29306181954225212503285177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39074909272300283337713569 29306181954225212503285177)
          ·
            refine ⟨21979636465668909377463883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29306181954225212503285177 21979636465668909377463883)
            ·
              refine ⟨32969454698503364066195825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21979636465668909377463883 32969454698503364066195825)
              ·
                refine ⟨24727091023877523049646869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32969454698503364066195825 24727091023877523049646869)
                ·
                  refine ⟨1159082391744258892952197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 24727091023877523049646869 1159082391744258892952197)
                  ·
                    refine ⟨217327948452048542428537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1159082391744258892952197 217327948452048542428537)
                    ·
                      rfl

theorem cell22_634867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 2, 6, 4].length) (baseStart_634867 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_634867 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_634867 prefixEnd_634867 := by exact prefixLift 634867
  have htrace : WordTrace (prefixWord ++ tailWord_634867) baseStart_634867 baseEnd_634867 := by
    simpa [prefixWord, tailWord_634867, baseEnd_634867] using wordTrace_append hprefix tailTrace_634867
  have hstable : (prefixWord ++ tailWord_634867).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_634867).length < 2 ^ (prefixWord ++ tailWord_634867).sum := by decide
  have hdescent : baseEnd_634867 < baseStart_634867 := by decide
  rcases family_descends (prefixWord ++ tailWord_634867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_634903 : List Nat := [1, 1, 3, 5, 2, 1, 1, 3, 2, 3]
def baseStart_634903 : Nat := 118140960795 + 634903 * 2 ^ 59
def prefixEnd_634903 : Nat := 4983230072969 + 3 ^ 40 * 634903 * 2
def baseEnd_634903 : Nat := 217340271987756448528427

theorem tailTrace_634903 : CollatzResearch.WordTrace tailWord_634903 prefixEnd_634903 217340271987756448528427 := by
  unfold tailWord_634903
  simp only [CollatzResearch.WordTrace]
  refine ⟨23156814818862338644733363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15437876545908225763155575 23156814818862338644733363)
  ·
    refine ⟨34735222228293507967100045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23156814818862338644733363 34735222228293507967100045)
    ·
      refine ⟨13025708335610065487662517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34735222228293507967100045 13025708335610065487662517)
      ·
        refine ⟨1221160156463443639468361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 13025708335610065487662517 1221160156463443639468361)
        ·
          refine ⟨915870117347582729601271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1221160156463443639468361 915870117347582729601271)
          ·
            refine ⟨1373805176021374094401907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 915870117347582729601271 1373805176021374094401907)
            ·
              refine ⟨2060707764032061141602861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1373805176021374094401907 2060707764032061141602861)
              ·
                refine ⟨772765411512022928101073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2060707764032061141602861 772765411512022928101073)
                ·
                  refine ⟨579574058634017196075805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 772765411512022928101073 579574058634017196075805)
                  ·
                    refine ⟨217340271987756448528427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 579574058634017196075805 217340271987756448528427)
                    ·
                      rfl

theorem cell22_634903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 1, 3, 2, 3].length) (baseStart_634903 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_634903 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_634903 prefixEnd_634903 := by exact prefixLift 634903
  have htrace : WordTrace (prefixWord ++ tailWord_634903) baseStart_634903 baseEnd_634903 := by
    simpa [prefixWord, tailWord_634903, baseEnd_634903] using wordTrace_append hprefix tailTrace_634903
  have hstable : (prefixWord ++ tailWord_634903).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_634903).length < 2 ^ (prefixWord ++ tailWord_634903).sum := by decide
  have hdescent : baseEnd_634903 < baseStart_634903 := by decide
  rcases family_descends (prefixWord ++ tailWord_634903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_634927 : List Nat := [1, 1, 2, 1, 2, 1, 1, 6, 7]
def baseStart_634927 : Nat := 118140960795 + 634927 * 2 ^ 59
def prefixEnd_634927 : Nat := 4983230072969 + 3 ^ 40 * 634927 * 2
def baseEnd_634927 : Nat := 72449495892742795309451

theorem tailTrace_634927 : CollatzResearch.WordTrace tailWord_634927 prefixEnd_634927 72449495892742795309451 := by
  unfold tailWord_634927
  simp only [CollatzResearch.WordTrace]
  refine ⟨23157690170775390743607035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15438460113850260495738023 23157690170775390743607035)
  ·
    refine ⟨34736535256163086115410553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23157690170775390743607035 34736535256163086115410553)
    ·
      refine ⟨26052401442122314586557915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34736535256163086115410553 26052401442122314586557915)
      ·
        refine ⟨39078602163183471879836873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26052401442122314586557915 39078602163183471879836873)
        ·
          refine ⟨29308951622387603909877655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39078602163183471879836873 29308951622387603909877655)
          ·
            refine ⟨43963427433581405864816483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29308951622387603909877655 43963427433581405864816483)
            ·
              refine ⟨65945141150372108797224725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43963427433581405864816483 65945141150372108797224725)
              ·
                refine ⟨3091178491423692599869909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 65945141150372108797224725 3091178491423692599869909)
                ·
                  refine ⟨72449495892742795309451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3091178491423692599869909 72449495892742795309451)
                  ·
                    rfl

theorem cell22_634927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 6, 7].length) (baseStart_634927 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_634927 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_634927 prefixEnd_634927 := by exact prefixLift 634927
  have htrace : WordTrace (prefixWord ++ tailWord_634927) baseStart_634927 baseEnd_634927 := by
    simpa [prefixWord, tailWord_634927, baseEnd_634927] using wordTrace_append hprefix tailTrace_634927
  have hstable : (prefixWord ++ tailWord_634927).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_634927).length < 2 ^ (prefixWord ++ tailWord_634927).sum := by decide
  have hdescent : baseEnd_634927 < baseStart_634927 := by decide
  rcases family_descends (prefixWord ++ tailWord_634927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_634944 : List Nat := [2, 1, 1, 2, 2, 4, 1, 4, 5]
def baseStart_634944 : Nat := 118140960795 + 634944 * 2 ^ 59
def prefixEnd_634944 : Nat := 4983230072969 + 3 ^ 40 * 634944 * 2
def baseEnd_634944 : Nat := 72451435708548669417767

theorem tailTrace_634944 : CollatzResearch.WordTrace tailWord_634944 prefixEnd_634944 72451435708548669417767 := by
  unfold tailWord_634944
  simp only [CollatzResearch.WordTrace]
  refine ⟨11579155105856901323487943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15438873474475868431317257 11579155105856901323487943)
  ·
    refine ⟨17368732658785351985231915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11579155105856901323487943 17368732658785351985231915)
    ·
      refine ⟨26053098988178027977847873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17368732658785351985231915 26053098988178027977847873)
      ·
        refine ⟨19539824241133520983385905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26053098988178027977847873 19539824241133520983385905)
        ·
          refine ⟨14654868180850140737539429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19539824241133520983385905 14654868180850140737539429)
          ·
            refine ⟨2747787783909401388288643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14654868180850140737539429 2747787783909401388288643)
            ·
              refine ⟨4121681675864102082432965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2747787783909401388288643 4121681675864102082432965)
              ·
                refine ⟨772815314224519140456181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4121681675864102082432965 772815314224519140456181)
                ·
                  refine ⟨72451435708548669417767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 772815314224519140456181 72451435708548669417767)
                  ·
                    rfl

theorem cell22_634944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 1, 4, 5].length) (baseStart_634944 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_634944 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_634944 prefixEnd_634944 := by exact prefixLift 634944
  have htrace : WordTrace (prefixWord ++ tailWord_634944) baseStart_634944 baseEnd_634944 := by
    simpa [prefixWord, tailWord_634944, baseEnd_634944] using wordTrace_append hprefix tailTrace_634944
  have hstable : (prefixWord ++ tailWord_634944).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_634944).length < 2 ^ (prefixWord ++ tailWord_634944).sum := by decide
  have hdescent : baseEnd_634944 < baseStart_634944 := by decide
  rcases family_descends (prefixWord ++ tailWord_634944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_634989 : List Nat := [1, 5, 1, 1, 2, 1, 1, 2, 8]
def baseStart_634989 : Nat := 118140960795 + 634989 * 2 ^ 59
def prefixEnd_634989 : Nat := 4983230072969 + 3 ^ 40 * 634989 * 2
def baseEnd_634989 : Nat := 72456570515093630292721

theorem tailTrace_634989 : CollatzResearch.WordTrace tailWord_634989 prefixEnd_634989 72456570515093630292721 := by
  unfold tailWord_634989
  simp only [CollatzResearch.WordTrace]
  refine ⟨23159951496550775332364021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15439967664367183554909347 23159951496550775332364021)
  ·
    refine ⟨2171245452801635187409127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 23159951496550775332364021 2171245452801635187409127)
    ·
      refine ⟨3256868179202452781113691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2171245452801635187409127 3256868179202452781113691)
      ·
        refine ⟨4885302268803679171670537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3256868179202452781113691 4885302268803679171670537)
        ·
          refine ⟨3663976701602759378752903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4885302268803679171670537 3663976701602759378752903)
          ·
            refine ⟨5495965052404139068129355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3663976701602759378752903 5495965052404139068129355)
            ·
              refine ⟨8243947578606208602194033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5495965052404139068129355 8243947578606208602194033)
              ·
                refine ⟨6182960683954656451645525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8243947578606208602194033 6182960683954656451645525)
                ·
                  refine ⟨72456570515093630292721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 6182960683954656451645525 72456570515093630292721)
                  ·
                    rfl

theorem cell22_634989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 2, 8].length) (baseStart_634989 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_634989 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_634989 prefixEnd_634989 := by exact prefixLift 634989
  have htrace : WordTrace (prefixWord ++ tailWord_634989) baseStart_634989 baseEnd_634989 := by
    simpa [prefixWord, tailWord_634989, baseEnd_634989] using wordTrace_append hprefix tailTrace_634989
  have hstable : (prefixWord ++ tailWord_634989).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_634989).length < 2 ^ (prefixWord ++ tailWord_634989).sum := by decide
  have hdescent : baseEnd_634989 < baseStart_634989 := by decide
  rcases family_descends (prefixWord ++ tailWord_634989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_634991 : List Nat := [1, 1, 2, 1, 3, 5, 1, 3, 1, 4]
def baseStart_634991 : Nat := 118140960795 + 634991 * 2 ^ 59
def prefixEnd_634991 : Nat := 4983230072969 + 3 ^ 40 * 634991 * 2
def baseEnd_634991 : Nat := 217370396186153552328157

theorem tailTrace_634991 : CollatzResearch.WordTrace tailWord_634991 prefixEnd_634991 217370396186153552328157 := by
  unfold tailWord_634991
  simp only [CollatzResearch.WordTrace]
  refine ⟨23160024442543529673936827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15440016295029019782624551 23160024442543529673936827)
  ·
    refine ⟨34740036663815294510905241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23160024442543529673936827 34740036663815294510905241)
    ·
      refine ⟨26055027497861470883178931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34740036663815294510905241 26055027497861470883178931)
      ·
        refine ⟨39082541246792206324768397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26055027497861470883178931 39082541246792206324768397)
        ·
          refine ⟨14655952967547077371788149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39082541246792206324768397 14655952967547077371788149)
          ·
            refine ⟨1373995590707538503605139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 14655952967547077371788149 1373995590707538503605139)
            ·
              refine ⟨2060993386061307755407709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1373995590707538503605139 2060993386061307755407709)
              ·
                refine ⟨772872519772990408277891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2060993386061307755407709 772872519772990408277891)
                ·
                  refine ⟨1159308779659485612416837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 772872519772990408277891 1159308779659485612416837)
                  ·
                    refine ⟨217370396186153552328157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1159308779659485612416837 217370396186153552328157)
                    ·
                      rfl

theorem cell22_634991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 1, 3, 1, 4].length) (baseStart_634991 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_634991 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_634991 prefixEnd_634991 := by exact prefixLift 634991
  have htrace : WordTrace (prefixWord ++ tailWord_634991) baseStart_634991 baseEnd_634991 := by
    simpa [prefixWord, tailWord_634991, baseEnd_634991] using wordTrace_append hprefix tailTrace_634991
  have hstable : (prefixWord ++ tailWord_634991).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_634991).length < 2 ^ (prefixWord ++ tailWord_634991).sum := by decide
  have hdescent : baseEnd_634991 < baseStart_634991 := by decide
  rcases family_descends (prefixWord ++ tailWord_634991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_635036 : List Nat := [2, 2, 3, 2, 1, 1, 2, 3, 2, 4]
def baseStart_635036 : Nat := 118140960795 + 635036 * 2 ^ 59
def prefixEnd_635036 : Nat := 4983230072969 + 3 ^ 40 * 635036 * 2
def baseEnd_635036 : Nat := 217385800605788434953019

theorem tailTrace_635036 : CollatzResearch.WordTrace tailWord_635036 prefixEnd_635036 217385800605788434953019 := by
  unfold tailWord_635036
  simp only [CollatzResearch.WordTrace]
  refine ⟨11580832863690251179662481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15441110484920334906216641 11580832863690251179662481)
  ·
    refine ⟨8685624647767688384746861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11580832863690251179662481 8685624647767688384746861)
    ·
      refine ⟨3257109242912883144280073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8685624647767688384746861 3257109242912883144280073)
      ·
        refine ⟨2442831932184662358210055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3257109242912883144280073 2442831932184662358210055)
        ·
          refine ⟨3664247898276993537315083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2442831932184662358210055 3664247898276993537315083)
          ·
            refine ⟨5496371847415490305972625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3664247898276993537315083 5496371847415490305972625)
            ·
              refine ⟨4122278885561617729479469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5496371847415490305972625 4122278885561617729479469)
              ·
                refine ⟨1545854582085606648554801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4122278885561617729479469 1545854582085606648554801)
                ·
                  refine ⟨1159390936564204986416101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1545854582085606648554801 1159390936564204986416101)
                  ·
                    refine ⟨217385800605788434953019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1159390936564204986416101 217385800605788434953019)
                    ·
                      rfl

theorem cell22_635036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 2, 3, 2, 4].length) (baseStart_635036 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_635036 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_635036 prefixEnd_635036 := by exact prefixLift 635036
  have htrace : WordTrace (prefixWord ++ tailWord_635036) baseStart_635036 baseEnd_635036 := by
    simpa [prefixWord, tailWord_635036, baseEnd_635036] using wordTrace_append hprefix tailTrace_635036
  have hstable : (prefixWord ++ tailWord_635036).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_635036).length < 2 ^ (prefixWord ++ tailWord_635036).sum := by decide
  have hdescent : baseEnd_635036 < baseStart_635036 := by decide
  rcases family_descends (prefixWord ++ tailWord_635036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_635053 : List Nat := [1, 5, 2, 1, 2, 2, 1, 2, 2, 4]
def baseStart_635053 : Nat := 118140960795 + 635053 * 2 ^ 59
def prefixEnd_635053 : Nat := 4983230072969 + 3 ^ 40 * 635053 * 2
def baseEnd_635053 : Nat := 217391620053206057277967

theorem tailTrace_635053 : CollatzResearch.WordTrace tailWord_635053 prefixEnd_635053 217391620053206057277967 := by
  unfold tailWord_635053
  simp only [CollatzResearch.WordTrace]
  refine ⟨23162285768318914262693813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15441523845545942841795875 23162285768318914262693813)
  ·
    refine ⟨2171464290779898212127545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 23162285768318914262693813 2171464290779898212127545)
    ·
      refine ⟨1628598218084923659095659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2171464290779898212127545 1628598218084923659095659)
      ·
        refine ⟨2442897327127385488643489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1628598218084923659095659 2442897327127385488643489)
        ·
          refine ⟨1832172995345539116482617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2442897327127385488643489 1832172995345539116482617)
          ·
            refine ⟨1374129746509154337361963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1832172995345539116482617 1374129746509154337361963)
            ·
              refine ⟨2061194619763731506042945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1374129746509154337361963 2061194619763731506042945)
              ·
                refine ⟨1545895964822798629532209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2061194619763731506042945 1545895964822798629532209)
                ·
                  refine ⟨1159421973617098972149157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1545895964822798629532209 1159421973617098972149157)
                  ·
                    refine ⟨217391620053206057277967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1159421973617098972149157 217391620053206057277967)
                    ·
                      rfl

theorem cell22_635053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 1, 2, 2, 4].length) (baseStart_635053 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_635053 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_635053 prefixEnd_635053 := by exact prefixLift 635053
  have htrace : WordTrace (prefixWord ++ tailWord_635053) baseStart_635053 baseEnd_635053 := by
    simpa [prefixWord, tailWord_635053, baseEnd_635053] using wordTrace_append hprefix tailTrace_635053
  have hstable : (prefixWord ++ tailWord_635053).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_635053).length < 2 ^ (prefixWord ++ tailWord_635053).sum := by decide
  have hdescent : baseEnd_635053 < baseStart_635053 := by decide
  rcases family_descends (prefixWord ++ tailWord_635053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_635064 : List Nat := [2, 1, 2, 1, 2, 1, 4, 1, 2, 6]
def baseStart_635064 : Nat := 118140960795 + 635064 * 2 ^ 59
def prefixEnd_635064 : Nat := 4983230072969 + 3 ^ 40 * 635064 * 2
def baseEnd_635064 : Nat := 217395385578005695252933

theorem tailTrace_635064 : CollatzResearch.WordTrace tailWord_635064 prefixEnd_635064 217395385578005695252933 := by
  unfold tailWord_635064
  simp only [CollatzResearch.WordTrace]
  refine ⟨11581343485639531570672123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15441791314186042094229497 11581343485639531570672123)
  ·
    refine ⟨17372015228459297356008185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11581343485639531570672123 17372015228459297356008185)
    ·
      refine ⟨13029011421344473017006139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17372015228459297356008185 13029011421344473017006139)
      ·
        refine ⟨19543517132016709525509209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13029011421344473017006139 19543517132016709525509209)
        ·
          refine ⟨14657637849012532144131907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19543517132016709525509209 14657637849012532144131907)
          ·
            refine ⟨21986456773518798216197861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14657637849012532144131907 21986456773518798216197861)
            ·
              refine ⟨4122460645034774665537099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21986456773518798216197861 4122460645034774665537099)
              ·
                refine ⟨6183690967552161998305649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4122460645034774665537099 6183690967552161998305649)
                ·
                  refine ⟨4637768225664121498729237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6183690967552161998305649 4637768225664121498729237)
                  ·
                    refine ⟨217395385578005695252933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4637768225664121498729237 217395385578005695252933)
                    ·
                      rfl

theorem cell22_635064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 4, 1, 2, 6].length) (baseStart_635064 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_635064 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_635064 prefixEnd_635064 := by exact prefixLift 635064
  have htrace : WordTrace (prefixWord ++ tailWord_635064) baseStart_635064 baseEnd_635064 := by
    simpa [prefixWord, tailWord_635064, baseEnd_635064] using wordTrace_append hprefix tailTrace_635064
  have hstable : (prefixWord ++ tailWord_635064).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_635064).length < 2 ^ (prefixWord ++ tailWord_635064).sum := by decide
  have hdescent : baseEnd_635064 < baseStart_635064 := by decide
  rcases family_descends (prefixWord ++ tailWord_635064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_635117 : List Nat := [1, 5, 1, 2, 3, 1, 1, 4, 1, 3]
def baseStart_635117 : Nat := 118140960795 + 635117 * 2 ^ 59
def prefixEnd_635117 : Nat := 4983230072969 + 3 ^ 40 * 635117 * 2
def baseEnd_635117 : Nat := 217413528561131223677771

theorem tailTrace_635117 : CollatzResearch.WordTrace tailWord_635117 prefixEnd_635117 217413528561131223677771 := by
  unfold tailWord_635117
  simp only [CollatzResearch.WordTrace]
  refine ⟨23164620040087053193023605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15443080026724702128682403 23164620040087053193023605)
  ·
    refine ⟨2171683128758161236845963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 23164620040087053193023605 2171683128758161236845963)
    ·
      refine ⟨3257524693137241855268945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2171683128758161236845963 3257524693137241855268945)
      ·
        refine ⟨2443143519852931391451709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3257524693137241855268945 2443143519852931391451709)
        ·
          refine ⟨916178819944849271794391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2443143519852931391451709 916178819944849271794391)
          ·
            refine ⟨1374268229917273907691587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 916178819944849271794391 1374268229917273907691587)
            ·
              refine ⟨2061402344875910861537381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1374268229917273907691587 2061402344875910861537381)
              ·
                refine ⟨386512939664233286538259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2061402344875910861537381 386512939664233286538259)
                ·
                  refine ⟨579769409496349929807389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 386512939664233286538259 579769409496349929807389)
                  ·
                    refine ⟨217413528561131223677771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 579769409496349929807389 217413528561131223677771)
                    ·
                      rfl

theorem cell22_635117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 1, 4, 1, 3].length) (baseStart_635117 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_635117 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_635117 prefixEnd_635117 := by exact prefixLift 635117
  have htrace : WordTrace (prefixWord ++ tailWord_635117) baseStart_635117 baseEnd_635117 := by
    simpa [prefixWord, tailWord_635117, baseEnd_635117] using wordTrace_append hprefix tailTrace_635117
  have hstable : (prefixWord ++ tailWord_635117).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_635117).length < 2 ^ (prefixWord ++ tailWord_635117).sum := by decide
  have hdescent : baseEnd_635117 < baseStart_635117 := by decide
  rcases family_descends (prefixWord ++ tailWord_635117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_635171 : List Nat := [1, 1, 1, 4, 2, 2, 2, 1, 4, 4]
def baseStart_635171 : Nat := 118140960795 + 635171 * 2 ^ 59
def prefixEnd_635171 : Nat := 4983230072969 + 3 ^ 40 * 635171 * 2
def baseEnd_635171 : Nat := 217432013864693082827605

theorem tailTrace_635171 : CollatzResearch.WordTrace tailWord_635171 prefixEnd_635171 217432013864693082827605 := by
  unfold tailWord_635171
  simp only [CollatzResearch.WordTrace]
  refine ⟨23166589581891420415489367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15444393054594280276992911 23166589581891420415489367)
  ·
    refine ⟨34749884372837130623234051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23166589581891420415489367 34749884372837130623234051)
    ·
      refine ⟨52124826559255695934851077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34749884372837130623234051 52124826559255695934851077)
      ·
        refine ⟨9773404979860442987784577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 52124826559255695934851077 9773404979860442987784577)
        ·
          refine ⟨7330053734895332240838433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9773404979860442987784577 7330053734895332240838433)
          ·
            refine ⟨5497540301171499180628825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7330053734895332240838433 5497540301171499180628825)
            ·
              refine ⟨4123155225878624385471619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5497540301171499180628825 4123155225878624385471619)
              ·
                refine ⟨6184732838817936578207429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4123155225878624385471619 6184732838817936578207429)
                ·
                  refine ⟨1159637407278363108413893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6184732838817936578207429 1159637407278363108413893)
                  ·
                    refine ⟨217432013864693082827605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1159637407278363108413893 217432013864693082827605)
                    ·
                      rfl

theorem cell22_635171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 2, 1, 4, 4].length) (baseStart_635171 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_635171 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_635171 prefixEnd_635171 := by exact prefixLift 635171
  have htrace : WordTrace (prefixWord ++ tailWord_635171) baseStart_635171 baseEnd_635171 := by
    simpa [prefixWord, tailWord_635171, baseEnd_635171] using wordTrace_append hprefix tailTrace_635171
  have hstable : (prefixWord ++ tailWord_635171).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_635171).length < 2 ^ (prefixWord ++ tailWord_635171).sum := by decide
  have hdescent : baseEnd_635171 < baseStart_635171 := by decide
  rcases family_descends (prefixWord ++ tailWord_635171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_635188 : List Nat := [2, 5, 1, 1, 1, 2, 1, 2, 1, 6]
def baseStart_635188 : Nat := 118140960795 + 635188 * 2 ^ 59
def prefixEnd_635188 : Nat := 4983230072969 + 3 ^ 40 * 635188 * 2
def baseEnd_635188 : Nat := 217437833312110705152553

theorem tailTrace_635188 : CollatzResearch.WordTrace tailWord_635188 prefixEnd_635188 217437833312110705152553 := by
  unfold tailWord_635188
  simp only [CollatzResearch.WordTrace]
  refine ⟨11583604811414916159429109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15444806415219888212572145 11583604811414916159429109)
  ·
    refine ⟨1085962951070148389946479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 11583604811414916159429109 1085962951070148389946479)
    ·
      refine ⟨1628944426605222584919719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1085962951070148389946479 1628944426605222584919719)
      ·
        refine ⟨2443416639907833877379579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1628944426605222584919719 2443416639907833877379579)
        ·
          refine ⟨3665124959861750816069369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2443416639907833877379579 3665124959861750816069369)
          ·
            refine ⟨2748843719896313112052027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3665124959861750816069369 2748843719896313112052027)
            ·
              refine ⟨4123265579844469668078041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2748843719896313112052027 4123265579844469668078041)
              ·
                refine ⟨3092449184883352251058531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4123265579844469668078041 3092449184883352251058531)
                ·
                  refine ⟨4638673777325028376587797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3092449184883352251058531 4638673777325028376587797)
                  ·
                    refine ⟨217437833312110705152553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4638673777325028376587797 217437833312110705152553)
                    ·
                      rfl

theorem cell22_635188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 1, 2, 1, 6].length) (baseStart_635188 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_635188 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_635188 prefixEnd_635188 := by exact prefixLift 635188
  have htrace : WordTrace (prefixWord ++ tailWord_635188) baseStart_635188 baseEnd_635188 := by
    simpa [prefixWord, tailWord_635188, baseEnd_635188] using wordTrace_append hprefix tailTrace_635188
  have hstable : (prefixWord ++ tailWord_635188).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_635188).length < 2 ^ (prefixWord ++ tailWord_635188).sum := by decide
  have hdescent : baseEnd_635188 < baseStart_635188 := by decide
  rcases family_descends (prefixWord ++ tailWord_635188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_635218 : List Nat := [3, 2, 2, 1, 1, 1, 2, 2, 5, 3]
def baseStart_635218 : Nat := 118140960795 + 635218 * 2 ^ 59
def prefixEnd_635218 : Nat := 4983230072969 + 3 ^ 40 * 635218 * 2
def baseEnd_635218 : Nat := 217448102925200626902461

theorem tailTrace_635218 : CollatzResearch.WordTrace tailWord_635218 prefixEnd_635218 217448102925200626902461 := by
  unfold tailWord_635218
  simp only [CollatzResearch.WordTrace]
  refine ⟨5792075953180286860612577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15445535875147431628300205 5792075953180286860612577)
  ·
    refine ⟨4344056964885215145459433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5792075953180286860612577 4344056964885215145459433)
    ·
      refine ⟨3258042723663911359094575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4344056964885215145459433 3258042723663911359094575)
      ·
        refine ⟨4887064085495867038641863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3258042723663911359094575 4887064085495867038641863)
        ·
          refine ⟨7330596128243800557962795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4887064085495867038641863 7330596128243800557962795)
          ·
            refine ⟨10995894192365700836944193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7330596128243800557962795 10995894192365700836944193)
            ·
              refine ⟨8246920644274275627708145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10995894192365700836944193 8246920644274275627708145)
              ·
                refine ⟨6185190483205706720781109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8246920644274275627708145 6185190483205706720781109)
                ·
                  refine ⟨579861607800535005073229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 6185190483205706720781109 579861607800535005073229)
                  ·
                    refine ⟨217448102925200626902461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 579861607800535005073229 217448102925200626902461)
                    ·
                      rfl

theorem cell22_635218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 2, 5, 3].length) (baseStart_635218 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_635218 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_635218 prefixEnd_635218 := by exact prefixLift 635218
  have htrace : WordTrace (prefixWord ++ tailWord_635218) baseStart_635218 baseEnd_635218 := by
    simpa [prefixWord, tailWord_635218, baseEnd_635218] using wordTrace_append hprefix tailTrace_635218
  have hstable : (prefixWord ++ tailWord_635218).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_635218).length < 2 ^ (prefixWord ++ tailWord_635218).sum := by decide
  have hdescent : baseEnd_635218 < baseStart_635218 := by decide
  rcases family_descends (prefixWord ++ tailWord_635218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_635231 : List Nat := [1, 1, 2, 3, 1, 2, 4, 1, 7]
def baseStart_635231 : Nat := 118140960795 + 635231 * 2 ^ 59
def prefixEnd_635231 : Nat := 4983230072969 + 3 ^ 40 * 635231 * 2
def baseEnd_635231 : Nat := 72484184363624308775807

theorem tailTrace_635231 : CollatzResearch.WordTrace tailWord_635231 prefixEnd_635231 72484184363624308775807 := by
  unfold tailWord_635231
  simp only [CollatzResearch.WordTrace]
  refine ⟨23168777961674050662673547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15445851974449367108449031 23168777961674050662673547)
  ·
    refine ⟨34753166942511075994010321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23168777961674050662673547 34753166942511075994010321)
    ·
      refine ⟨26064875206883306995507741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34753166942511075994010321 26064875206883306995507741)
      ·
        refine ⟨9774328202581240123315403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26064875206883306995507741 9774328202581240123315403)
        ·
          refine ⟨14661492303871860184973105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9774328202581240123315403 14661492303871860184973105)
          ·
            refine ⟨10996119227903895138729829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14661492303871860184973105 10996119227903895138729829)
            ·
              refine ⟨2061772355231980338511843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10996119227903895138729829 2061772355231980338511843)
              ·
                refine ⟨3092658532847970507767765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2061772355231980338511843 3092658532847970507767765)
                ·
                  refine ⟨72484184363624308775807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3092658532847970507767765 72484184363624308775807)
                  ·
                    rfl

theorem cell22_635231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 4, 1, 7].length) (baseStart_635231 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_635231 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_635231 prefixEnd_635231 := by exact prefixLift 635231
  have htrace : WordTrace (prefixWord ++ tailWord_635231) baseStart_635231 baseEnd_635231 := by
    simpa [prefixWord, tailWord_635231, baseEnd_635231] using wordTrace_append hprefix tailTrace_635231
  have hstable : (prefixWord ++ tailWord_635231).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_635231).length < 2 ^ (prefixWord ++ tailWord_635231).sum := by decide
  have hdescent : baseEnd_635231 < baseStart_635231 := by decide
  rcases family_descends (prefixWord ++ tailWord_635231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_635248 : List Nat := [2, 1, 1, 1, 4, 4, 1, 3, 5]
def baseStart_635248 : Nat := 118140960795 + 635248 * 2 ^ 59
def prefixEnd_635248 : Nat := 4983230072969 + 3 ^ 40 * 635248 * 2
def baseEnd_635248 : Nat := 72486124179430182884123

theorem tailTrace_635248 : CollatzResearch.WordTrace tailWord_635248 prefixEnd_635248 72486124179430182884123 := by
  unfold tailWord_635248
  simp only [CollatzResearch.WordTrace]
  refine ⟨11584699001306231283021199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15446265335074975044028265 11584699001306231283021199)
  ·
    refine ⟨17377048501959346924531799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11584699001306231283021199 17377048501959346924531799)
    ·
      refine ⟨26065572752939020386797699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17377048501959346924531799 26065572752939020386797699)
      ·
        refine ⟨39098359129408530580196549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26065572752939020386797699 39098359129408530580196549)
        ·
          refine ⟨7330942336764099483786853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39098359129408530580196549 7330942336764099483786853)
          ·
            refine ⟨1374551688143268653210035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7330942336764099483786853 1374551688143268653210035)
            ·
              refine ⟨2061827532214902979815053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1374551688143268653210035 2061827532214902979815053)
              ·
                refine ⟨773185324580588617430645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2061827532214902979815053 773185324580588617430645)
                ·
                  refine ⟨72486124179430182884123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 773185324580588617430645 72486124179430182884123)
                  ·
                    rfl

theorem cell22_635248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 1, 3, 5].length) (baseStart_635248 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_635248 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_635248 prefixEnd_635248 := by exact prefixLift 635248
  have htrace : WordTrace (prefixWord ++ tailWord_635248) baseStart_635248 baseEnd_635248 := by
    simpa [prefixWord, tailWord_635248, baseEnd_635248] using wordTrace_append hprefix tailTrace_635248
  have hstable : (prefixWord ++ tailWord_635248).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_635248).length < 2 ^ (prefixWord ++ tailWord_635248).sum := by decide
  have hdescent : baseEnd_635248 < baseStart_635248 := by decide
  rcases family_descends (prefixWord ++ tailWord_635248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_635308 : List Nat := [2, 2, 1, 1, 1, 1, 3, 2, 6, 3]
def baseStart_635308 : Nat := 118140960795 + 635308 * 2 ^ 59
def prefixEnd_635308 : Nat := 4983230072969 + 3 ^ 40 * 635308 * 2
def baseEnd_635308 : Nat := 217478911764470392152185

theorem tailTrace_635308 : CollatzResearch.WordTrace tailWord_635308 prefixEnd_635308 217478911764470392152185 := by
  unfold tailWord_635308
  simp only [CollatzResearch.WordTrace]
  refine ⟨11585793191197546406613289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15447724254930061875484385 11585793191197546406613289)
  ·
    refine ⟨8689344893398159804959967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11585793191197546406613289 8689344893398159804959967)
    ·
      refine ⟨13034017340097239707439951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8689344893398159804959967 13034017340097239707439951)
      ·
        refine ⟨19551026010145859561159927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13034017340097239707439951 19551026010145859561159927)
        ·
          refine ⟨29326539015218789341739891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19551026010145859561159927 29326539015218789341739891)
          ·
            refine ⟨43989808522828184012609837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29326539015218789341739891 43989808522828184012609837)
            ·
              refine ⟨16496178196060569004728689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43989808522828184012609837 16496178196060569004728689)
              ·
                refine ⟨12372133647045426753546517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16496178196060569004728689 12372133647045426753546517)
                ·
                  refine ⟨579943764705254379072493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 12372133647045426753546517 579943764705254379072493)
                  ·
                    refine ⟨217478911764470392152185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 579943764705254379072493 217478911764470392152185)
                    ·
                      rfl

theorem cell22_635308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 6, 3].length) (baseStart_635308 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_635308 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_635308 prefixEnd_635308 := by exact prefixLift 635308
  have htrace : WordTrace (prefixWord ++ tailWord_635308) baseStart_635308 baseEnd_635308 := by
    simpa [prefixWord, tailWord_635308, baseEnd_635308] using wordTrace_append hprefix tailTrace_635308
  have hstable : (prefixWord ++ tailWord_635308).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_635308).length < 2 ^ (prefixWord ++ tailWord_635308).sum := by decide
  have hdescent : baseEnd_635308 < baseStart_635308 := by decide
  rcases family_descends (prefixWord ++ tailWord_635308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_635447 : List Nat := [1, 1, 3, 1, 2, 3, 5, 1, 1, 4]
def baseStart_635447 : Nat := 118140960795 + 635447 * 2 ^ 59
def prefixEnd_635447 : Nat := 4983230072969 + 3 ^ 40 * 635447 * 2
def baseEnd_635447 : Nat := 217526494305120362926759

theorem tailTrace_635447 : CollatzResearch.WordTrace tailWord_635447 prefixEnd_635447 217526494305120362926759 := by
  unfold tailWord_635447
  simp only [CollatzResearch.WordTrace]
  refine ⟨23176656128891519552536595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15451104085927679701691063 23176656128891519552536595)
  ·
    refine ⟨34764984193337279328804893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23176656128891519552536595 34764984193337279328804893)
    ·
      refine ⟨13036869072501479748301835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34764984193337279328804893 13036869072501479748301835)
      ·
        refine ⟨19555303608752219622452753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13036869072501479748301835 19555303608752219622452753)
        ·
          refine ⟨14666477706564164716839565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19555303608752219622452753 14666477706564164716839565)
          ·
            refine ⟨5499929139961561768814837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14666477706564164716839565 5499929139961561768814837)
            ·
              refine ⟨515618356871396415826391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5499929139961561768814837 515618356871396415826391)
              ·
                refine ⟨773427535307094623739587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 515618356871396415826391 773427535307094623739587)
                ·
                  refine ⟨1160141302960641935609381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 773427535307094623739587 1160141302960641935609381)
                  ·
                    refine ⟨217526494305120362926759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1160141302960641935609381 217526494305120362926759)
                    ·
                      rfl

theorem cell22_635447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 5, 1, 1, 4].length) (baseStart_635447 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_635447 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_635447 prefixEnd_635447 := by exact prefixLift 635447
  have htrace : WordTrace (prefixWord ++ tailWord_635447) baseStart_635447 baseEnd_635447 := by
    simpa [prefixWord, tailWord_635447, baseEnd_635447] using wordTrace_append hprefix tailTrace_635447
  have hstable : (prefixWord ++ tailWord_635447).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_635447).length < 2 ^ (prefixWord ++ tailWord_635447).sum := by decide
  have hdescent : baseEnd_635447 < baseStart_635447 := by decide
  rcases family_descends (prefixWord ++ tailWord_635447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_635477 : List Nat := [1, 3, 2, 2, 1, 1, 4, 3, 2, 3]
def baseStart_635477 : Nat := 118140960795 + 635477 * 2 ^ 59
def prefixEnd_635477 : Nat := 4983230072969 + 3 ^ 40 * 635477 * 2
def baseEnd_635477 : Nat := 217536763918210284676667

theorem tailTrace_635477 : CollatzResearch.WordTrace tailWord_635477 prefixEnd_635477 217536763918210284676667 := by
  unfold tailWord_635477
  simp only [CollatzResearch.WordTrace]
  refine ⟨23177750318782834676128685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15451833545855223117419123 23177750318782834676128685)
  ·
    refine ⟨8691656369543563003548257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23177750318782834676128685 8691656369543563003548257)
    ·
      refine ⟨6518742277157672252661193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8691656369543563003548257 6518742277157672252661193)
      ·
        refine ⟨4889056707868254189495895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6518742277157672252661193 4889056707868254189495895)
        ·
          refine ⟨7333585061802381284243843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4889056707868254189495895 7333585061802381284243843)
          ·
            refine ⟨11000377592703571926365765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7333585061802381284243843 11000377592703571926365765)
            ·
              refine ⟨2062570798631919736193581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11000377592703571926365765 2062570798631919736193581)
              ·
                refine ⟨773464049486969901072593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2062570798631919736193581 773464049486969901072593)
                ·
                  refine ⟨580098037115227425804445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 773464049486969901072593 580098037115227425804445)
                  ·
                    refine ⟨217536763918210284676667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 580098037115227425804445 217536763918210284676667)
                    ·
                      rfl

theorem cell22_635477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 4, 3, 2, 3].length) (baseStart_635477 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_635477 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_635477 prefixEnd_635477 := by exact prefixLift 635477
  have htrace : WordTrace (prefixWord ++ tailWord_635477) baseStart_635477 baseEnd_635477 := by
    simpa [prefixWord, tailWord_635477, baseEnd_635477] using wordTrace_append hprefix tailTrace_635477
  have hstable : (prefixWord ++ tailWord_635477).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_635477).length < 2 ^ (prefixWord ++ tailWord_635477).sum := by decide
  have hdescent : baseEnd_635477 < baseStart_635477 := by decide
  rcases family_descends (prefixWord ++ tailWord_635477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_635573 : List Nat := [1, 3, 3, 3, 1, 2, 3, 2, 1, 3]
def baseStart_635573 : Nat := 118140960795 + 635573 * 2 ^ 59
def prefixEnd_635573 : Nat := 4983230072969 + 3 ^ 40 * 635573 * 2
def baseEnd_635573 : Nat := 217569626680098034276373

theorem tailTrace_635573 : CollatzResearch.WordTrace tailWord_635573 prefixEnd_635573 217569626680098034276373 := by
  unfold tailWord_635573
  simp only [CollatzResearch.WordTrace]
  refine ⟨23181251726435043071623373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15454167817623362047748915 23181251726435043071623373)
  ·
    refine ⟨8692969397413141151858765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23181251726435043071623373 8692969397413141151858765)
    ·
      refine ⟨3259863524029927931947037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8692969397413141151858765 3259863524029927931947037)
      ·
        refine ⟨1222448821511222974480139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3259863524029927931947037 1222448821511222974480139)
        ·
          refine ⟨1833673232266834461720209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1222448821511222974480139 1833673232266834461720209)
          ·
            refine ⟨1375254924200125846290157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1833673232266834461720209 1375254924200125846290157)
            ·
              refine ⟨515720596575047192358809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1375254924200125846290157 515720596575047192358809)
              ·
                refine ⟨386790447431285394269107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 515720596575047192358809 386790447431285394269107)
                ·
                  refine ⟨580185671146928091403661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 386790447431285394269107 580185671146928091403661)
                  ·
                    refine ⟨217569626680098034276373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 580185671146928091403661 217569626680098034276373)
                    ·
                      rfl

theorem cell22_635573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 3, 2, 1, 3].length) (baseStart_635573 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_635573 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_635573 prefixEnd_635573 := by exact prefixLift 635573
  have htrace : WordTrace (prefixWord ++ tailWord_635573) baseStart_635573 baseEnd_635573 := by
    simpa [prefixWord, tailWord_635573, baseEnd_635573] using wordTrace_append hprefix tailTrace_635573
  have hstable : (prefixWord ++ tailWord_635573).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_635573).length < 2 ^ (prefixWord ++ tailWord_635573).sum := by decide
  have hdescent : baseEnd_635573 < baseStart_635573 := by decide
  rcases family_descends (prefixWord ++ tailWord_635573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_635582 : List Nat := [4, 2, 1, 1, 2, 1, 2, 2, 3, 4]
def baseStart_635582 : Nat := 118140960795 + 635582 * 2 ^ 59
def prefixEnd_635582 : Nat := 4983230072969 + 3 ^ 40 * 635582 * 2
def baseEnd_635582 : Nat := 217572707564025010801345

theorem tailTrace_635582 : CollatzResearch.WordTrace tailWord_635582 prefixEnd_635582 217572707564025010801345 := by
  unfold tailWord_635582
  simp only [CollatzResearch.WordTrace]
  refine ⟨2897697497925304701087625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15454386655601625072467333 2897697497925304701087625)
  ·
    refine ⟨2173273123443978525815719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2897697497925304701087625 2173273123443978525815719)
    ·
      refine ⟨3259909685165967788723579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2173273123443978525815719 3259909685165967788723579)
      ·
        refine ⟨4889864527748951683085369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3259909685165967788723579 4889864527748951683085369)
        ·
          refine ⟨3667398395811713762314027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4889864527748951683085369 3667398395811713762314027)
          ·
            refine ⟨5501097593717570643471041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3667398395811713762314027 5501097593717570643471041)
            ·
              refine ⟨4125823195288177982603281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5501097593717570643471041 4125823195288177982603281)
              ·
                refine ⟨3094367396466133486952461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4125823195288177982603281 3094367396466133486952461)
                ·
                  refine ⟨1160387773674800057607173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3094367396466133486952461 1160387773674800057607173)
                  ·
                    refine ⟨217572707564025010801345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1160387773674800057607173 217572707564025010801345)
                    ·
                      rfl

theorem cell22_635582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 2, 2, 3, 4].length) (baseStart_635582 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_635582 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_635582 prefixEnd_635582 := by exact prefixLift 635582
  have htrace : WordTrace (prefixWord ++ tailWord_635582) baseStart_635582 baseEnd_635582 := by
    simpa [prefixWord, tailWord_635582, baseEnd_635582] using wordTrace_append hprefix tailTrace_635582
  have hstable : (prefixWord ++ tailWord_635582).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_635582).length < 2 ^ (prefixWord ++ tailWord_635582).sum := by decide
  have hdescent : baseEnd_635582 < baseStart_635582 := by decide
  rcases family_descends (prefixWord ++ tailWord_635582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_635631 : List Nat := [1, 1, 2, 1, 5, 4, 2, 2, 4]
def baseStart_635631 : Nat := 118140960795 + 635631 * 2 ^ 59
def prefixEnd_635631 : Nat := 4983230072969 + 3 ^ 40 * 635631 * 2
def baseEnd_635631 : Nat := 72529827088468405442065

theorem tailTrace_635631 : CollatzResearch.WordTrace tailWord_635631 prefixEnd_635631 72529827088468405442065 := by
  unfold tailWord_635631
  simp only [CollatzResearch.WordTrace]
  refine ⟨23183367160224918977234747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15455578106816612651489831 23183367160224918977234747)
  ·
    refine ⟨34775050740337378465852121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23183367160224918977234747 34775050740337378465852121)
    ·
      refine ⟨26081288055253033849389091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34775050740337378465852121 26081288055253033849389091)
      ·
        refine ⟨39121932082879550774083637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26081288055253033849389091 39121932082879550774083637)
        ·
          refine ⟨3667681132769957885070341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 39121932082879550774083637 3667681132769957885070341)
          ·
            refine ⟨687690212394367103450689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3667681132769957885070341 687690212394367103450689)
            ·
              refine ⟨515767659295775327588017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 687690212394367103450689 515767659295775327588017)
              ·
                refine ⟨386825744471831495691013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 515767659295775327588017 386825744471831495691013)
                ·
                  refine ⟨72529827088468405442065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 386825744471831495691013 72529827088468405442065)
                  ·
                    rfl

theorem cell22_635631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 4, 2, 2, 4].length) (baseStart_635631 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_635631 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_635631 prefixEnd_635631 := by exact prefixLift 635631
  have htrace : WordTrace (prefixWord ++ tailWord_635631) baseStart_635631 baseEnd_635631 := by
    simpa [prefixWord, tailWord_635631, baseEnd_635631] using wordTrace_append hprefix tailTrace_635631
  have hstable : (prefixWord ++ tailWord_635631).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_635631).length < 2 ^ (prefixWord ++ tailWord_635631).sum := by decide
  have hdescent : baseEnd_635631 < baseStart_635631 := by decide
  rcases family_descends (prefixWord ++ tailWord_635631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_635646 : List Nat := [4, 2, 2, 1, 2, 1, 2, 3, 2, 3]
def baseStart_635646 : Nat := 118140960795 + 635646 * 2 ^ 59
def prefixEnd_635646 : Nat := 4983230072969 + 3 ^ 40 * 635646 * 2
def baseEnd_635646 : Nat := 217594616071950177201149

theorem tailTrace_635646 : CollatzResearch.WordTrace tailWord_635646 prefixEnd_635646 217594616071950177201149 := by
  unfold tailWord_635646
  simp only [CollatzResearch.WordTrace]
  refine ⟨2897989281896322067378849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15455942836780384359353861 2897989281896322067378849)
  ·
    refine ⟨2173491961422241550534137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2897989281896322067378849 2173491961422241550534137)
    ·
      refine ⟨1630118971066681162900603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2173491961422241550534137 1630118971066681162900603)
      ·
        refine ⟨2445178456600021744350905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1630118971066681162900603 2445178456600021744350905)
        ·
          refine ⟨1833883842450016308263179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2445178456600021744350905 1833883842450016308263179)
          ·
            refine ⟨2750825763675024462394769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1833883842450016308263179 2750825763675024462394769)
            ·
              refine ⟨2063119322756268346796077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2750825763675024462394769 2063119322756268346796077)
              ·
                refine ⟨773669746033600630048529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2063119322756268346796077 773669746033600630048529)
                ·
                  refine ⟨580252309525200472536397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 773669746033600630048529 580252309525200472536397)
                  ·
                    refine ⟨217594616071950177201149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 580252309525200472536397 217594616071950177201149)
                    ·
                      rfl

theorem cell22_635646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 2, 3, 2, 3].length) (baseStart_635646 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_635646 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_635646 prefixEnd_635646 := by exact prefixLift 635646
  have htrace : WordTrace (prefixWord ++ tailWord_635646) baseStart_635646 baseEnd_635646 := by
    simpa [prefixWord, tailWord_635646, baseEnd_635646] using wordTrace_append hprefix tailTrace_635646
  have hstable : (prefixWord ++ tailWord_635646).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_635646).length < 2 ^ (prefixWord ++ tailWord_635646).sum := by decide
  have hdescent : baseEnd_635646 < baseStart_635646 := by decide
  rcases family_descends (prefixWord ++ tailWord_635646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_635657 : List Nat := [1, 2, 1, 1, 3, 2, 3, 1, 5, 3]
def baseStart_635657 : Nat := 118140960795 + 635657 * 2 ^ 59
def prefixEnd_635657 : Nat := 4983230072969 + 3 ^ 40 * 635657 * 2
def baseEnd_635657 : Nat := 217598381596749815176115

theorem tailTrace_635657 : CollatzResearch.WordTrace tailWord_635657 prefixEnd_635657 217598381596749815176115 := by
  unfold tailWord_635657
  simp only [CollatzResearch.WordTrace]
  refine ⟨23184315458130725417681225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15456210305420483611787483 23184315458130725417681225)
  ·
    refine ⟨17388236593598044063260919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23184315458130725417681225 17388236593598044063260919)
    ·
      refine ⟨26082354890397066094891379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17388236593598044063260919 26082354890397066094891379)
      ·
        refine ⟨39123532335595599142337069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26082354890397066094891379 39123532335595599142337069)
        ·
          refine ⟨14671324625848349678376401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39123532335595599142337069 14671324625848349678376401)
          ·
            refine ⟨11003493469386262258782301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14671324625848349678376401 11003493469386262258782301)
            ·
              refine ⟨4126310051019848347043363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11003493469386262258782301 4126310051019848347043363)
              ·
                refine ⟨6189465076529772520565045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4126310051019848347043363 6189465076529772520565045)
                ·
                  refine ⟨580262350924666173802973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 6189465076529772520565045 580262350924666173802973)
                  ·
                    refine ⟨217598381596749815176115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 580262350924666173802973 217598381596749815176115)
                    ·
                      rfl

theorem cell22_635657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 3, 1, 5, 3].length) (baseStart_635657 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_635657 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_635657 prefixEnd_635657 := by exact prefixLift 635657
  have htrace : WordTrace (prefixWord ++ tailWord_635657) baseStart_635657 baseEnd_635657 := by
    simpa [prefixWord, tailWord_635657, baseEnd_635657] using wordTrace_append hprefix tailTrace_635657
  have hstable : (prefixWord ++ tailWord_635657).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_635657).length < 2 ^ (prefixWord ++ tailWord_635657).sum := by decide
  have hdescent : baseEnd_635657 < baseStart_635657 := by decide
  rcases family_descends (prefixWord ++ tailWord_635657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_635704 : List Nat := [2, 1, 2, 1, 3, 2, 5, 1, 5]
def baseStart_635704 : Nat := 118140960795 + 635704 * 2 ^ 59
def prefixEnd_635704 : Nat := 4983230072969 + 3 ^ 40 * 635704 * 2
def baseEnd_635704 : Nat := 72538156885752453083657

theorem tailTrace_635704 : CollatzResearch.WordTrace tailWord_635704 prefixEnd_635704 72538156885752453083657 := by
  unfold tailWord_635704
  simp only [CollatzResearch.WordTrace]
  refine ⟨11593014844480226222321083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15457353125973634963094777 11593014844480226222321083)
  ·
    refine ⟨17389522266720339333481625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11593014844480226222321083 17389522266720339333481625)
    ·
      refine ⟨13042141700040254500111219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17389522266720339333481625 13042141700040254500111219)
      ·
        refine ⟨19563212550060381750166829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13042141700040254500111219 19563212550060381750166829)
        ·
          refine ⟨7336204706272643156312561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19563212550060381750166829 7336204706272643156312561)
          ·
            refine ⟨5502153529704482367234421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7336204706272643156312561 5502153529704482367234421)
            ·
              refine ⟨515826893409795221928227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5502153529704482367234421 515826893409795221928227)
              ·
                refine ⟨773740340114692832892341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 515826893409795221928227 773740340114692832892341)
                ·
                  refine ⟨72538156885752453083657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 773740340114692832892341 72538156885752453083657)
                  ·
                    rfl

theorem cell22_635704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 5, 1, 5].length) (baseStart_635704 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_635704 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_635704 prefixEnd_635704 := by exact prefixLift 635704
  have htrace : WordTrace (prefixWord ++ tailWord_635704) baseStart_635704 baseEnd_635704 := by
    simpa [prefixWord, tailWord_635704, baseEnd_635704] using wordTrace_append hprefix tailTrace_635704
  have hstable : (prefixWord ++ tailWord_635704).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_635704).length < 2 ^ (prefixWord ++ tailWord_635704).sum := by decide
  have hdescent : baseEnd_635704 < baseStart_635704 := by decide
  rcases family_descends (prefixWord ++ tailWord_635704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_635749 : List Nat := [1, 3, 1, 3, 1, 1, 2, 6, 4]
def baseStart_635749 : Nat := 118140960795 + 635749 * 2 ^ 59
def prefixEnd_635749 : Nat := 4983230072969 + 3 ^ 40 * 635749 * 2
def baseEnd_635749 : Nat := 72543291692297413958611

theorem tailTrace_635749 : CollatzResearch.WordTrace tailWord_635749 prefixEnd_635749 72543291692297413958611 := by
  unfold tailWord_635749
  simp only [CollatzResearch.WordTrace]
  refine ⟨23187670973797425130030301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15458447315864950086686867 23187670973797425130030301)
  ·
    refine ⟨8695376615174034423761363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23187670973797425130030301 8695376615174034423761363)
    ·
      refine ⟨13043064922761051635642045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8695376615174034423761363 13043064922761051635642045)
      ·
        refine ⟨4891149346035394363365767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13043064922761051635642045 4891149346035394363365767)
        ·
          refine ⟨7336724019053091545048651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4891149346035394363365767 7336724019053091545048651)
          ·
            refine ⟨11005086028579637317572977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7336724019053091545048651 11005086028579637317572977)
            ·
              refine ⟨8253814521434727988179733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11005086028579637317572977 8253814521434727988179733)
              ·
                refine ⟨386897555692252874445925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 8253814521434727988179733 386897555692252874445925)
                ·
                  refine ⟨72543291692297413958611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 386897555692252874445925 72543291692297413958611)
                  ·
                    rfl

theorem cell22_635749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 6, 4].length) (baseStart_635749 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_635749 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_635749 prefixEnd_635749 := by exact prefixLift 635749
  have htrace : WordTrace (prefixWord ++ tailWord_635749) baseStart_635749 baseEnd_635749 := by
    simpa [prefixWord, tailWord_635749, baseEnd_635749] using wordTrace_append hprefix tailTrace_635749
  have hstable : (prefixWord ++ tailWord_635749).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_635749).length < 2 ^ (prefixWord ++ tailWord_635749).sum := by decide
  have hdescent : baseEnd_635749 < baseStart_635749 := by decide
  rcases family_descends (prefixWord ++ tailWord_635749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_635762 : List Nat := [3, 2, 1, 2, 1, 1, 2, 1, 3, 6]
def baseStart_635762 : Nat := 118140960795 + 635762 * 2 ^ 59
def prefixEnd_635762 : Nat := 4983230072969 + 3 ^ 40 * 635762 * 2
def baseEnd_635762 : Nat := 217634325242564541300793

theorem tailTrace_635762 : CollatzResearch.WordTrace tailWord_635762 prefixEnd_635762 217634325242564541300793 := by
  unfold tailWord_635762
  simp only [CollatzResearch.WordTrace]
  refine ⟨5797036280687582087563385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15458763415166885566835693 5797036280687582087563385)
  ·
    refine ⟨4347777210515686565672539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5797036280687582087563385 4347777210515686565672539)
    ·
      refine ⟨6521665815773529848508809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4347777210515686565672539 6521665815773529848508809)
      ·
        refine ⟨4891249361830147386381607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6521665815773529848508809 4891249361830147386381607)
        ·
          refine ⟨7336874042745221079572411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4891249361830147386381607 7336874042745221079572411)
          ·
            refine ⟨11005311064117831619358617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7336874042745221079572411 11005311064117831619358617)
            ·
              refine ⟨8253983298088373714518963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11005311064117831619358617 8253983298088373714518963)
              ·
                refine ⟨12380974947132560571778445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8253983298088373714518963 12380974947132560571778445)
                ·
                  refine ⟨4642865605174710214416917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12380974947132560571778445 4642865605174710214416917)
                  ·
                    refine ⟨217634325242564541300793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4642865605174710214416917 217634325242564541300793)
                    ·
                      rfl

theorem cell22_635762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 1, 3, 6].length) (baseStart_635762 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_635762 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_635762 prefixEnd_635762 := by exact prefixLift 635762
  have htrace : WordTrace (prefixWord ++ tailWord_635762) baseStart_635762 baseEnd_635762 := by
    simpa [prefixWord, tailWord_635762, baseEnd_635762] using wordTrace_append hprefix tailTrace_635762
  have hstable : (prefixWord ++ tailWord_635762).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_635762).length < 2 ^ (prefixWord ++ tailWord_635762).sum := by decide
  have hdescent : baseEnd_635762 < baseStart_635762 := by decide
  rcases family_descends (prefixWord ++ tailWord_635762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_635779 : List Nat := [1, 1, 1, 3, 4, 1, 4, 1, 2, 4]
def baseStart_635779 : Nat := 118140960795 + 635779 * 2 ^ 59
def prefixEnd_635779 : Nat := 4983230072969 + 3 ^ 40 * 635779 * 2
def baseEnd_635779 : Nat := 217640144689982163625741

theorem tailTrace_635779 : CollatzResearch.WordTrace tailWord_635779 prefixEnd_635779 217640144689982163625741 := by
  unfold tailWord_635779
  simp only [CollatzResearch.WordTrace]
  refine ⟨23188765163688740253622391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15459176775792493502414927 23188765163688740253622391)
  ·
    refine ⟨34783147745533110380433587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23188765163688740253622391 34783147745533110380433587)
    ·
      refine ⟨52174721618299665570650381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34783147745533110380433587 52174721618299665570650381)
      ·
        refine ⟨19565520606862374588993893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52174721618299665570650381 19565520606862374588993893)
        ·
          refine ⟨3668535113786695235436355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19565520606862374588993893 3668535113786695235436355)
          ·
            refine ⟨5502802670680042853154533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3668535113786695235436355 5502802670680042853154533)
            ·
              refine ⟨1031775500752508034966475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5502802670680042853154533 1031775500752508034966475)
              ·
                refine ⟨1547663251128762052449713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1031775500752508034966475 1547663251128762052449713)
                ·
                  refine ⟨1160747438346571539337285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1547663251128762052449713 1160747438346571539337285)
                  ·
                    refine ⟨217640144689982163625741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1160747438346571539337285 217640144689982163625741)
                    ·
                      rfl

theorem cell22_635779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 4, 1, 2, 4].length) (baseStart_635779 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_635779 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_635779 prefixEnd_635779 := by exact prefixLift 635779
  have htrace : WordTrace (prefixWord ++ tailWord_635779) baseStart_635779 baseEnd_635779 := by
    simpa [prefixWord, tailWord_635779, baseEnd_635779] using wordTrace_append hprefix tailTrace_635779
  have hstable : (prefixWord ++ tailWord_635779).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_635779).length < 2 ^ (prefixWord ++ tailWord_635779).sum := by decide
  have hdescent : baseEnd_635779 < baseStart_635779 := by decide
  rcases family_descends (prefixWord ++ tailWord_635779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_635794 : List Nat := [3, 2, 3, 2, 2, 10]
def baseStart_635794 : Nat := 118140960795 + 635794 * 2 ^ 59
def prefixEnd_635794 : Nat := 4983230072969 + 3 ^ 40 * 635794 * 2
def baseEnd_635794 : Nat := 2686978759216384253095

theorem tailTrace_635794 : CollatzResearch.WordTrace tailWord_635794 prefixEnd_635794 2686978759216384253095 := by
  unfold tailWord_635794
  simp only [CollatzResearch.WordTrace]
  refine ⟨5797328064658599453854609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15459541505756265210278957 5797328064658599453854609)
  ·
    refine ⟨4347996048493949590390957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5797328064658599453854609 4347996048493949590390957)
    ·
      refine ⟨1630498518185231096396609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4347996048493949590390957 1630498518185231096396609)
      ·
        refine ⟨1222873888638923322297457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1630498518185231096396609 1222873888638923322297457)
        ·
          refine ⟨917155416479192491723093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1222873888638923322297457 917155416479192491723093)
          ·
            refine ⟨2686978759216384253095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 917155416479192491723093 2686978759216384253095)
            ·
              rfl

theorem cell22_635794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 10].length) (baseStart_635794 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_635794 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_635794 prefixEnd_635794 := by exact prefixLift 635794
  have htrace : WordTrace (prefixWord ++ tailWord_635794) baseStart_635794 baseEnd_635794 := by
    simpa [prefixWord, tailWord_635794, baseEnd_635794] using wordTrace_append hprefix tailTrace_635794
  have hstable : (prefixWord ++ tailWord_635794).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_635794).length < 2 ^ (prefixWord ++ tailWord_635794).sum := by decide
  have hdescent : baseEnd_635794 < baseStart_635794 := by decide
  rcases family_descends (prefixWord ++ tailWord_635794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_635828 : List Nat := [2, 5, 2, 1, 1, 2, 3, 6]
def baseStart_635828 : Nat := 118140960795 + 635828 * 2 ^ 59
def prefixEnd_635828 : Nat := 4983230072969 + 3 ^ 40 * 635828 * 2
def baseEnd_635828 : Nat := 24184102043484707683399

theorem tailTrace_635828 : CollatzResearch.WordTrace tailWord_635828 prefixEnd_635828 24184102043484707683399 := by
  unfold tailWord_635828
  simp only [CollatzResearch.WordTrace]
  refine ⟨11595276170255610811078069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15460368227007481081437425 11595276170255610811078069)
  ·
    refine ⟨1087057140961463513538569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 11595276170255610811078069 1087057140961463513538569)
    ·
      refine ⟨815292855721097635153927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1087057140961463513538569 815292855721097635153927)
      ·
        refine ⟨1222939283581646452730891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 815292855721097635153927 1222939283581646452730891)
        ·
          refine ⟨1834408925372469679096337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1222939283581646452730891 1834408925372469679096337)
          ·
            refine ⟨1375806694029352259322253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1834408925372469679096337 1375806694029352259322253)
            ·
              refine ⟨515927510261007097245845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1375806694029352259322253 515927510261007097245845)
              ·
                refine ⟨24184102043484707683399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 515927510261007097245845 24184102043484707683399)
                ·
                  rfl

theorem cell22_635828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 3, 6].length) (baseStart_635828 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_635828 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_635828 prefixEnd_635828 := by exact prefixLift 635828
  have htrace : WordTrace (prefixWord ++ tailWord_635828) baseStart_635828 baseEnd_635828 := by
    simpa [prefixWord, tailWord_635828, baseEnd_635828] using wordTrace_append hprefix tailTrace_635828
  have hstable : (prefixWord ++ tailWord_635828).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_635828).length < 2 ^ (prefixWord ++ tailWord_635828).sum := by decide
  have hdescent : baseEnd_635828 < baseStart_635828 := by decide
  rcases family_descends (prefixWord ++ tailWord_635828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_635830 : List Nat := [5, 1, 4, 1, 1, 1, 1, 1, 1, 6]
def baseStart_635830 : Nat := 118140960795 + 635830 * 2 ^ 59
def prefixEnd_635830 : Nat := 4983230072969 + 3 ^ 40 * 635830 * 2
def baseEnd_635830 : Nat := 217657603032235030600585

theorem tailTrace_635830 : CollatzResearch.WordTrace tailWord_635830 prefixEnd_635830 217657603032235030600585 := by
  unfold tailWord_635830
  simp only [CollatzResearch.WordTrace]
  refine ⟨1449414080406498497733059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 15460416857669317309152629 1449414080406498497733059)
  ·
    refine ⟨2174121120609747746599589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1449414080406498497733059 2174121120609747746599589)
    ·
      refine ⟨407647710114327702487423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2174121120609747746599589 407647710114327702487423)
      ·
        refine ⟨611471565171491553731135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 407647710114327702487423 611471565171491553731135)
        ·
          refine ⟨917207347757237330596703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 611471565171491553731135 917207347757237330596703)
          ·
            refine ⟨1375811021635855995895055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 917207347757237330596703 1375811021635855995895055)
            ·
              refine ⟨2063716532453783993842583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1375811021635855995895055 2063716532453783993842583)
              ·
                refine ⟨3095574798680675990763875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2063716532453783993842583 3095574798680675990763875)
                ·
                  refine ⟨4643362198021013986145813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3095574798680675990763875 4643362198021013986145813)
                  ·
                    refine ⟨217657603032235030600585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4643362198021013986145813 217657603032235030600585)
                    ·
                      rfl

theorem cell22_635830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 1, 1, 1, 6].length) (baseStart_635830 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_635830 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_635830 prefixEnd_635830 := by exact prefixLift 635830
  have htrace : WordTrace (prefixWord ++ tailWord_635830) baseStart_635830 baseEnd_635830 := by
    simpa [prefixWord, tailWord_635830, baseEnd_635830] using wordTrace_append hprefix tailTrace_635830
  have hstable : (prefixWord ++ tailWord_635830).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_635830).length < 2 ^ (prefixWord ++ tailWord_635830).sum := by decide
  have hdescent : baseEnd_635830 < baseStart_635830 := by decide
  rcases family_descends (prefixWord ++ tailWord_635830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_635854 : List Nat := [4, 1, 1, 1, 2, 3, 1, 2, 2, 5]
def baseStart_635854 : Nat := 118140960795 + 635854 * 2 ^ 59
def prefixEnd_635854 : Nat := 4983230072969 + 3 ^ 40 * 635854 * 2
def baseEnd_635854 : Nat := 217665818722706968000511

theorem tailTrace_635854 : CollatzResearch.WordTrace tailWord_635854 prefixEnd_635854 217665818722706968000511 := by
  unfold tailWord_635854
  simp only [CollatzResearch.WordTrace]
  refine ⟨2898937579802128507825327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15461000425611352041735077 2898937579802128507825327)
  ·
    refine ⟨4348406369703192761737991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2898937579802128507825327 4348406369703192761737991)
    ·
      refine ⟨6522609554554789142606987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4348406369703192761737991 6522609554554789142606987)
      ·
        refine ⟨9783914331832183713910481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6522609554554789142606987 9783914331832183713910481)
        ·
          refine ⟨7337935748874137785432861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9783914331832183713910481 7337935748874137785432861)
          ·
            refine ⟨2751725905827801669537323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7337935748874137785432861 2751725905827801669537323)
            ·
              refine ⟨4127588858741702504305985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2751725905827801669537323 4127588858741702504305985)
              ·
                refine ⟨3095691644056276878229489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4127588858741702504305985 3095691644056276878229489)
                ·
                  refine ⟨2321768733042207658672117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3095691644056276878229489 2321768733042207658672117)
                  ·
                    refine ⟨217665818722706968000511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2321768733042207658672117 217665818722706968000511)
                    ·
                      rfl

theorem cell22_635854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 1, 2, 2, 5].length) (baseStart_635854 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_635854 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_635854 prefixEnd_635854 := by exact prefixLift 635854
  have htrace : WordTrace (prefixWord ++ tailWord_635854) baseStart_635854 baseEnd_635854 := by
    simpa [prefixWord, tailWord_635854, baseEnd_635854] using wordTrace_append hprefix tailTrace_635854
  have hstable : (prefixWord ++ tailWord_635854).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_635854).length < 2 ^ (prefixWord ++ tailWord_635854).sum := by decide
  have hdescent : baseEnd_635854 < baseStart_635854 := by decide
  rcases family_descends (prefixWord ++ tailWord_635854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_635916 : List Nat := [2, 2, 1, 2, 3, 2, 2, 1, 4, 3]
def baseStart_635916 : Nat := 118140960795 + 635916 * 2 ^ 59
def prefixEnd_635916 : Nat := 4983230072969 + 3 ^ 40 * 635916 * 2
def baseEnd_635916 : Nat := 217687042589759472950321

theorem tailTrace_635916 : CollatzResearch.WordTrace tailWord_635916 prefixEnd_635916 217687042589759472950321 := by
  unfold tailWord_635916
  simp only [CollatzResearch.WordTrace]
  refine ⟨11596880982096206325679801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15462507976128275100906401 11596880982096206325679801)
  ·
    refine ⟨8697660736572154744259851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11596880982096206325679801 8697660736572154744259851)
    ·
      refine ⟨13046491104858232116389777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8697660736572154744259851 13046491104858232116389777)
      ·
        refine ⟨9784868328643674087292333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13046491104858232116389777 9784868328643674087292333)
        ·
          refine ⟨3669325623241377782734625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9784868328643674087292333 3669325623241377782734625)
          ·
            refine ⟨2751994217431033337050969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3669325623241377782734625 2751994217431033337050969)
            ·
              refine ⟨2063995663073275002788227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2751994217431033337050969 2063995663073275002788227)
              ·
                refine ⟨3095993494609912504182341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2063995663073275002788227 3095993494609912504182341)
                ·
                  refine ⟨580498780239358594534189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3095993494609912504182341 580498780239358594534189)
                  ·
                    refine ⟨217687042589759472950321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 580498780239358594534189 217687042589759472950321)
                    ·
                      rfl

theorem cell22_635916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 2, 1, 4, 3].length) (baseStart_635916 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_635916 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_635916 prefixEnd_635916 := by exact prefixLift 635916
  have htrace : WordTrace (prefixWord ++ tailWord_635916) baseStart_635916 baseEnd_635916 := by
    simpa [prefixWord, tailWord_635916, baseEnd_635916] using wordTrace_append hprefix tailTrace_635916
  have hstable : (prefixWord ++ tailWord_635916).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_635916).length < 2 ^ (prefixWord ++ tailWord_635916).sum := by decide
  have hdescent : baseEnd_635916 < baseStart_635916 := by decide
  rcases family_descends (prefixWord ++ tailWord_635916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_636025 : List Nat := [1, 2, 1, 3, 6, 1, 1, 2, 5]
def baseStart_636025 : Nat := 118140960795 + 636025 * 2 ^ 59
def prefixEnd_636025 : Nat := 4983230072969 + 3 ^ 40 * 636025 * 2
def baseEnd_636025 : Nat := 72574785172439840658329

theorem tailTrace_636025 : CollatzResearch.WordTrace tailWord_636025 prefixEnd_636025 72574785172439840658329 := by
  unfold tailWord_636025
  simp only [CollatzResearch.WordTrace]
  refine ⟨23197737520797524267077529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15465158347198349511385019 23197737520797524267077529)
  ·
    refine ⟨17398303140598143200308147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23197737520797524267077529 17398303140598143200308147)
    ·
      refine ⟨26097454710897214800462221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17398303140598143200308147 26097454710897214800462221)
      ·
        refine ⟨9786545516586455550173333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26097454710897214800462221 9786545516586455550173333)
        ·
          refine ⟨458744321089990103914375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 9786545516586455550173333 458744321089990103914375)
          ·
            refine ⟨688116481634985155871563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 458744321089990103914375 688116481634985155871563)
            ·
              refine ⟨1032174722452477733807345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 688116481634985155871563 1032174722452477733807345)
              ·
                refine ⟨774131041839358300355509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1032174722452477733807345 774131041839358300355509)
                ·
                  refine ⟨72574785172439840658329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 774131041839358300355509 72574785172439840658329)
                  ·
                    rfl

theorem cell22_636025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 6, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 6, 1, 1, 2, 5].length) (baseStart_636025 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_636025 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_636025 prefixEnd_636025 := by exact prefixLift 636025
  have htrace : WordTrace (prefixWord ++ tailWord_636025) baseStart_636025 baseEnd_636025 := by
    simpa [prefixWord, tailWord_636025, baseEnd_636025] using wordTrace_append hprefix tailTrace_636025
  have hstable : (prefixWord ++ tailWord_636025).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_636025).length < 2 ^ (prefixWord ++ tailWord_636025).sum := by decide
  have hdescent : baseEnd_636025 < baseStart_636025 := by decide
  rcases family_descends (prefixWord ++ tailWord_636025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_636036 : List Nat := [2, 3, 2, 1, 2, 2, 1, 3, 6]
def baseStart_636036 : Nat := 118140960795 + 636036 * 2 ^ 59
def prefixEnd_636036 : Nat := 4983230072969 + 3 ^ 40 * 636036 * 2
def baseEnd_636036 : Nat := 72576040347373053316651

theorem tailTrace_636036 : CollatzResearch.WordTrace tailWord_636036 prefixEnd_636036 72576040347373053316651 := by
  unfold tailWord_636036
  simp only [CollatzResearch.WordTrace]
  refine ⟨11599069361878836572863981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15465425815838448763818641 11599069361878836572863981)
  ·
    refine ⟨4349651010704563714823993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11599069361878836572863981 4349651010704563714823993)
    ·
      refine ⟨3262238258028422786117995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4349651010704563714823993 3262238258028422786117995)
      ·
        refine ⟨4893357387042634179176993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3262238258028422786117995 4893357387042634179176993)
        ·
          refine ⟨3670018040281975634382745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4893357387042634179176993 3670018040281975634382745)
          ·
            refine ⟨2752513530211481725787059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3670018040281975634382745 2752513530211481725787059)
            ·
              refine ⟨4128770295317222588680589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2752513530211481725787059 4128770295317222588680589)
              ·
                refine ⟨1548288860743958470755221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4128770295317222588680589 1548288860743958470755221)
                ·
                  refine ⟨72576040347373053316651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1548288860743958470755221 72576040347373053316651)
                  ·
                    rfl

theorem cell22_636036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 1, 3, 6].length) (baseStart_636036 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_636036 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_636036 prefixEnd_636036 := by exact prefixLift 636036
  have htrace : WordTrace (prefixWord ++ tailWord_636036) baseStart_636036 baseEnd_636036 := by
    simpa [prefixWord, tailWord_636036, baseEnd_636036] using wordTrace_append hprefix tailTrace_636036
  have hstable : (prefixWord ++ tailWord_636036).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_636036).length < 2 ^ (prefixWord ++ tailWord_636036).sum := by decide
  have hdescent : baseEnd_636036 < baseStart_636036 := by decide
  rcases family_descends (prefixWord ++ tailWord_636036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_636051 : List Nat := [1, 1, 1, 2, 1, 2, 7, 1, 1, 5]
def baseStart_636051 : Nat := 118140960795 + 636051 * 2 ^ 59
def prefixEnd_636051 : Nat := 4983230072969 + 3 ^ 40 * 636051 * 2
def baseEnd_636051 : Nat := 217733255848664120824907

theorem tailTrace_636051 : CollatzResearch.WordTrace tailWord_636051 prefixEnd_636051 217733255848664120824907 := by
  unfold tailWord_636051
  simp only [CollatzResearch.WordTrace]
  refine ⟨23198685818703330707524007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15465790545802220471682671 23198685818703330707524007)
  ·
    refine ⟨34798028728054996061286011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23198685818703330707524007 34798028728054996061286011)
    ·
      refine ⟨52197043092082494091929017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34798028728054996061286011 52197043092082494091929017)
      ·
        refine ⟨39147782319061870568946763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52197043092082494091929017 39147782319061870568946763)
        ·
          refine ⟨58721673478592805853420145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39147782319061870568946763 58721673478592805853420145)
          ·
            refine ⟨44041255108944604390065109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58721673478592805853420145 44041255108944604390065109)
            ·
              refine ⟨1032216916615889165392151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 44041255108944604390065109 1032216916615889165392151)
              ·
                refine ⟨1548325374923833748088227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1032216916615889165392151 1548325374923833748088227)
                ·
                  refine ⟨2322488062385750622132341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1548325374923833748088227 2322488062385750622132341)
                  ·
                    refine ⟨217733255848664120824907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2322488062385750622132341 217733255848664120824907)
                    ·
                      rfl

theorem cell22_636051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 7, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 7, 1, 1, 5].length) (baseStart_636051 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_636051 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_636051 prefixEnd_636051 := by exact prefixLift 636051
  have htrace : WordTrace (prefixWord ++ tailWord_636051) baseStart_636051 baseEnd_636051 := by
    simpa [prefixWord, tailWord_636051, baseEnd_636051] using wordTrace_append hprefix tailTrace_636051
  have hstable : (prefixWord ++ tailWord_636051).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_636051).length < 2 ^ (prefixWord ++ tailWord_636051).sum := by decide
  have hdescent : baseEnd_636051 < baseStart_636051 := by decide
  rcases family_descends (prefixWord ++ tailWord_636051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_636068 : List Nat := [2, 3, 1, 2, 3, 1, 1, 2, 4, 3]
def baseStart_636068 : Nat := 118140960795 + 636068 * 2 ^ 59
def prefixEnd_636068 : Nat := 4983230072969 + 3 ^ 40 * 636068 * 2
def baseEnd_636068 : Nat := 217739075296081743149855

theorem tailTrace_636068 : CollatzResearch.WordTrace tailWord_636068 prefixEnd_636068 217739075296081743149855 := by
  unfold tailWord_636068
  simp only [CollatzResearch.WordTrace]
  refine ⟨11599652929820871305446429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15466203906427828407261905 11599652929820871305446429)
  ·
    refine ⟨4349869848682826739542411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11599652929820871305446429 4349869848682826739542411)
    ·
      refine ⟨6524804773024240109313617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4349869848682826739542411 6524804773024240109313617)
      ·
        refine ⟨4893603579768180081985213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6524804773024240109313617 4893603579768180081985213)
        ·
          refine ⟨1835101342413067530744455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4893603579768180081985213 1835101342413067530744455)
          ·
            refine ⟨2752652013619601296116683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1835101342413067530744455 2752652013619601296116683)
            ·
              refine ⟨4128978020429401944175025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2752652013619601296116683 4128978020429401944175025)
              ·
                refine ⟨3096733515322051458131269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4128978020429401944175025 3096733515322051458131269)
                ·
                  refine ⟨580637534122884648399613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3096733515322051458131269 580637534122884648399613)
                  ·
                    refine ⟨217739075296081743149855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 580637534122884648399613 217739075296081743149855)
                    ·
                      rfl

theorem cell22_636068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 1, 2, 4, 3].length) (baseStart_636068 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_636068 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_636068 prefixEnd_636068 := by exact prefixLift 636068
  have htrace : WordTrace (prefixWord ++ tailWord_636068) baseStart_636068 baseEnd_636068 := by
    simpa [prefixWord, tailWord_636068, baseEnd_636068] using wordTrace_append hprefix tailTrace_636068
  have hstable : (prefixWord ++ tailWord_636068).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_636068).length < 2 ^ (prefixWord ++ tailWord_636068).sum := by decide
  have hdescent : baseEnd_636068 < baseStart_636068 := by decide
  rcases family_descends (prefixWord ++ tailWord_636068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_636081 : List Nat := [1, 2, 2, 5, 1, 1, 10]
def baseStart_636081 : Nat := 118140960795 + 636081 * 2 ^ 59
def prefixEnd_636081 : Nat := 4983230072969 + 3 ^ 40 * 636081 * 2
def baseEnd_636081 : Nat := 8064575017102001576845

theorem tailTrace_636081 : CollatzResearch.WordTrace tailWord_636081 prefixEnd_636081 8064575017102001576845 := by
  unfold tailWord_636081
  simp only [CollatzResearch.WordTrace]
  refine ⟨23199780008594645831116097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15466520005729763887410731 23199780008594645831116097)
  ·
    refine ⟨17399835006445984373337073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23199780008594645831116097 17399835006445984373337073)
    ·
      refine ⟨13049876254834488280002805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17399835006445984373337073 13049876254834488280002805)
      ·
        refine ⟨1223425898890733276250263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 13049876254834488280002805 1223425898890733276250263)
        ·
          refine ⟨1835138848336099914375395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1223425898890733276250263 1835138848336099914375395)
          ·
            refine ⟨2752708272504149871563093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1835138848336099914375395 2752708272504149871563093)
            ·
              refine ⟨8064575017102001576845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 2752708272504149871563093 8064575017102001576845)
              ·
                rfl

theorem cell22_636081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 10].length) (baseStart_636081 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_636081 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_636081 prefixEnd_636081 := by exact prefixLift 636081
  have htrace : WordTrace (prefixWord ++ tailWord_636081) baseStart_636081 baseEnd_636081 := by
    simpa [prefixWord, tailWord_636081, baseEnd_636081] using wordTrace_append hprefix tailTrace_636081
  have hstable : (prefixWord ++ tailWord_636081).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_636081).length < 2 ^ (prefixWord ++ tailWord_636081).sum := by decide
  have hdescent : baseEnd_636081 < baseStart_636081 := by decide
  rcases family_descends (prefixWord ++ tailWord_636081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_636147 : List Nat := [1, 1, 1, 2, 2, 5, 4, 2, 1, 3]
def baseStart_636147 : Nat := 118140960795 + 636147 * 2 ^ 59
def prefixEnd_636147 : Nat := 4983230072969 + 3 ^ 40 * 636147 * 2
def baseEnd_636147 : Nat := 217766118610551870424613

theorem tailTrace_636147 : CollatzResearch.WordTrace tailWord_636147 prefixEnd_636147 217766118610551870424613 := by
  unfold tailWord_636147
  simp only [CollatzResearch.WordTrace]
  refine ⟨23202187226355539103018695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15468124817570359402012463 23202187226355539103018695)
  ·
    refine ⟨34803280839533308654528043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23202187226355539103018695 34803280839533308654528043)
    ·
      refine ⟨52204921259299962981792065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34803280839533308654528043 52204921259299962981792065)
      ·
        refine ⟨39153690944474972236344049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52204921259299962981792065 39153690944474972236344049)
        ·
          refine ⟨29365268208356229177258037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39153690944474972236344049 29365268208356229177258037)
          ·
            refine ⟨2752993894533396485367941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 29365268208356229177258037 2752993894533396485367941)
            ·
              refine ⟨516186355225011841006489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2752993894533396485367941 516186355225011841006489)
              ·
                refine ⟨387139766418758880754867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 516186355225011841006489 387139766418758880754867)
                ·
                  refine ⟨580709649628138321132301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 387139766418758880754867 580709649628138321132301)
                  ·
                    refine ⟨217766118610551870424613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 580709649628138321132301 217766118610551870424613)
                    ·
                      rfl

theorem cell22_636147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 4, 2, 1, 3].length) (baseStart_636147 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_636147 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_636147 prefixEnd_636147 := by exact prefixLift 636147
  have htrace : WordTrace (prefixWord ++ tailWord_636147) baseStart_636147 baseEnd_636147 := by
    simpa [prefixWord, tailWord_636147, baseEnd_636147] using wordTrace_append hprefix tailTrace_636147
  have hstable : (prefixWord ++ tailWord_636147).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_636147).length < 2 ^ (prefixWord ++ tailWord_636147).sum := by decide
  have hdescent : baseEnd_636147 < baseStart_636147 := by decide
  rcases family_descends (prefixWord ++ tailWord_636147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_636158 : List Nat := [4, 2, 2, 1, 1, 2, 1, 1, 1, 7]
def baseStart_636158 : Nat := 118140960795 + 636158 * 2 ^ 59
def prefixEnd_636158 : Nat := 4983230072969 + 3 ^ 40 * 636158 * 2
def baseEnd_636158 : Nat := 217769884135351508399579

theorem tailTrace_636158 : CollatzResearch.WordTrace tailWord_636158 prefixEnd_636158 217769884135351508399579 := by
  unfold tailWord_636158
  simp only [CollatzResearch.WordTrace]
  refine ⟨2900323553664460997708641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15468392286210458654446085 2900323553664460997708641)
  ·
    refine ⟨2175242665248345748281481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2900323553664460997708641 2175242665248345748281481)
    ·
      refine ⟨1631431998936259311211111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2175242665248345748281481 1631431998936259311211111)
      ·
        refine ⟨2447147998404388966816667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1631431998936259311211111 2447147998404388966816667)
        ·
          refine ⟨3670721997606583450225001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2447147998404388966816667 3670721997606583450225001)
          ·
            refine ⟨2753041498204937587668751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3670721997606583450225001 2753041498204937587668751)
            ·
              refine ⟨4129562247307406381503127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2753041498204937587668751 4129562247307406381503127)
              ·
                refine ⟨6194343370961109572254691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4129562247307406381503127 6194343370961109572254691)
                ·
                  refine ⟨9291515056441664358382037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6194343370961109572254691 9291515056441664358382037)
                  ·
                    refine ⟨217769884135351508399579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 9291515056441664358382037 217769884135351508399579)
                    ·
                      rfl

theorem cell22_636158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 1, 1, 1, 7].length) (baseStart_636158 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_636158 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_636158 prefixEnd_636158 := by exact prefixLift 636158
  have htrace : WordTrace (prefixWord ++ tailWord_636158) baseStart_636158 baseEnd_636158 := by
    simpa [prefixWord, tailWord_636158, baseEnd_636158] using wordTrace_append hprefix tailTrace_636158
  have hstable : (prefixWord ++ tailWord_636158).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_636158).length < 2 ^ (prefixWord ++ tailWord_636158).sum := by decide
  have hdescent : baseEnd_636158 < baseStart_636158 := by decide
  rcases family_descends (prefixWord ++ tailWord_636158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_636171 : List Nat := [1, 1, 1, 1, 5, 3, 1, 1, 8]
def baseStart_636171 : Nat := 118140960795 + 636171 * 2 ^ 59
def prefixEnd_636171 : Nat := 4983230072969 + 3 ^ 40 * 636171 * 2
def baseEnd_636171 : Nat := 72591444767007935941513

theorem tailTrace_636171 : CollatzResearch.WordTrace tailWord_636171 prefixEnd_636171 72591444767007935941513 := by
  unfold tailWord_636171
  simp only [CollatzResearch.WordTrace]
  refine ⟨23203062578268591201892367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15468708385512394134594911 23203062578268591201892367)
  ·
    refine ⟨34804593867402886802838551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23203062578268591201892367 34804593867402886802838551)
    ·
      refine ⟨52206890801104330204257827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34804593867402886802838551 52206890801104330204257827)
      ·
        refine ⟨78310336201656495306386741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52206890801104330204257827 78310336201656495306386741)
        ·
          refine ⟨7341594018905296434973757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 78310336201656495306386741 7341594018905296434973757)
          ·
            refine ⟨2753097757089486163115159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7341594018905296434973757 2753097757089486163115159)
            ·
              refine ⟨4129646635634229244672739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2753097757089486163115159 4129646635634229244672739)
              ·
                refine ⟨6194469953451343867009109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4129646635634229244672739 6194469953451343867009109)
                ·
                  refine ⟨72591444767007935941513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 6194469953451343867009109 72591444767007935941513)
                  ·
                    rfl

theorem cell22_636171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 1, 1, 8].length) (baseStart_636171 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_636171 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_636171 prefixEnd_636171 := by exact prefixLift 636171
  have htrace : WordTrace (prefixWord ++ tailWord_636171) baseStart_636171 baseEnd_636171 := by
    simpa [prefixWord, tailWord_636171, baseEnd_636171] using wordTrace_append hprefix tailTrace_636171
  have hstable : (prefixWord ++ tailWord_636171).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_636171).length < 2 ^ (prefixWord ++ tailWord_636171).sum := by decide
  have hdescent : baseEnd_636171 < baseStart_636171 := by decide
  rcases family_descends (prefixWord ++ tailWord_636171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_636205 : List Nat := [1, 5, 3, 1, 1, 1, 1, 3, 6]
def baseStart_636205 : Nat := 118140960795 + 636205 * 2 ^ 59
def prefixEnd_636205 : Nat := 4983230072969 + 3 ^ 40 * 636205 * 2
def baseEnd_636205 : Nat := 72595324398619684158145

theorem tailTrace_636205 : CollatzResearch.WordTrace tailWord_636205 prefixEnd_636205 72595324398619684158145 := by
  unfold tailWord_636205
  simp only [CollatzResearch.WordTrace]
  refine ⟨23204302660145415008630069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15469535106763610005753379 23204302660145415008630069)
  ·
    refine ⟨2175403374388632657059069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 23204302660145415008630069 2175403374388632657059069)
    ·
      refine ⟨815776265395737246397151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2175403374388632657059069 815776265395737246397151)
      ·
        refine ⟨1223664398093605869595727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 815776265395737246397151 1223664398093605869595727)
        ·
          refine ⟨1835496597140408804393591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1223664398093605869595727 1835496597140408804393591)
          ·
            refine ⟨2753244895710613206590387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1835496597140408804393591 2753244895710613206590387)
            ·
              refine ⟨4129867343565919809885581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2753244895710613206590387 4129867343565919809885581)
              ·
                refine ⟨1548700253837219928707093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4129867343565919809885581 1548700253837219928707093)
                ·
                  refine ⟨72595324398619684158145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1548700253837219928707093 72595324398619684158145)
                  ·
                    rfl

theorem cell22_636205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 1, 3, 6].length) (baseStart_636205 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_636205 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_636205 prefixEnd_636205 := by exact prefixLift 636205
  have htrace : WordTrace (prefixWord ++ tailWord_636205) baseStart_636205 baseEnd_636205 := by
    simpa [prefixWord, tailWord_636205, baseEnd_636205] using wordTrace_append hprefix tailTrace_636205
  have hstable : (prefixWord ++ tailWord_636205).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_636205).length < 2 ^ (prefixWord ++ tailWord_636205).sum := by decide
  have hdescent : baseEnd_636205 < baseStart_636205 := by decide
  rcases family_descends (prefixWord ++ tailWord_636205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_636216 : List Nat := [2, 1, 2, 1, 3, 1, 1, 11]
def baseStart_636216 : Nat := 118140960795 + 636216 * 2 ^ 59
def prefixEnd_636216 : Nat := 4983230072969 + 3 ^ 40 * 636216 * 2
def baseEnd_636216 : Nat := 24198859857850965605489

theorem tailTrace_636216 : CollatzResearch.WordTrace tailWord_636216 prefixEnd_636216 24198859857850965605489 := by
  unfold tailWord_636216
  simp only [CollatzResearch.WordTrace]
  refine ⟨11602351931552781943640251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15469802575403709258187001 11602351931552781943640251)
  ·
    refine ⟨17403527897329172915460377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11602351931552781943640251 17403527897329172915460377)
    ·
      refine ⟨13052645922996879686595283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17403527897329172915460377 13052645922996879686595283)
      ·
        refine ⟨19578968884495319529892925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13052645922996879686595283 19578968884495319529892925)
        ·
          refine ⟨7342113331685744823709847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19578968884495319529892925 7342113331685744823709847)
          ·
            refine ⟨11013169997528617235564771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7342113331685744823709847 11013169997528617235564771)
            ·
              refine ⟨16519754996292925853347157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11013169997528617235564771 16519754996292925853347157)
              ·
                refine ⟨24198859857850965605489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 16519754996292925853347157 24198859857850965605489)
                ·
                  rfl

theorem cell22_636216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 11].length) (baseStart_636216 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_636216 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_636216 prefixEnd_636216 := by exact prefixLift 636216
  have htrace : WordTrace (prefixWord ++ tailWord_636216) baseStart_636216 baseEnd_636216 := by
    simpa [prefixWord, tailWord_636216, baseEnd_636216] using wordTrace_append hprefix tailTrace_636216
  have hstable : (prefixWord ++ tailWord_636216).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_636216).length < 2 ^ (prefixWord ++ tailWord_636216).sum := by decide
  have hdescent : baseEnd_636216 < baseStart_636216 := by decide
  rcases family_descends (prefixWord ++ tailWord_636216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_636220 : List Nat := [2, 2, 2, 2, 1, 5, 1, 1, 1, 5]
def baseStart_636220 : Nat := 118140960795 + 636220 * 2 ^ 59
def prefixEnd_636220 : Nat := 4983230072969 + 3 ^ 40 * 636220 * 2
def baseEnd_636220 : Nat := 217791108002404013349389

theorem tailTrace_636220 : CollatzResearch.WordTrace tailWord_636220 prefixEnd_636220 217791108002404013349389 := by
  unfold tailWord_636220
  simp only [CollatzResearch.WordTrace]
  refine ⟨11602424877545536285213057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15469899836727381713617409 11602424877545536285213057)
  ·
    refine ⟨8701818658159152213909793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11602424877545536285213057 8701818658159152213909793)
    ·
      refine ⟨6526363993619364160432345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8701818658159152213909793 6526363993619364160432345)
      ·
        refine ⟨4894772995214523120324259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6526363993619364160432345 4894772995214523120324259)
        ·
          refine ⟨7342159492821784680486389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4894772995214523120324259 7342159492821784680486389)
          ·
            refine ⟨688327452452042313795599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 7342159492821784680486389 688327452452042313795599)
            ·
              refine ⟨1032491178678063470693399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 688327452452042313795599 1032491178678063470693399)
              ·
                refine ⟨1548736768017095206040099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1032491178678063470693399 1548736768017095206040099)
                ·
                  refine ⟨2323105152025642809060149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1548736768017095206040099 2323105152025642809060149)
                  ·
                    refine ⟨217791108002404013349389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2323105152025642809060149 217791108002404013349389)
                    ·
                      rfl

theorem cell22_636220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 5, 1, 1, 1, 5].length) (baseStart_636220 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_636220 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_636220 prefixEnd_636220 := by exact prefixLift 636220
  have htrace : WordTrace (prefixWord ++ tailWord_636220) baseStart_636220 baseEnd_636220 := by
    simpa [prefixWord, tailWord_636220, baseEnd_636220] using wordTrace_append hprefix tailTrace_636220
  have hstable : (prefixWord ++ tailWord_636220).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_636220).length < 2 ^ (prefixWord ++ tailWord_636220).sum := by decide
  have hdescent : baseEnd_636220 < baseStart_636220 := by decide
  rcases family_descends (prefixWord ++ tailWord_636220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_636233 : List Nat := [1, 2, 1, 1, 2, 3, 6, 6]
def baseStart_636233 : Nat := 118140960795 + 636233 * 2 ^ 59
def prefixEnd_636233 : Nat := 4983230072969 + 3 ^ 40 * 636233 * 2
def baseEnd_636233 : Nat := 24199506463119590308261

theorem tailTrace_636233 : CollatzResearch.WordTrace tailWord_636233 prefixEnd_636233 24199506463119590308261 := by
  unfold tailWord_636233
  simp only [CollatzResearch.WordTrace]
  refine ⟨23205323904043975790649353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15470215936029317193766235 23205323904043975790649353)
  ·
    refine ⟨17403992928032981842987015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23205323904043975790649353 17403992928032981842987015)
    ·
      refine ⟨26105989392049472764480523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17403992928032981842987015 26105989392049472764480523)
      ·
        refine ⟨39158984088074209146720785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26105989392049472764480523 39158984088074209146720785)
        ·
          refine ⟨29369238066055656860040589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39158984088074209146720785 29369238066055656860040589)
          ·
            refine ⟨11013464274770871322515221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29369238066055656860040589 11013464274770871322515221)
            ·
              refine ⟨516256137879884593242901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 11013464274770871322515221 516256137879884593242901)
              ·
                refine ⟨24199506463119590308261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 516256137879884593242901 24199506463119590308261)
                ·
                  rfl

theorem cell22_636233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 6, 6].length) (baseStart_636233 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_636233 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_636233 prefixEnd_636233 := by exact prefixLift 636233
  have htrace : WordTrace (prefixWord ++ tailWord_636233) baseStart_636233 baseEnd_636233 := by
    simpa [prefixWord, tailWord_636233, baseEnd_636233] using wordTrace_append hprefix tailTrace_636233
  have hstable : (prefixWord ++ tailWord_636233).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_636233).length < 2 ^ (prefixWord ++ tailWord_636233).sum := by decide
  have hdescent : baseEnd_636233 < baseStart_636233 := by decide
  rcases family_descends (prefixWord ++ tailWord_636233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_636312 : List Nat := [2, 1, 2, 5, 2, 1, 2, 2, 5]
def baseStart_636312 : Nat := 118140960795 + 636312 * 2 ^ 59
def prefixEnd_636312 : Nat := 4983230072969 + 3 ^ 40 * 636312 * 2
def baseEnd_636312 : Nat := 72607533827515480016369

theorem tailTrace_636312 : CollatzResearch.WordTrace tailWord_636312 prefixEnd_636312 72607533827515480016369 := by
  unfold tailWord_636312
  simp only [CollatzResearch.WordTrace]
  refine ⟨11604102635378886141387595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15472136847171848188516793 11604102635378886141387595)
  ·
    refine ⟨17406153953068329212081393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11604102635378886141387595 17406153953068329212081393)
    ·
      refine ⟨13054615464801246909061045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17406153953068329212081393 13054615464801246909061045)
      ·
        refine ⟨1223870199825116897724473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 13054615464801246909061045 1223870199825116897724473)
        ·
          refine ⟨917902649868837673293355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1223870199825116897724473 917902649868837673293355)
          ·
            refine ⟨1376853974803256509940033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 917902649868837673293355 1376853974803256509940033)
            ·
              refine ⟨1032640481102442382455025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1376853974803256509940033 1032640481102442382455025)
              ·
                refine ⟨774480360826831786841269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1032640481102442382455025 774480360826831786841269)
                ·
                  refine ⟨72607533827515480016369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 774480360826831786841269 72607533827515480016369)
                  ·
                    rfl

theorem cell22_636312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 2, 2, 5].length) (baseStart_636312 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_636312 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_636312 prefixEnd_636312 := by exact prefixLift 636312
  have htrace : WordTrace (prefixWord ++ tailWord_636312) baseStart_636312 baseEnd_636312 := by
    simpa [prefixWord, tailWord_636312, baseEnd_636312] using wordTrace_append hprefix tailTrace_636312
  have hstable : (prefixWord ++ tailWord_636312).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_636312).length < 2 ^ (prefixWord ++ tailWord_636312).sum := by decide
  have hdescent : baseEnd_636312 < baseStart_636312 := by decide
  rcases family_descends (prefixWord ++ tailWord_636312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_636316 : List Nat := [2, 2, 3, 4, 1, 1, 1, 4, 1, 3]
def baseStart_636316 : Nat := 118140960795 + 636316 * 2 ^ 59
def prefixEnd_636316 : Nat := 4983230072969 + 3 ^ 40 * 636316 * 2
def baseEnd_636316 : Nat := 217823970764291762949095

theorem tailTrace_636316 : CollatzResearch.WordTrace tailWord_636316 prefixEnd_636316 217823970764291762949095 := by
  unfold tailWord_636316
  simp only [CollatzResearch.WordTrace]
  refine ⟨11604175581371640482960401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15472234108495520643947201 11604175581371640482960401)
  ·
    refine ⟨8703131686028730362220301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11604175581371640482960401 8703131686028730362220301)
    ·
      refine ⟨3263674382260773885832613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8703131686028730362220301 3263674382260773885832613)
      ·
        refine ⟨611938946673895103593615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3263674382260773885832613 611938946673895103593615)
        ·
          refine ⟨917908420010842655390423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 611938946673895103593615 917908420010842655390423)
          ·
            refine ⟨1376862630016263983085635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 917908420010842655390423 1376862630016263983085635)
            ·
              refine ⟨2065293945024395974628453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1376862630016263983085635 2065293945024395974628453)
              ·
                refine ⟨387242614692074245242835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2065293945024395974628453 387242614692074245242835)
                ·
                  refine ⟨580863922038111367864253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 387242614692074245242835 580863922038111367864253)
                  ·
                    refine ⟨217823970764291762949095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 580863922038111367864253 217823970764291762949095)
                    ·
                      rfl

theorem cell22_636316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 1, 4, 1, 3].length) (baseStart_636316 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_636316 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_636316 prefixEnd_636316 := by exact prefixLift 636316
  have htrace : WordTrace (prefixWord ++ tailWord_636316) baseStart_636316 baseEnd_636316 := by
    simpa [prefixWord, tailWord_636316, baseEnd_636316] using wordTrace_append hprefix tailTrace_636316
  have hstable : (prefixWord ++ tailWord_636316).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_636316).length < 2 ^ (prefixWord ++ tailWord_636316).sum := by decide
  have hdescent : baseEnd_636316 < baseStart_636316 := by decide
  rcases family_descends (prefixWord ++ tailWord_636316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_636323 : List Nat := [1, 1, 1, 4, 1, 3, 2, 3, 6]
def baseStart_636323 : Nat := 118140960795 + 636323 * 2 ^ 59
def prefixEnd_636323 : Nat := 4983230072969 + 3 ^ 40 * 636323 * 2
def baseEnd_636323 : Nat := 72608789002448692674691

theorem tailTrace_636323 : CollatzResearch.WordTrace tailWord_636323 prefixEnd_636323 72608789002448692674691 := by
  unfold tailWord_636323
  simp only [CollatzResearch.WordTrace]
  refine ⟨23208606473717921161425623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15472404315811947440950415 23208606473717921161425623)
  ·
    refine ⟨34812909710576881742138435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23208606473717921161425623 34812909710576881742138435)
    ·
      refine ⟨52219364565865322613207653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34812909710576881742138435 52219364565865322613207653)
      ·
        refine ⟨9791130856099747989976435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 52219364565865322613207653 9791130856099747989976435)
        ·
          refine ⟨14686696284149621984964653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9791130856099747989976435 14686696284149621984964653)
          ·
            refine ⟨5507511106556108244361745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14686696284149621984964653 5507511106556108244361745)
            ·
              refine ⟨4130633329917081183271309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5507511106556108244361745 4130633329917081183271309)
              ·
                refine ⟨1548987498718905443726741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4130633329917081183271309 1548987498718905443726741)
                ·
                  refine ⟨72608789002448692674691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1548987498718905443726741 72608789002448692674691)
                  ·
                    rfl

theorem cell22_636323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 2, 3, 6].length) (baseStart_636323 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_636323 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_636323 prefixEnd_636323 := by exact prefixLift 636323
  have htrace : WordTrace (prefixWord ++ tailWord_636323) baseStart_636323 baseEnd_636323 := by
    simpa [prefixWord, tailWord_636323, baseEnd_636323] using wordTrace_append hprefix tailTrace_636323
  have hstable : (prefixWord ++ tailWord_636323).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_636323).length < 2 ^ (prefixWord ++ tailWord_636323).sum := by decide
  have hdescent : baseEnd_636323 < baseStart_636323 := by decide
  rcases family_descends (prefixWord ++ tailWord_636323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_636374 : List Nat := [5, 2, 1, 1, 1, 2, 2, 4, 4]
def baseStart_636374 : Nat := 118140960795 + 636374 * 2 ^ 59
def prefixEnd_636374 : Nat := 4983230072969 + 3 ^ 40 * 636374 * 2
def baseEnd_636374 : Nat := 72614608449866314999639

theorem tailTrace_636374 : CollatzResearch.WordTrace tailWord_636374 prefixEnd_636374 72614608449866314999639 := by
  unfold tailWord_636374
  simp only [CollatzResearch.WordTrace]
  refine ⟨1450654162283322304470761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 15473644397688771247688117 1450654162283322304470761)
  ·
    refine ⟨1087990621712491728353071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1450654162283322304470761 1087990621712491728353071)
    ·
      refine ⟨1631985932568737592529607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1087990621712491728353071 1631985932568737592529607)
      ·
        refine ⟨2447978898853106388794411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1631985932568737592529607 2447978898853106388794411)
        ·
          refine ⟨3671968348279659583191617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2447978898853106388794411 3671968348279659583191617)
          ·
            refine ⟨2753976261209744687393713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3671968348279659583191617 2753976261209744687393713)
            ·
              refine ⟨2065482195907308515545285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2753976261209744687393713 2065482195907308515545285)
              ·
                refine ⟨387277911732620346664741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2065482195907308515545285 387277911732620346664741)
                ·
                  refine ⟨72614608449866314999639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 387277911732620346664741 72614608449866314999639)
                  ·
                    rfl

theorem cell22_636374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 2, 4, 4].length) (baseStart_636374 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_636374 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_636374 prefixEnd_636374 := by exact prefixLift 636374
  have htrace : WordTrace (prefixWord ++ tailWord_636374) baseStart_636374 baseEnd_636374 := by
    simpa [prefixWord, tailWord_636374, baseEnd_636374] using wordTrace_append hprefix tailTrace_636374
  have hstable : (prefixWord ++ tailWord_636374).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_636374).length < 2 ^ (prefixWord ++ tailWord_636374).sum := by decide
  have hdescent : baseEnd_636374 < baseStart_636374 := by decide
  rcases family_descends (prefixWord ++ tailWord_636374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_636402 : List Nat := [3, 2, 1, 4, 1, 1, 4, 6]
def baseStart_636402 : Nat := 118140960795 + 636402 * 2 ^ 59
def prefixEnd_636402 : Nat := 4983230072969 + 3 ^ 40 * 636402 * 2
def baseEnd_636402 : Nat := 24205934480201800588759

theorem tailTrace_636402 : CollatzResearch.WordTrace tailWord_636402 prefixEnd_636402 24205934480201800588759 := by
  unfold tailWord_636402
  simp only [CollatzResearch.WordTrace]
  refine ⟨5802871960107929413387865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15474325226954478435700973 5802871960107929413387865)
  ·
    refine ⟨4352153970080947060040899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5802871960107929413387865 4352153970080947060040899)
    ·
      refine ⟨6528230955121420590061349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4352153970080947060040899 6528230955121420590061349)
      ·
        refine ⟨1224043304085266360636503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6528230955121420590061349 1224043304085266360636503)
        ·
          refine ⟨1836064956127899540954755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1224043304085266360636503 1836064956127899540954755)
          ·
            refine ⟨2754097434191849311432133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1836064956127899540954755 2754097434191849311432133)
            ·
              refine ⟨516393268910971745893525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2754097434191849311432133 516393268910971745893525)
              ·
                refine ⟨24205934480201800588759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 516393268910971745893525 24205934480201800588759)
                ·
                  rfl

theorem cell22_636402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 4, 6].length) (baseStart_636402 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_636402 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_636402 prefixEnd_636402 := by exact prefixLift 636402
  have htrace : WordTrace (prefixWord ++ tailWord_636402) baseStart_636402 baseEnd_636402 := by
    simpa [prefixWord, tailWord_636402, baseEnd_636402] using wordTrace_append hprefix tailTrace_636402
  have hstable : (prefixWord ++ tailWord_636402).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_636402).length < 2 ^ (prefixWord ++ tailWord_636402).sum := by decide
  have hdescent : baseEnd_636402 < baseStart_636402 := by decide
  rcases family_descends (prefixWord ++ tailWord_636402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_636445 : List Nat := [1, 4, 2, 2, 1, 1, 2, 1, 1, 7]
def baseStart_636445 : Nat := 118140960795 + 636445 * 2 ^ 59
def prefixEnd_636445 : Nat := 4983230072969 + 3 ^ 40 * 636445 * 2
def baseEnd_636445 : Nat := 217868130100578426473699

theorem tailTrace_636445 : CollatzResearch.WordTrace tailWord_636445 prefixEnd_636445 217868130100578426473699 := by
  unfold tailWord_636445
  simp only [CollatzResearch.WordTrace]
  refine ⟨23213056179275935997366789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15475370786183957331577859 23213056179275935997366789)
  ·
    refine ⟨4352448033614237999506273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23213056179275935997366789 4352448033614237999506273)
    ·
      refine ⟨3264336025210678499629705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4352448033614237999506273 3264336025210678499629705)
      ·
        refine ⟨2448252018908008874722279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3264336025210678499629705 2448252018908008874722279)
        ·
          refine ⟨3672378028362013312083419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2448252018908008874722279 3672378028362013312083419)
          ·
            refine ⟨5508567042543019968125129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3672378028362013312083419 5508567042543019968125129)
            ·
              refine ⟨4131425281907264976093847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5508567042543019968125129 4131425281907264976093847)
              ·
                refine ⟨6197137922860897464140771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4131425281907264976093847 6197137922860897464140771)
                ·
                  refine ⟨9295706884291346196211157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6197137922860897464140771 9295706884291346196211157)
                  ·
                    refine ⟨217868130100578426473699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 9295706884291346196211157 217868130100578426473699)
                    ·
                      rfl

theorem cell22_636445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 2, 1, 1, 7].length) (baseStart_636445 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_636445 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_636445 prefixEnd_636445 := by exact prefixLift 636445
  have htrace : WordTrace (prefixWord ++ tailWord_636445) baseStart_636445 baseEnd_636445 := by
    simpa [prefixWord, tailWord_636445, baseEnd_636445] using wordTrace_append hprefix tailTrace_636445
  have hstable : (prefixWord ++ tailWord_636445).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_636445).length < 2 ^ (prefixWord ++ tailWord_636445).sum := by decide
  have hdescent : baseEnd_636445 < baseStart_636445 := by decide
  rcases family_descends (prefixWord ++ tailWord_636445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_636447 : List Nat := [1, 1, 2, 4, 1, 1, 6, 1, 5]
def baseStart_636447 : Nat := 118140960795 + 636447 * 2 ^ 59
def prefixEnd_636447 : Nat := 4983230072969 + 3 ^ 40 * 636447 * 2
def baseEnd_636447 : Nat := 72622938247150362641231

theorem tailTrace_636447 : CollatzResearch.WordTrace tailWord_636447 prefixEnd_636447 72622938247150362641231 := by
  unfold tailWord_636447
  simp only [CollatzResearch.WordTrace]
  refine ⟨23213129125268690338939595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15475419416845793559293063 23213129125268690338939595)
  ·
    refine ⟨34819693687903035508409393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23213129125268690338939595 34819693687903035508409393)
    ·
      refine ⟨26114770265927276631307045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34819693687903035508409393 26114770265927276631307045)
      ·
        refine ⟨4896519424861364368370071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26114770265927276631307045 4896519424861364368370071)
        ·
          refine ⟨7344779137292046552555107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4896519424861364368370071 7344779137292046552555107)
          ·
            refine ⟨11017168705938069828832661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7344779137292046552555107 11017168705938069828832661)
            ·
              refine ⟨516429783090847023226531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 11017168705938069828832661 516429783090847023226531)
              ·
                refine ⟨774644674636270534839797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 516429783090847023226531 774644674636270534839797)
                ·
                  refine ⟨72622938247150362641231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 774644674636270534839797 72622938247150362641231)
                  ·
                    rfl

theorem cell22_636447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 6, 1, 5].length) (baseStart_636447 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_636447 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_636447 prefixEnd_636447 := by exact prefixLift 636447
  have htrace : WordTrace (prefixWord ++ tailWord_636447) baseStart_636447 baseEnd_636447 := by
    simpa [prefixWord, tailWord_636447, baseEnd_636447] using wordTrace_append hprefix tailTrace_636447
  have hstable : (prefixWord ++ tailWord_636447).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_636447).length < 2 ^ (prefixWord ++ tailWord_636447).sum := by decide
  have hdescent : baseEnd_636447 < baseStart_636447 := by decide
  rcases family_descends (prefixWord ++ tailWord_636447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_636490 : List Nat := [3, 1, 2, 1, 1, 3, 1, 2, 3, 5]
def baseStart_636490 : Nat := 118140960795 + 636490 * 2 ^ 59
def prefixEnd_636490 : Nat := 4983230072969 + 3 ^ 40 * 636490 * 2
def baseEnd_636490 : Nat := 217883534520213309098561

theorem tailTrace_636490 : CollatzResearch.WordTrace tailWord_636490 prefixEnd_636490 217883534520213309098561 := by
  unfold tailWord_636490
  simp only [CollatzResearch.WordTrace]
  refine ⟨5803674366028227170688731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15476464976075272455169949 5803674366028227170688731)
  ·
    refine ⟨8705511549042340756033097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5803674366028227170688731 8705511549042340756033097)
    ·
      refine ⟨6529133661781755567024823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8705511549042340756033097 6529133661781755567024823)
      ·
        refine ⟨9793700492672633350537235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6529133661781755567024823 9793700492672633350537235)
        ·
          refine ⟨14690550739008950025805853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9793700492672633350537235 14690550739008950025805853)
          ·
            refine ⟨5508956527128356259677195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14690550739008950025805853 5508956527128356259677195)
            ·
              refine ⟨8263434790692534389515793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5508956527128356259677195 8263434790692534389515793)
              ·
                refine ⟨6197576093019400792136845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8263434790692534389515793 6197576093019400792136845)
                ·
                  refine ⟨2324091034882275297051317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6197576093019400792136845 2324091034882275297051317)
                  ·
                    refine ⟨217883534520213309098561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2324091034882275297051317 217883534520213309098561)
                    ·
                      rfl

theorem cell22_636490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 2, 3, 5].length) (baseStart_636490 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_636490 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_636490 prefixEnd_636490 := by exact prefixLift 636490
  have htrace : WordTrace (prefixWord ++ tailWord_636490) baseStart_636490 baseEnd_636490 := by
    simpa [prefixWord, tailWord_636490, baseEnd_636490] using wordTrace_append hprefix tailTrace_636490
  have hstable : (prefixWord ++ tailWord_636490).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_636490).length < 2 ^ (prefixWord ++ tailWord_636490).sum := by decide
  have hdescent : baseEnd_636490 < baseStart_636490 := by decide
  rcases family_descends (prefixWord ++ tailWord_636490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_636505 : List Nat := [1, 2, 1, 2, 2, 1, 1, 4, 4, 4]
def baseStart_636505 : Nat := 118140960795 + 636505 * 2 ^ 59
def prefixEnd_636505 : Nat := 4983230072969 + 3 ^ 40 * 636505 * 2
def baseEnd_636505 : Nat := 217888669326758269973515

theorem tailTrace_636505 : CollatzResearch.WordTrace tailWord_636505 prefixEnd_636505 217888669326758269973515 := by
  unfold tailWord_636505
  simp only [CollatzResearch.WordTrace]
  refine ⟨23215244559058566244550969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15476829706039044163033979 23215244559058566244550969)
  ·
    refine ⟨17411433419293924683413227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23215244559058566244550969 17411433419293924683413227)
    ·
      refine ⟨26117150128940887025119841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17411433419293924683413227 26117150128940887025119841)
      ·
        refine ⟨19587862596705665268839881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26117150128940887025119841 19587862596705665268839881)
        ·
          refine ⟨14690896947529248951629911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19587862596705665268839881 14690896947529248951629911)
          ·
            refine ⟨22036345421293873427444867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14690896947529248951629911 22036345421293873427444867)
            ·
              refine ⟨33054518131940810141167301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22036345421293873427444867 33054518131940810141167301)
              ·
                refine ⟨6197722149738901901468869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33054518131940810141167301 6197722149738901901468869)
                ·
                  refine ⟨1162072903076044106525413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6197722149738901901468869 1162072903076044106525413)
                  ·
                    refine ⟨217888669326758269973515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1162072903076044106525413 217888669326758269973515)
                    ·
                      rfl

theorem cell22_636505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 4, 4, 4].length) (baseStart_636505 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_636505 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_636505 prefixEnd_636505 := by exact prefixLift 636505
  have htrace : WordTrace (prefixWord ++ tailWord_636505) baseStart_636505 baseEnd_636505 := by
    simpa [prefixWord, tailWord_636505, baseEnd_636505] using wordTrace_append hprefix tailTrace_636505
  have hstable : (prefixWord ++ tailWord_636505).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_636505).length < 2 ^ (prefixWord ++ tailWord_636505).sum := by decide
  have hdescent : baseEnd_636505 < baseStart_636505 := by decide
  rcases family_descends (prefixWord ++ tailWord_636505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_636522 : List Nat := [3, 1, 3, 2, 1, 3, 1, 1, 1, 6]
def baseStart_636522 : Nat := 118140960795 + 636522 * 2 ^ 59
def prefixEnd_636522 : Nat := 4983230072969 + 3 ^ 40 * 636522 * 2
def baseEnd_636522 : Nat := 217894488774175892298463

theorem tailTrace_636522 : CollatzResearch.WordTrace tailWord_636522 prefixEnd_636522 217894488774175892298463 := by
  unfold tailWord_636522
  simp only [CollatzResearch.WordTrace]
  refine ⟨5803966149999244536979955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15477243066664652098613213 5803966149999244536979955)
  ·
    refine ⟨8705949224998866805469933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5803966149999244536979955 8705949224998866805469933)
    ·
      refine ⟨3264730959374575052051225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8705949224998866805469933 3264730959374575052051225)
      ·
        refine ⟨2448548219530931289038419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3264730959374575052051225 2448548219530931289038419)
        ·
          refine ⟨3672822329296396933557629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2448548219530931289038419 3672822329296396933557629)
          ·
            refine ⟨1377308373486148850084111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3672822329296396933557629 1377308373486148850084111)
            ·
              refine ⟨2065962560229223275126167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1377308373486148850084111 2065962560229223275126167)
              ·
                refine ⟨3098943840343834912689251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2065962560229223275126167 3098943840343834912689251)
                ·
                  refine ⟨4648415760515752369033877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3098943840343834912689251 4648415760515752369033877)
                  ·
                    refine ⟨217894488774175892298463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4648415760515752369033877 217894488774175892298463)
                    ·
                      rfl

theorem cell22_636522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 1, 1, 1, 6].length) (baseStart_636522 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_636522 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_636522 prefixEnd_636522 := by exact prefixLift 636522
  have htrace : WordTrace (prefixWord ++ tailWord_636522) baseStart_636522 baseEnd_636522 := by
    simpa [prefixWord, tailWord_636522, baseEnd_636522] using wordTrace_append hprefix tailTrace_636522
  have hstable : (prefixWord ++ tailWord_636522).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_636522).length < 2 ^ (prefixWord ++ tailWord_636522).sum := by decide
  have hdescent : baseEnd_636522 < baseStart_636522 := by decide
  rcases family_descends (prefixWord ++ tailWord_636522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_636526 : List Nat := [4, 1, 2, 2, 3, 1, 2, 3, 4]
def baseStart_636526 : Nat := 118140960795 + 636526 * 2 ^ 59
def prefixEnd_636526 : Nat := 4983230072969 + 3 ^ 40 * 636526 * 2
def baseEnd_636526 : Nat := 72631952685307071732817

theorem tailTrace_636526 : CollatzResearch.WordTrace tailWord_636526 prefixEnd_636526 72631952685307071732817 := by
  unfold tailWord_636526
  simp only [CollatzResearch.WordTrace]
  refine ⟨2902001311497810853883179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15477340327988324554043621 2902001311497810853883179)
  ·
    refine ⟨4353001967246716280824769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2902001311497810853883179 4353001967246716280824769)
    ·
      refine ⟨3264751475435037210618577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4353001967246716280824769 3264751475435037210618577)
      ·
        refine ⟨2448563606576277907963933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3264751475435037210618577 2448563606576277907963933)
        ·
          refine ⟨918211352466104215486475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2448563606576277907963933 918211352466104215486475)
          ·
            refine ⟨1377317028699156323229713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 918211352466104215486475 1377317028699156323229713)
            ·
              refine ⟨1032987771524367242422285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1377317028699156323229713 1032987771524367242422285)
              ·
                refine ⟨387370414321637715908357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1032987771524367242422285 387370414321637715908357)
                ·
                  refine ⟨72631952685307071732817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 387370414321637715908357 72631952685307071732817)
                  ·
                    rfl

theorem cell22_636526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 2, 3, 4].length) (baseStart_636526 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_636526 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_636526 prefixEnd_636526 := by exact prefixLift 636526
  have htrace : WordTrace (prefixWord ++ tailWord_636526) baseStart_636526 baseEnd_636526 := by
    simpa [prefixWord, tailWord_636526, baseEnd_636526] using wordTrace_append hprefix tailTrace_636526
  have hstable : (prefixWord ++ tailWord_636526).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_636526).length < 2 ^ (prefixWord ++ tailWord_636526).sum := by decide
  have hdescent : baseEnd_636526 < baseStart_636526 := by decide
  rcases family_descends (prefixWord ++ tailWord_636526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_636541 : List Nat := [1, 4, 1, 1, 4, 3, 1, 2, 2, 3]
def baseStart_636541 : Nat := 118140960795 + 636541 * 2 ^ 59
def prefixEnd_636541 : Nat := 4983230072969 + 3 ^ 40 * 636541 * 2
def baseEnd_636541 : Nat := 217900992862466176073405

theorem tailTrace_636541 : CollatzResearch.WordTrace tailWord_636541 prefixEnd_636541 217900992862466176073405 := by
  unfold tailWord_636541
  simp only [CollatzResearch.WordTrace]
  refine ⟨23216557586928144392861477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15477705057952096261907651 23216557586928144392861477)
  ·
    refine ⟨4353104547549027073661527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23216557586928144392861477 4353104547549027073661527)
    ·
      refine ⟨6529656821323540610492291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4353104547549027073661527 6529656821323540610492291)
      ·
        refine ⟨9794485231985310915738437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6529656821323540610492291 9794485231985310915738437)
        ·
          refine ⟨1836465980997245796700957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9794485231985310915738437 1836465980997245796700957)
          ·
            refine ⟨688674742873967173762859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1836465980997245796700957 688674742873967173762859)
            ·
              refine ⟨1033012114310950760644289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 688674742873967173762859 1033012114310950760644289)
              ·
                refine ⟨774759085733213070483217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1033012114310950760644289 774759085733213070483217)
                ·
                  refine ⟨581069314299909802862413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 774759085733213070483217 581069314299909802862413)
                  ·
                    refine ⟨217900992862466176073405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 581069314299909802862413 217900992862466176073405)
                    ·
                      rfl

theorem cell22_636541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 3, 1, 2, 2, 3].length) (baseStart_636541 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_636541 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_636541 prefixEnd_636541 := by exact prefixLift 636541
  have htrace : WordTrace (prefixWord ++ tailWord_636541) baseStart_636541 baseEnd_636541 := by
    simpa [prefixWord, tailWord_636541, baseEnd_636541] using wordTrace_append hprefix tailTrace_636541
  have hstable : (prefixWord ++ tailWord_636541).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_636541).length < 2 ^ (prefixWord ++ tailWord_636541).sum := by decide
  have hdescent : baseEnd_636541 < baseStart_636541 := by decide
  rcases family_descends (prefixWord ++ tailWord_636541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_636644 : List Nat := [2, 3, 1, 1, 1, 3, 2, 5, 4]
def baseStart_636644 : Nat := 118140960795 + 636644 * 2 ^ 59
def prefixEnd_636644 : Nat := 4983230072969 + 3 ^ 40 * 636644 * 2
def baseEnd_636644 : Nat := 72645417289136080249363

theorem tailTrace_636644 : CollatzResearch.WordTrace tailWord_636644 prefixEnd_636644 72645417289136080249363 := by
  unfold tailWord_636644
  simp only [CollatzResearch.WordTrace]
  refine ⟨11610157152777496491930493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15480209537036661989240657 11610157152777496491930493)
  ·
    refine ⟨4353808932291561184473935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11610157152777496491930493 4353808932291561184473935)
    ·
      refine ⟨6530713398437341776710903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4353808932291561184473935 6530713398437341776710903)
      ·
        refine ⟨9796070097656012665066355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6530713398437341776710903 9796070097656012665066355)
        ·
          refine ⟨14694105146484018997599533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9796070097656012665066355 14694105146484018997599533)
          ·
            refine ⟨5510289429931507124099825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14694105146484018997599533 5510289429931507124099825)
            ·
              refine ⟨4132717072448630343074869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5510289429931507124099825 4132717072448630343074869)
              ·
                refine ⟨387442225542059094663269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4132717072448630343074869 387442225542059094663269)
                ·
                  refine ⟨72645417289136080249363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 387442225542059094663269 72645417289136080249363)
                  ·
                    rfl

theorem cell22_636644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 2, 5, 4].length) (baseStart_636644 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_636644 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_636644 prefixEnd_636644 := by exact prefixLift 636644
  have htrace : WordTrace (prefixWord ++ tailWord_636644) baseStart_636644 baseEnd_636644 := by
    simpa [prefixWord, tailWord_636644, baseEnd_636644] using wordTrace_append hprefix tailTrace_636644
  have hstable : (prefixWord ++ tailWord_636644).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_636644).length < 2 ^ (prefixWord ++ tailWord_636644).sum := by decide
  have hdescent : baseEnd_636644 < baseStart_636644 := by decide
  rcases family_descends (prefixWord ++ tailWord_636644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_636659 : List Nat := [1, 1, 1, 2, 2, 3, 3, 4, 2, 3]
def baseStart_636659 : Nat := 118140960795 + 636659 * 2 ^ 59
def prefixEnd_636659 : Nat := 4983230072969 + 3 ^ 40 * 636659 * 2
def baseEnd_636659 : Nat := 217941386673953201623043

theorem tailTrace_636659 : CollatzResearch.WordTrace tailWord_636659 prefixEnd_636659 217941386673953201623043 := by
  unfold tailWord_636659
  simp only [CollatzResearch.WordTrace]
  refine ⟨23220861400500650545657031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15480574267000433697104687 23220861400500650545657031)
  ·
    refine ⟨34831292100750975818485547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23220861400500650545657031 34831292100750975818485547)
    ·
      refine ⟨52246938151126463727728321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34831292100750975818485547 52246938151126463727728321)
      ·
        refine ⟨39185203613344847795796241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52246938151126463727728321 39185203613344847795796241)
        ·
          refine ⟨29388902710008635846847181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39185203613344847795796241 29388902710008635846847181)
          ·
            refine ⟨11020838516253238442567693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29388902710008635846847181 11020838516253238442567693)
            ·
              refine ⟨4132814443594964415962885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11020838516253238442567693 4132814443594964415962885)
              ·
                refine ⟨774902708174055827993041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4132814443594964415962885 774902708174055827993041)
                ·
                  refine ⟨581177031130541870994781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 774902708174055827993041 581177031130541870994781)
                  ·
                    refine ⟨217941386673953201623043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 581177031130541870994781 217941386673953201623043)
                    ·
                      rfl

theorem cell22_636659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 3, 4, 2, 3].length) (baseStart_636659 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_636659 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_636659 prefixEnd_636659 := by exact prefixLift 636659
  have htrace : WordTrace (prefixWord ++ tailWord_636659) baseStart_636659 baseEnd_636659 := by
    simpa [prefixWord, tailWord_636659, baseEnd_636659] using wordTrace_append hprefix tailTrace_636659
  have hstable : (prefixWord ++ tailWord_636659).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_636659).length < 2 ^ (prefixWord ++ tailWord_636659).sum := by decide
  have hdescent : baseEnd_636659 < baseStart_636659 := by decide
  rcases family_descends (prefixWord ++ tailWord_636659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_636674 : List Nat := [3, 4, 1, 1, 1, 1, 2, 2, 1, 6]
def baseStart_636674 : Nat := 118140960795 + 636674 * 2 ^ 59
def prefixEnd_636674 : Nat := 4983230072969 + 3 ^ 40 * 636674 * 2
def baseEnd_636674 : Nat := 217946521480498162497997

theorem tailTrace_636674 : CollatzResearch.WordTrace tailWord_636674 prefixEnd_636674 217946521480498162497997 := by
  unfold tailWord_636674
  simp only [CollatzResearch.WordTrace]
  refine ⟨5805352123861577026863269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15480938996964205404968717 5805352123861577026863269)
  ·
    refine ⟨1088503523224045692536863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5805352123861577026863269 1088503523224045692536863)
    ·
      refine ⟨1632755284836068538805295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1088503523224045692536863 1632755284836068538805295)
      ·
        refine ⟨2449132927254102808207943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1632755284836068538805295 2449132927254102808207943)
        ·
          refine ⟨3673699390881154212311915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2449132927254102808207943 3673699390881154212311915)
          ·
            refine ⟨5510549086321731318467873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3673699390881154212311915 5510549086321731318467873)
            ·
              refine ⟨4132911814741298488850905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5510549086321731318467873 4132911814741298488850905)
              ·
                refine ⟨3099683861055973866638179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4132911814741298488850905 3099683861055973866638179)
                ·
                  refine ⟨4649525791583960799957269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3099683861055973866638179 4649525791583960799957269)
                  ·
                    refine ⟨217946521480498162497997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4649525791583960799957269 217946521480498162497997)
                    ·
                      rfl

theorem cell22_636674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 2, 2, 1, 6].length) (baseStart_636674 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_636674 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_636674 prefixEnd_636674 := by exact prefixLift 636674
  have htrace : WordTrace (prefixWord ++ tailWord_636674) baseStart_636674 baseEnd_636674 := by
    simpa [prefixWord, tailWord_636674, baseEnd_636674] using wordTrace_append hprefix tailTrace_636674
  have hstable : (prefixWord ++ tailWord_636674).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_636674).length < 2 ^ (prefixWord ++ tailWord_636674).sum := by decide
  have hdescent : baseEnd_636674 < baseStart_636674 := by decide
  rcases family_descends (prefixWord ++ tailWord_636674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_636676 : List Nat := [2, 3, 2, 2, 1, 2, 2, 3, 2, 3]
def baseStart_636676 : Nat := 118140960795 + 636676 * 2 ^ 59
def prefixEnd_636676 : Nat := 4983230072969 + 3 ^ 40 * 636676 * 2
def baseEnd_636676 : Nat := 217947206121370823947991

theorem tailTrace_636676 : CollatzResearch.WordTrace tailWord_636676 prefixEnd_636676 217947206121370823947991 := by
  unfold tailWord_636676
  simp only [CollatzResearch.WordTrace]
  refine ⟨11610740720719531224512941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15480987627626041632683921 11610740720719531224512941)
  ·
    refine ⟨4354027770269824209192353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11610740720719531224512941 4354027770269824209192353)
    ·
      refine ⟨3265520827702368156894265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4354027770269824209192353 3265520827702368156894265)
      ·
        refine ⟨2449140620776776117670699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3265520827702368156894265 2449140620776776117670699)
        ·
          refine ⟨3673710931165164176506049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2449140620776776117670699 3673710931165164176506049)
          ·
            refine ⟨2755283198373873132379537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3673710931165164176506049 2755283198373873132379537)
            ·
              refine ⟨2066462398780404849284653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2755283198373873132379537 2066462398780404849284653)
              ·
                refine ⟨774923399542651818481745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2066462398780404849284653 774923399542651818481745)
                ·
                  refine ⟨581192549656988863861309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 774923399542651818481745 581192549656988863861309)
                  ·
                    refine ⟨217947206121370823947991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 581192549656988863861309 217947206121370823947991)
                    ·
                      rfl

theorem cell22_636676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 2, 3, 2, 3].length) (baseStart_636676 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_636676 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_636676 prefixEnd_636676 := by exact prefixLift 636676
  have htrace : WordTrace (prefixWord ++ tailWord_636676) baseStart_636676 baseEnd_636676 := by
    simpa [prefixWord, tailWord_636676, baseEnd_636676] using wordTrace_append hprefix tailTrace_636676
  have hstable : (prefixWord ++ tailWord_636676).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_636676).length < 2 ^ (prefixWord ++ tailWord_636676).sum := by decide
  have hdescent : baseEnd_636676 < baseStart_636676 := by decide
  rcases family_descends (prefixWord ++ tailWord_636676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_636704 : List Nat := [2, 1, 1, 5, 1, 1, 1, 2, 5, 3]
def baseStart_636704 : Nat := 118140960795 + 636704 * 2 ^ 59
def prefixEnd_636704 : Nat := 4983230072969 + 3 ^ 40 * 636704 * 2
def baseEnd_636704 : Nat := 217956791093588084247905

theorem tailTrace_636704 : CollatzResearch.WordTrace tailWord_636704 prefixEnd_636704 217956791093588084247905 := by
  unfold tailWord_636704
  simp only [CollatzResearch.WordTrace]
  refine ⟨11611251342668811615522583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15481668456891748820696777 11611251342668811615522583)
  ·
    refine ⟨17416877014003217423283875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11611251342668811615522583 17416877014003217423283875)
    ·
      refine ⟨26125315521004826134925813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17416877014003217423283875 26125315521004826134925813)
      ·
        refine ⟨2449248330094202450149295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 26125315521004826134925813 2449248330094202450149295)
        ·
          refine ⟨3673872495141303675223943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2449248330094202450149295 3673872495141303675223943)
          ·
            refine ⟨5510808742711955512835915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3673872495141303675223943 5510808742711955512835915)
            ·
              refine ⟨8266213114067933269253873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5510808742711955512835915 8266213114067933269253873)
              ·
                refine ⟨6199659835550949951940405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8266213114067933269253873 6199659835550949951940405)
                ·
                  refine ⟨581218109582901557994413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 6199659835550949951940405 581218109582901557994413)
                  ·
                    refine ⟨217956791093588084247905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 581218109582901557994413 217956791093588084247905)
                    ·
                      rfl

theorem cell22_636704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 2, 5, 3].length) (baseStart_636704 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_636704 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_636704 prefixEnd_636704 := by exact prefixLift 636704
  have htrace : WordTrace (prefixWord ++ tailWord_636704) baseStart_636704 baseEnd_636704 := by
    simpa [prefixWord, tailWord_636704, baseEnd_636704] using wordTrace_append hprefix tailTrace_636704
  have hstable : (prefixWord ++ tailWord_636704).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_636704).length < 2 ^ (prefixWord ++ tailWord_636704).sum := by decide
  have hdescent : baseEnd_636704 < baseStart_636704 := by decide
  rcases family_descends (prefixWord ++ tailWord_636704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_636721 : List Nat := [1, 2, 2, 3, 2, 3, 2, 1, 3, 3]
def baseStart_636721 : Nat := 118140960795 + 636721 * 2 ^ 59
def prefixEnd_636721 : Nat := 4983230072969 + 3 ^ 40 * 636721 * 2
def baseEnd_636721 : Nat := 217962610541005706572853

theorem tailTrace_636721 : CollatzResearch.WordTrace tailWord_636721 prefixEnd_636721 217962610541005706572853 := by
  unfold tailWord_636721
  simp only [CollatzResearch.WordTrace]
  refine ⟨23223122726276035134414017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15482081817517356756276011 23223122726276035134414017)
  ·
    refine ⟨17417342044707026350810513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23223122726276035134414017 17417342044707026350810513)
    ·
      refine ⟨13063006533530269763107885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17417342044707026350810513 13063006533530269763107885)
      ·
        refine ⟨4898627450073851161165457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13063006533530269763107885 4898627450073851161165457)
        ·
          refine ⟨3673970587555388370874093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4898627450073851161165457 3673970587555388370874093)
          ·
            refine ⟨1377738970333270639077785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3673970587555388370874093 1377738970333270639077785)
            ·
              refine ⟨1033304227749952979308339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1377738970333270639077785 1033304227749952979308339)
              ·
                refine ⟨1549956341624929468962509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1033304227749952979308339 1549956341624929468962509)
                ·
                  refine ⟨581233628109348550860941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1549956341624929468962509 581233628109348550860941)
                  ·
                    refine ⟨217962610541005706572853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 581233628109348550860941 217962610541005706572853)
                    ·
                      rfl

theorem cell22_636721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 2, 1, 3, 3].length) (baseStart_636721 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_636721 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_636721 prefixEnd_636721 := by exact prefixLift 636721
  have htrace : WordTrace (prefixWord ++ tailWord_636721) baseStart_636721 baseEnd_636721 := by
    simpa [prefixWord, tailWord_636721, baseEnd_636721] using wordTrace_append hprefix tailTrace_636721
  have hstable : (prefixWord ++ tailWord_636721).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_636721).length < 2 ^ (prefixWord ++ tailWord_636721).sum := by decide
  have hdescent : baseEnd_636721 < baseStart_636721 := by decide
  rcases family_descends (prefixWord ++ tailWord_636721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_636798 : List Nat := [4, 2, 3, 1, 1, 2, 1, 1, 3, 4]
def baseStart_636798 : Nat := 118140960795 + 636798 * 2 ^ 59
def prefixEnd_636798 : Nat := 4983230072969 + 3 ^ 40 * 636798 * 2
def baseEnd_636798 : Nat := 217988969214603172397617

theorem tailTrace_636798 : CollatzResearch.WordTrace tailWord_636798 prefixEnd_636798 217988969214603172397617 := by
  unfold tailWord_636798
  simp only [CollatzResearch.WordTrace]
  refine ⟨2903241393374634660620881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15483954097998051523311365 2903241393374634660620881)
  ·
    refine ⟨2177431045030975995465661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2903241393374634660620881 2177431045030975995465661)
    ·
      refine ⟨816536641886615998299623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2177431045030975995465661 816536641886615998299623)
      ·
        refine ⟨1224804962829923997449435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 816536641886615998299623 1224804962829923997449435)
        ·
          refine ⟨1837207444244885996174153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1224804962829923997449435 1837207444244885996174153)
          ·
            refine ⟨1377905583183664497130615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1837207444244885996174153 1377905583183664497130615)
            ·
              refine ⟨2066858374775496745695923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1377905583183664497130615 2066858374775496745695923)
              ·
                refine ⟨3100287562163245118543885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2066858374775496745695923 3100287562163245118543885)
                ·
                  refine ⟨1162607835811216919453957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3100287562163245118543885 1162607835811216919453957)
                  ·
                    refine ⟨217988969214603172397617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1162607835811216919453957 217988969214603172397617)
                    ·
                      rfl

theorem cell22_636798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 1, 1, 3, 4].length) (baseStart_636798 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_636798 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_636798 prefixEnd_636798 := by exact prefixLift 636798
  have htrace : WordTrace (prefixWord ++ tailWord_636798) baseStart_636798 baseEnd_636798 := by
    simpa [prefixWord, tailWord_636798, baseEnd_636798] using wordTrace_append hprefix tailTrace_636798
  have hstable : (prefixWord ++ tailWord_636798).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_636798).length < 2 ^ (prefixWord ++ tailWord_636798).sum := by decide
  have hdescent : baseEnd_636798 < baseStart_636798 := by decide
  rcases family_descends (prefixWord ++ tailWord_636798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_636824 : List Nat := [2, 1, 2, 6, 11]
def baseStart_636824 : Nat := 118140960795 + 636824 * 2 ^ 59
def prefixEnd_636824 : Nat := 4983230072969 + 3 ^ 40 * 636824 * 2
def baseEnd_636824 : Nat := 897110574263159552459

theorem tailTrace_636824 : CollatzResearch.WordTrace tailWord_636824 prefixEnd_636824 897110574263159552459 := by
  unfold tailWord_636824
  simp only [CollatzResearch.WordTrace]
  refine ⟨11613439722451441862706763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15484586296601922483609017 11613439722451441862706763)
  ·
    refine ⟨17420159583677162794060145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11613439722451441862706763 17420159583677162794060145)
    ·
      refine ⟨13065119687757872095545109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17420159583677162794060145 13065119687757872095545109)
      ·
        refine ⟨612427485363650254478677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 13065119687757872095545109 612427485363650254478677)
        ·
          refine ⟨897110574263159552459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 612427485363650254478677 897110574263159552459)
          ·
            rfl

theorem cell22_636824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 11].length) (baseStart_636824 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_636824 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_636824 prefixEnd_636824 := by exact prefixLift 636824
  have htrace : WordTrace (prefixWord ++ tailWord_636824) baseStart_636824 baseEnd_636824 := by
    simpa [prefixWord, tailWord_636824, baseEnd_636824] using wordTrace_append hprefix tailTrace_636824
  have hstable : (prefixWord ++ tailWord_636824).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_636824).length < 2 ^ (prefixWord ++ tailWord_636824).sum := by decide
  have hdescent : baseEnd_636824 < baseStart_636824 := by decide
  rcases family_descends (prefixWord ++ tailWord_636824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_636826 : List Nat := [3, 1, 1, 4, 2, 1, 2, 2, 2, 4]
def baseStart_636826 : Nat := 118140960795 + 636826 * 2 ^ 59
def prefixEnd_636826 : Nat := 4983230072969 + 3 ^ 40 * 636826 * 2
def baseEnd_636826 : Nat := 217998554186820432697531

theorem tailTrace_636826 : CollatzResearch.WordTrace tailWord_636826 prefixEnd_636826 217998554186820432697531 := by
  unfold tailWord_636826
  simp only [CollatzResearch.WordTrace]
  refine ⟨5806738097723909516746583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15484634927263758711324221 5806738097723909516746583)
  ·
    refine ⟨8710107146585864275119875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5806738097723909516746583 8710107146585864275119875)
    ·
      refine ⟨13065160719878796412679813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8710107146585864275119875 13065160719878796412679813)
      ·
        refine ⟨2449717634977274327377465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13065160719878796412679813 2449717634977274327377465)
        ·
          refine ⟨1837288226232955745533099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2449717634977274327377465 1837288226232955745533099)
          ·
            refine ⟨2755932339349433618299649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1837288226232955745533099 2755932339349433618299649)
            ·
              refine ⟨2066949254512075213724737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2755932339349433618299649 2066949254512075213724737)
              ·
                refine ⟨1550211940884056410293553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2066949254512075213724737 1550211940884056410293553)
                ·
                  refine ⟨1162658955663042307720165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1550211940884056410293553 1162658955663042307720165)
                  ·
                    refine ⟨217998554186820432697531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1162658955663042307720165 217998554186820432697531)
                    ·
                      rfl

theorem cell22_636826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 2, 2, 2, 4].length) (baseStart_636826 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_636826 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_636826 prefixEnd_636826 := by exact prefixLift 636826
  have htrace : WordTrace (prefixWord ++ tailWord_636826) baseStart_636826 baseEnd_636826 := by
    simpa [prefixWord, tailWord_636826, baseEnd_636826] using wordTrace_append hprefix tailTrace_636826
  have hstable : (prefixWord ++ tailWord_636826).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_636826).length < 2 ^ (prefixWord ++ tailWord_636826).sum := by decide
  have hdescent : baseEnd_636826 < baseStart_636826 := by decide
  rcases family_descends (prefixWord ++ tailWord_636826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_636828 : List Nat := [2, 2, 3, 3, 1, 1, 1, 4, 2, 3]
def baseStart_636828 : Nat := 118140960795 + 636828 * 2 ^ 59
def prefixEnd_636828 : Nat := 4983230072969 + 3 ^ 40 * 636828 * 2
def baseEnd_636828 : Nat := 217999238827693094147525

theorem tailTrace_636828 : CollatzResearch.WordTrace tailWord_636828 prefixEnd_636828 217999238827693094147525 := by
  unfold tailWord_636828
  simp only [CollatzResearch.WordTrace]
  refine ⟨11613512668444196204279569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15484683557925594939039425 11613512668444196204279569)
  ·
    refine ⟨8710134501333147153209677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11613512668444196204279569 8710134501333147153209677)
    ·
      refine ⟨3266300437999930182453629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8710134501333147153209677 3266300437999930182453629)
      ·
        refine ⟨1224862664249973818420111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3266300437999930182453629 1224862664249973818420111)
        ·
          refine ⟨1837293996374960727630167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1224862664249973818420111 1837293996374960727630167)
          ·
            refine ⟨2755940994562441091445251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1837293996374960727630167 2755940994562441091445251)
            ·
              refine ⟨4133911491843661637167877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2755940994562441091445251 4133911491843661637167877)
              ·
                refine ⟨775108404720686556968977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4133911491843661637167877 775108404720686556968977)
                ·
                  refine ⟨581331303540514917726733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 775108404720686556968977 581331303540514917726733)
                  ·
                    refine ⟨217999238827693094147525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 581331303540514917726733 217999238827693094147525)
                    ·
                      rfl

theorem cell22_636828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 1, 4, 2, 3].length) (baseStart_636828 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_636828 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_636828 prefixEnd_636828 := by exact prefixLift 636828
  have htrace : WordTrace (prefixWord ++ tailWord_636828) baseStart_636828 baseEnd_636828 := by
    simpa [prefixWord, tailWord_636828, baseEnd_636828] using wordTrace_append hprefix tailTrace_636828
  have hstable : (prefixWord ++ tailWord_636828).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_636828).length < 2 ^ (prefixWord ++ tailWord_636828).sum := by decide
  have hdescent : baseEnd_636828 < baseStart_636828 := by decide
  rcases family_descends (prefixWord ++ tailWord_636828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_636856 : List Nat := [2, 1, 2, 1, 2, 3, 3, 2, 3, 3]
def baseStart_636856 : Nat := 118140960795 + 636856 * 2 ^ 59
def prefixEnd_636856 : Nat := 4983230072969 + 3 ^ 40 * 636856 * 2
def baseEnd_636856 : Nat := 218008823799910354447439

theorem tailTrace_636856 : CollatzResearch.WordTrace tailWord_636856 prefixEnd_636856 218008823799910354447439 := by
  unfold tailWord_636856
  simp only [CollatzResearch.WordTrace]
  refine ⟨11614023290393476595289211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15485364387191302127052281 11614023290393476595289211)
  ·
    refine ⟨17421034935590214892933817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11614023290393476595289211 17421034935590214892933817)
    ·
      refine ⟨13065776201692661169700363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17421034935590214892933817 13065776201692661169700363)
      ·
        refine ⟨19598664302538991754550545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13065776201692661169700363 19598664302538991754550545)
        ·
          refine ⟨14698998226904243815912909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19598664302538991754550545 14698998226904243815912909)
          ·
            refine ⟨5512124335089091430967341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14698998226904243815912909 5512124335089091430967341)
            ·
              refine ⟨2067046625658409286612753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5512124335089091430967341 2067046625658409286612753)
              ·
                refine ⟨1550284969243806964959565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2067046625658409286612753 1550284969243806964959565)
                ·
                  refine ⟨581356863466427611859837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1550284969243806964959565 581356863466427611859837)
                  ·
                    refine ⟨218008823799910354447439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 581356863466427611859837 218008823799910354447439)
                    ·
                      rfl

theorem cell22_636856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 3, 2, 3, 3].length) (baseStart_636856 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_636856 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_636856 prefixEnd_636856 := by exact prefixLift 636856
  have htrace : WordTrace (prefixWord ++ tailWord_636856) baseStart_636856 baseEnd_636856 := by
    simpa [prefixWord, tailWord_636856, baseEnd_636856] using wordTrace_append hprefix tailTrace_636856
  have hstable : (prefixWord ++ tailWord_636856).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_636856).length < 2 ^ (prefixWord ++ tailWord_636856).sum := by decide
  have hdescent : baseEnd_636856 < baseStart_636856 := by decide
  rcases family_descends (prefixWord ++ tailWord_636856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_636860 : List Nat := [2, 2, 2, 5, 1, 2, 1, 1, 2, 4]
def baseStart_636860 : Nat := 118140960795 + 636860 * 2 ^ 59
def prefixEnd_636860 : Nat := 4983230072969 + 3 ^ 40 * 636860 * 2
def baseEnd_636860 : Nat := 218010193081655677347427

theorem tailTrace_636860 : CollatzResearch.WordTrace tailWord_636860 prefixEnd_636860 218010193081655677347427 := by
  unfold tailWord_636860
  simp only [CollatzResearch.WordTrace]
  refine ⟨11614096236386230936862017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15485461648514974582482689 11614096236386230936862017)
  ·
    refine ⟨8710572177289673202646513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11614096236386230936862017 8710572177289673202646513)
    ·
      refine ⟨6532929132967254901984885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8710572177289673202646513 6532929132967254901984885)
      ·
        refine ⟨612462106215680147061083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 6532929132967254901984885 612462106215680147061083)
        ·
          refine ⟨918693159323520220591625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 612462106215680147061083 918693159323520220591625)
          ·
            refine ⟨689019869492640165443719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 918693159323520220591625 689019869492640165443719)
            ·
              refine ⟨1033529804238960248165579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 689019869492640165443719 1033529804238960248165579)
              ·
                refine ⟨1550294706358440372248369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1033529804238960248165579 1550294706358440372248369)
                ·
                  refine ⟨1162721029768830279186277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1550294706358440372248369 1162721029768830279186277)
                  ·
                    refine ⟨218010193081655677347427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1162721029768830279186277 218010193081655677347427)
                    ·
                      rfl

theorem cell22_636860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 2, 1, 1, 2, 4].length) (baseStart_636860 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_636860 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_636860 prefixEnd_636860 := by exact prefixLift 636860
  have htrace : WordTrace (prefixWord ++ tailWord_636860) baseStart_636860 baseEnd_636860 := by
    simpa [prefixWord, tailWord_636860, baseEnd_636860] using wordTrace_append hprefix tailTrace_636860
  have hstable : (prefixWord ++ tailWord_636860).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_636860).length < 2 ^ (prefixWord ++ tailWord_636860).sum := by decide
  have hdescent : baseEnd_636860 < baseStart_636860 := by decide
  rcases family_descends (prefixWord ++ tailWord_636860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_636941 : List Nat := [1, 7, 1, 2, 2, 1, 1, 1, 3, 3]
def baseStart_636941 : Nat := 118140960795 + 636941 * 2 ^ 59
def prefixEnd_636941 : Nat := 4983230072969 + 3 ^ 40 * 636941 * 2
def baseEnd_636941 : Nat := 218037921036998466072179

theorem tailTrace_636941 : CollatzResearch.WordTrace tailWord_636941 prefixEnd_636941 218037921036998466072179 := by
  unfold tailWord_636941
  simp only [CollatzResearch.WordTrace]
  refine ⟨23231146785479012707422677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15487431190319341804948451 23231146785479012707422677)
  ·
    refine ⟨544480002784664360330219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 23231146785479012707422677 544480002784664360330219)
    ·
      refine ⟨816720004176996540495329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 544480002784664360330219 816720004176996540495329)
      ·
        refine ⟨612540003132747405371497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 816720004176996540495329 612540003132747405371497)
        ·
          refine ⟨459405002349560554028623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 612540003132747405371497 459405002349560554028623)
          ·
            refine ⟨689107503524340831042935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 459405002349560554028623 689107503524340831042935)
            ·
              refine ⟨1033661255286511246564403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 689107503524340831042935 1033661255286511246564403)
              ·
                refine ⟨1550491882929766869846605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1033661255286511246564403 1550491882929766869846605)
                ·
                  refine ⟨581434456098662576192477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1550491882929766869846605 581434456098662576192477)
                  ·
                    refine ⟨218037921036998466072179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 581434456098662576192477 218037921036998466072179)
                    ·
                      rfl

theorem cell22_636941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 2, 1, 1, 1, 3, 3].length) (baseStart_636941 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_636941 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_636941 prefixEnd_636941 := by exact prefixLift 636941
  have htrace : WordTrace (prefixWord ++ tailWord_636941) baseStart_636941 baseEnd_636941 := by
    simpa [prefixWord, tailWord_636941, baseEnd_636941] using wordTrace_append hprefix tailTrace_636941
  have hstable : (prefixWord ++ tailWord_636941).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_636941).length < 2 ^ (prefixWord ++ tailWord_636941).sum := by decide
  have hdescent : baseEnd_636941 < baseStart_636941 := by decide
  rcases family_descends (prefixWord ++ tailWord_636941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_636963 : List Nat := [1, 1, 1, 4, 3, 1, 3, 3, 2, 3]
def baseStart_636963 : Nat := 118140960795 + 636963 * 2 ^ 59
def prefixEnd_636963 : Nat := 4983230072969 + 3 ^ 40 * 636963 * 2
def baseEnd_636963 : Nat := 218045452086597742022111

theorem tailTrace_636963 : CollatzResearch.WordTrace tailWord_636963 prefixEnd_636963 218045452086597742022111 := by
  unfold tailWord_636963
  simp only [CollatzResearch.WordTrace]
  refine ⟨23231949191399310464723543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15487966127599540309815695 23231949191399310464723543)
  ·
    refine ⟨34847923787098965697085315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23231949191399310464723543 34847923787098965697085315)
    ·
      refine ⟨52271885680648448545627973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34847923787098965697085315 52271885680648448545627973)
      ·
        refine ⟨9800978565121584102305245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 52271885680648448545627973 9800978565121584102305245)
        ·
          refine ⟨3675366961920594038364467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9800978565121584102305245 3675366961920594038364467)
          ·
            refine ⟨5513050442880891057546701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3675366961920594038364467 5513050442880891057546701)
            ·
              refine ⟨2067393916080334146580013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5513050442880891057546701 2067393916080334146580013)
              ·
                refine ⟨775272718530125304967505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2067393916080334146580013 775272718530125304967505)
                ·
                  refine ⟨581454538897593978725629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 775272718530125304967505 581454538897593978725629)
                  ·
                    refine ⟨218045452086597742022111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 581454538897593978725629 218045452086597742022111)
                    ·
                      rfl

theorem cell22_636963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 3, 3, 2, 3].length) (baseStart_636963 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_636963 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_636963 prefixEnd_636963 := by exact prefixLift 636963
  have htrace : WordTrace (prefixWord ++ tailWord_636963) baseStart_636963 baseEnd_636963 := by
    simpa [prefixWord, tailWord_636963, baseEnd_636963] using wordTrace_append hprefix tailTrace_636963
  have hstable : (prefixWord ++ tailWord_636963).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_636963).length < 2 ^ (prefixWord ++ tailWord_636963).sum := by decide
  have hdescent : baseEnd_636963 < baseStart_636963 := by decide
  rcases family_descends (prefixWord ++ tailWord_636963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_636967 : List Nat := [1, 1, 7, 1, 2, 2, 1, 2, 1, 4]
def baseStart_636967 : Nat := 118140960795 + 636967 * 2 ^ 59
def prefixEnd_636967 : Nat := 4983230072969 + 3 ^ 40 * 636967 * 2
def baseEnd_636967 : Nat := 218046821368343064922099

theorem tailTrace_636967 : CollatzResearch.WordTrace tailWord_636967 prefixEnd_636967 218046821368343064922099 := by
  unfold tailWord_636967
  simp only [CollatzResearch.WordTrace]
  refine ⟨23232095083384819147869155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15488063388923212765246103 23232095083384819147869155)
  ·
    refine ⟨34848142625077228721803733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23232095083384819147869155 34848142625077228721803733)
    ·
      refine ⟨816753342775247548167275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 34848142625077228721803733 816753342775247548167275)
      ·
        refine ⟨1225130014162871322250913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 816753342775247548167275 1225130014162871322250913)
        ·
          refine ⟨918847510622153491688185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1225130014162871322250913 918847510622153491688185)
          ·
            refine ⟨689135632966615118766139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 918847510622153491688185 689135632966615118766139)
            ·
              refine ⟨1033703449449922678149209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 689135632966615118766139 1033703449449922678149209)
              ·
                refine ⟨775277587087442008611907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1033703449449922678149209 775277587087442008611907)
                ·
                  refine ⟨1162916380631163012917861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 775277587087442008611907 1162916380631163012917861)
                  ·
                    refine ⟨218046821368343064922099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1162916380631163012917861 218046821368343064922099)
                    ·
                      rfl

theorem cell22_636967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 2, 1, 2, 1, 4].length) (baseStart_636967 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_636967 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_636967 prefixEnd_636967 := by exact prefixLift 636967
  have htrace : WordTrace (prefixWord ++ tailWord_636967) baseStart_636967 baseEnd_636967 := by
    simpa [prefixWord, tailWord_636967, baseEnd_636967] using wordTrace_append hprefix tailTrace_636967
  have hstable : (prefixWord ++ tailWord_636967).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_636967).length < 2 ^ (prefixWord ++ tailWord_636967).sum := by decide
  have hdescent : baseEnd_636967 < baseStart_636967 := by decide
  rcases family_descends (prefixWord ++ tailWord_636967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_636978 : List Nat := [3, 2, 1, 1, 2, 4, 2, 1, 2, 4]
def baseStart_636978 : Nat := 118140960795 + 636978 * 2 ^ 59
def prefixEnd_636978 : Nat := 4983230072969 + 3 ^ 40 * 636978 * 2
def baseEnd_636978 : Nat := 218050586893142702897065

theorem tailTrace_636978 : CollatzResearch.WordTrace tailWord_636978 prefixEnd_636978 218050586893142702897065 := by
  unfold tailWord_636978
  simp only [CollatzResearch.WordTrace]
  refine ⟨5808124071586242006629897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15488330857563312017679725 5808124071586242006629897)
  ·
    refine ⟨4356093053689681504972423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5808124071586242006629897 4356093053689681504972423)
    ·
      refine ⟨6534139580534522257458635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4356093053689681504972423 6534139580534522257458635)
      ·
        refine ⟨9801209370801783386187953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6534139580534522257458635 9801209370801783386187953)
        ·
          refine ⟨7350907028101337539640965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9801209370801783386187953 7350907028101337539640965)
          ·
            refine ⟨1378295067769000788682681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7350907028101337539640965 1378295067769000788682681)
            ·
              refine ⟨1033721300826750591512011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1378295067769000788682681 1033721300826750591512011)
              ·
                refine ⟨1550581951240125887268017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1033721300826750591512011 1550581951240125887268017)
                ·
                  refine ⟨1162936463430094415451013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1550581951240125887268017 1162936463430094415451013)
                  ·
                    refine ⟨218050586893142702897065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1162936463430094415451013 218050586893142702897065)
                    ·
                      rfl

theorem cell22_636978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 2, 1, 2, 4].length) (baseStart_636978 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_636978 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_636978 prefixEnd_636978 := by exact prefixLift 636978
  have htrace : WordTrace (prefixWord ++ tailWord_636978) baseStart_636978 baseEnd_636978 := by
    simpa [prefixWord, tailWord_636978, baseEnd_636978] using wordTrace_append hprefix tailTrace_636978
  have hstable : (prefixWord ++ tailWord_636978).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_636978).length < 2 ^ (prefixWord ++ tailWord_636978).sum := by decide
  have hdescent : baseEnd_636978 < baseStart_636978 := by decide
  rcases family_descends (prefixWord ++ tailWord_636978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_636980 : List Nat := [2, 5, 1, 2, 2, 1, 1, 2, 1, 5]
def baseStart_636980 : Nat := 118140960795 + 636980 * 2 ^ 59
def prefixEnd_636980 : Nat := 4983230072969 + 3 ^ 40 * 636980 * 2
def baseEnd_636980 : Nat := 218051271534015364347059

theorem tailTrace_636980 : CollatzResearch.WordTrace tailWord_636980 prefixEnd_636980 218051271534015364347059 := by
  unfold tailWord_636980
  simp only [CollatzResearch.WordTrace]
  refine ⟨11616284616168861184046197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15488379488225148245394929 11616284616168861184046197)
  ·
    refine ⟨1089026682765830736004331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 11616284616168861184046197 1089026682765830736004331)
    ·
      refine ⟨1633540024148746104006497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1089026682765830736004331 1633540024148746104006497)
      ·
        refine ⟨1225155018111559578004873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1633540024148746104006497 1225155018111559578004873)
        ·
          refine ⟨918866263583669683503655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1225155018111559578004873 918866263583669683503655)
          ·
            refine ⟨1378299395375504525255483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 918866263583669683503655 1378299395375504525255483)
            ·
              refine ⟨2067449093063256787883225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1378299395375504525255483 2067449093063256787883225)
              ·
                refine ⟨1550586819797442590912419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2067449093063256787883225 1550586819797442590912419)
                ·
                  refine ⟨2325880229696163886368629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1550586819797442590912419 2325880229696163886368629)
                  ·
                    refine ⟨218051271534015364347059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2325880229696163886368629 218051271534015364347059)
                    ·
                      rfl

theorem cell22_636980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 1, 2, 1, 5].length) (baseStart_636980 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_636980 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_636980 prefixEnd_636980 := by exact prefixLift 636980
  have htrace : WordTrace (prefixWord ++ tailWord_636980) baseStart_636980 baseEnd_636980 := by
    simpa [prefixWord, tailWord_636980, baseEnd_636980] using wordTrace_append hprefix tailTrace_636980
  have hstable : (prefixWord ++ tailWord_636980).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_636980).length < 2 ^ (prefixWord ++ tailWord_636980).sum := by decide
  have hdescent : baseEnd_636980 < baseStart_636980 := by decide
  rcases family_descends (prefixWord ++ tailWord_636980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_637006 : List Nat := [4, 1, 1, 1, 1, 4, 1, 1, 2, 6]
def baseStart_637006 : Nat := 118140960795 + 637006 * 2 ^ 59
def prefixEnd_637006 : Nat := 4983230072969 + 3 ^ 40 * 637006 * 2
def baseEnd_637006 : Nat := 218060171865359963196979

theorem tailTrace_637006 : CollatzResearch.WordTrace tailWord_637006 prefixEnd_637006 218060171865359963196979 := by
  unfold tailWord_637006
  simp only [CollatzResearch.WordTrace]
  refine ⟨2904189691280441101067359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15489011686829019205692581 2904189691280441101067359)
  ·
    refine ⟨4356284536920661651601039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2904189691280441101067359 4356284536920661651601039)
    ·
      refine ⟨6534426805380992477401559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4356284536920661651601039 6534426805380992477401559)
      ·
        refine ⟨9801640208071488716102339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6534426805380992477401559 9801640208071488716102339)
        ·
          refine ⟨14702460312107233074153509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9801640208071488716102339 14702460312107233074153509)
          ·
            refine ⟨2756711308520106201403783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14702460312107233074153509 2756711308520106201403783)
            ·
              refine ⟨4135066962780159302105675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2756711308520106201403783 4135066962780159302105675)
              ·
                refine ⟨6202600444170238953158513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4135066962780159302105675 6202600444170238953158513)
                ·
                  refine ⟨4651950333127679214868885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6202600444170238953158513 4651950333127679214868885)
                  ·
                    refine ⟨218060171865359963196979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4651950333127679214868885 218060171865359963196979)
                    ·
                      rfl

theorem cell22_637006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 1, 1, 2, 6].length) (baseStart_637006 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_637006 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_637006 prefixEnd_637006 := by exact prefixLift 637006
  have htrace : WordTrace (prefixWord ++ tailWord_637006) baseStart_637006 baseEnd_637006 := by
    simpa [prefixWord, tailWord_637006, baseEnd_637006] using wordTrace_append hprefix tailTrace_637006
  have hstable : (prefixWord ++ tailWord_637006).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_637006).length < 2 ^ (prefixWord ++ tailWord_637006).sum := by decide
  have hdescent : baseEnd_637006 < baseStart_637006 := by decide
  rcases family_descends (prefixWord ++ tailWord_637006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_637010 : List Nat := [3, 2, 2, 1, 5, 1, 1, 7]
def baseStart_637010 : Nat := 118140960795 + 637010 * 2 ^ 59
def prefixEnd_637010 : Nat := 4983230072969 + 3 ^ 40 * 637010 * 2
def baseEnd_637010 : Nat := 24229060127456142899663

theorem tailTrace_637010 : CollatzResearch.WordTrace tailWord_637010 prefixEnd_637010 24229060127456142899663 := by
  unfold tailWord_637010
  simp only [CollatzResearch.WordTrace]
  refine ⟨5808415855557259372921121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15489108948152691661122989 5808415855557259372921121)
  ·
    refine ⟨4356311891667944529690841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5808415855557259372921121 4356311891667944529690841)
    ·
      refine ⟨3267233918750958397268131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4356311891667944529690841 3267233918750958397268131)
      ·
        refine ⟨4900850878126437595902197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3267233918750958397268131 4900850878126437595902197)
        ·
          refine ⟨459454769824353524615831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4900850878126437595902197 459454769824353524615831)
          ·
            refine ⟨689182154736530286923747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 459454769824353524615831 689182154736530286923747)
            ·
              refine ⟨1033773232104795430385621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 689182154736530286923747 1033773232104795430385621)
              ·
                refine ⟨24229060127456142899663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1033773232104795430385621 24229060127456142899663)
                ·
                  rfl

theorem cell22_637010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 5, 1, 1, 7].length) (baseStart_637010 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_637010 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_637010 prefixEnd_637010 := by exact prefixLift 637010
  have htrace : WordTrace (prefixWord ++ tailWord_637010) baseStart_637010 baseEnd_637010 := by
    simpa [prefixWord, tailWord_637010, baseEnd_637010] using wordTrace_append hprefix tailTrace_637010
  have hstable : (prefixWord ++ tailWord_637010).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_637010).length < 2 ^ (prefixWord ++ tailWord_637010).sum := by decide
  have hdescent : baseEnd_637010 < baseStart_637010 := by decide
  rcases family_descends (prefixWord ++ tailWord_637010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_637042 : List Nat := [3, 2, 1, 2, 2, 3, 2, 3, 1, 3]
def baseStart_637042 : Nat := 118140960795 + 637042 * 2 ^ 59
def prefixEnd_637042 : Nat := 4983230072969 + 3 ^ 40 * 637042 * 2
def baseEnd_637042 : Nat := 218072495401067869296869

theorem tailTrace_637042 : CollatzResearch.WordTrace tailWord_637042 prefixEnd_637042 218072495401067869296869 := by
  unfold tailWord_637042
  simp only [CollatzResearch.WordTrace]
  refine ⟨5808707639528276739212345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15489887038742071304566253 5808707639528276739212345)
  ·
    refine ⟨4356530729646207554409259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5808707639528276739212345 4356530729646207554409259)
    ·
      refine ⟨6534796094469311331613889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4356530729646207554409259 6534796094469311331613889)
      ·
        refine ⟨4901097070851983498710417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6534796094469311331613889 4901097070851983498710417)
        ·
          refine ⟨3675822803138987624032813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4901097070851983498710417 3675822803138987624032813)
          ·
            refine ⟨1378433551177120359012305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3675822803138987624032813 1378433551177120359012305)
            ·
              refine ⟨1033825163382840269259229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1378433551177120359012305 1033825163382840269259229)
              ·
                refine ⟨387684436268565100972211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1033825163382840269259229 387684436268565100972211)
                ·
                  refine ⟨581526654402847651458317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 387684436268565100972211 581526654402847651458317)
                  ·
                    refine ⟨218072495401067869296869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 581526654402847651458317 218072495401067869296869)
                    ·
                      rfl

theorem cell22_637042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 2, 3, 1, 3].length) (baseStart_637042 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_637042 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_637042 prefixEnd_637042 := by exact prefixLift 637042
  have htrace : WordTrace (prefixWord ++ tailWord_637042) baseStart_637042 baseEnd_637042 := by
    simpa [prefixWord, tailWord_637042, baseEnd_637042] using wordTrace_append hprefix tailTrace_637042
  have hstable : (prefixWord ++ tailWord_637042).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_637042).length < 2 ^ (prefixWord ++ tailWord_637042).sum := by decide
  have hdescent : baseEnd_637042 < baseStart_637042 := by decide
  rcases family_descends (prefixWord ++ tailWord_637042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_637078 : List Nat := [5, 3, 2, 1, 2, 1, 2, 6]
def baseStart_637078 : Nat := 118140960795 + 637078 * 2 ^ 59
def prefixEnd_637078 : Nat := 4983230072969 + 3 ^ 40 * 637078 * 2
def baseEnd_637078 : Nat := 24231646548530641710751

theorem tailTrace_637078 : CollatzResearch.WordTrace tailWord_637078 prefixEnd_637078 24231646548530641710751 := by
  unfold tailWord_637078
  simp only [CollatzResearch.WordTrace]
  refine ⟨1452258974123917819072493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 15490762390655123403439925 1452258974123917819072493)
  ·
    refine ⟨544597115296469182152185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1452258974123917819072493 544597115296469182152185)
    ·
      refine ⟨408447836472351886614139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 544597115296469182152185 408447836472351886614139)
      ·
        refine ⟨612671754708527829921209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 408447836472351886614139 612671754708527829921209)
        ·
          refine ⟨459503816031395872440907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 612671754708527829921209 459503816031395872440907)
          ·
            refine ⟨689255724047093808661361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 459503816031395872440907 689255724047093808661361)
            ·
              refine ⟨516941793035320356496021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 689255724047093808661361 516941793035320356496021)
              ·
                refine ⟨24231646548530641710751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 516941793035320356496021 24231646548530641710751)
                ·
                  rfl

theorem cell22_637078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 2, 1, 2, 6].length) (baseStart_637078 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_637078 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_637078 prefixEnd_637078 := by exact prefixLift 637078
  have htrace : WordTrace (prefixWord ++ tailWord_637078) baseStart_637078 baseEnd_637078 := by
    simpa [prefixWord, tailWord_637078, baseEnd_637078] using wordTrace_append hprefix tailTrace_637078
  have hstable : (prefixWord ++ tailWord_637078).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_637078).length < 2 ^ (prefixWord ++ tailWord_637078).sum := by decide
  have hdescent : baseEnd_637078 < baseStart_637078 := by decide
  rcases family_descends (prefixWord ++ tailWord_637078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_637085 : List Nat := [1, 4, 2, 1, 1, 4, 2, 2, 1, 4]
def baseStart_637085 : Nat := 118140960795 + 637085 * 2 ^ 59
def prefixEnd_637085 : Nat := 4983230072969 + 3 ^ 40 * 637085 * 2
def baseEnd_637085 : Nat := 218087215179830090471737

theorem tailTrace_637085 : CollatzResearch.WordTrace tailWord_637085 prefixEnd_637085 218087215179830090471737 := by
  unfold tailWord_637085
  simp only [CollatzResearch.WordTrace]
  refine ⟨23236398896957325300664709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15490932597971550200443139 23236398896957325300664709)
  ·
    refine ⟨4356824793179498493874633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23236398896957325300664709 4356824793179498493874633)
    ·
      refine ⟨3267618594884623870405975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4356824793179498493874633 3267618594884623870405975)
      ·
        refine ⟨4901427892326935805608963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3267618594884623870405975 4901427892326935805608963)
        ·
          refine ⟨7352141838490403708413445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4901427892326935805608963 7352141838490403708413445)
          ·
            refine ⟨1378526594716950695327521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7352141838490403708413445 1378526594716950695327521)
            ·
              refine ⟨1033894946037713021495641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1378526594716950695327521 1033894946037713021495641)
              ·
                refine ⟨775421209528284766121731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1033894946037713021495641 775421209528284766121731)
                ·
                  refine ⟨1163131814292427149182597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 775421209528284766121731 1163131814292427149182597)
                  ·
                    refine ⟨218087215179830090471737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1163131814292427149182597 218087215179830090471737)
                    ·
                      rfl

theorem cell22_637085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 2, 2, 1, 4].length) (baseStart_637085 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_637085 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_637085 prefixEnd_637085 := by exact prefixLift 637085
  have htrace : WordTrace (prefixWord ++ tailWord_637085) baseStart_637085 baseEnd_637085 := by
    simpa [prefixWord, tailWord_637085, baseEnd_637085] using wordTrace_append hprefix tailTrace_637085
  have hstable : (prefixWord ++ tailWord_637085).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_637085).length < 2 ^ (prefixWord ++ tailWord_637085).sum := by decide
  have hdescent : baseEnd_637085 < baseStart_637085 := by decide
  rcases family_descends (prefixWord ++ tailWord_637085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_637111 : List Nat := [1, 1, 3, 1, 4, 2, 10]
def baseStart_637111 : Nat := 118140960795 + 637111 * 2 ^ 59
def prefixEnd_637111 : Nat := 4983230072969 + 3 ^ 40 * 637111 * 2
def baseEnd_637111 : Nat := 8077633907821284789691

theorem tailTrace_637111 : CollatzResearch.WordTrace tailWord_637111 prefixEnd_637111 8077633907821284789691 := by
  unfold tailWord_637111
  simp only [CollatzResearch.WordTrace]
  refine ⟨23237347194863131741111187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15491564796575421160740791 23237347194863131741111187)
  ·
    refine ⟨34856020792294697611666781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23237347194863131741111187 34856020792294697611666781)
    ·
      refine ⟨13071007797110511604375043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34856020792294697611666781 13071007797110511604375043)
      ·
        refine ⟨19606511695665767406562565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13071007797110511604375043 19606511695665767406562565)
        ·
          refine ⟨3676220942937331388730481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19606511695665767406562565 3676220942937331388730481)
          ·
            refine ⟨2757165707202998541547861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3676220942937331388730481 2757165707202998541547861)
            ·
              refine ⟨8077633907821284789691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 2757165707202998541547861 8077633907821284789691)
              ·
                rfl

theorem cell22_637111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 10].length) (baseStart_637111 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_637111 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_637111 prefixEnd_637111 := by exact prefixLift 637111
  have htrace : WordTrace (prefixWord ++ tailWord_637111) baseStart_637111 baseEnd_637111 := by
    simpa [prefixWord, tailWord_637111, baseEnd_637111] using wordTrace_append hprefix tailTrace_637111
  have hstable : (prefixWord ++ tailWord_637111).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_637111).length < 2 ^ (prefixWord ++ tailWord_637111).sum := by decide
  have hdescent : baseEnd_637111 < baseStart_637111 := by decide
  rcases family_descends (prefixWord ++ tailWord_637111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_637113 : List Nat := [1, 2, 1, 4, 1, 2, 3, 2, 2, 4]
def baseStart_637113 : Nat := 118140960795 + 637113 * 2 ^ 59
def prefixEnd_637113 : Nat := 4983230072969 + 3 ^ 40 * 637113 * 2
def baseEnd_637113 : Nat := 218096800152047350771651

theorem tailTrace_637113 : CollatzResearch.WordTrace tailWord_637113 prefixEnd_637113 218096800152047350771651 := by
  unfold tailWord_637113
  simp only [CollatzResearch.WordTrace]
  refine ⟨23237420140855886082683993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15491613427237257388455995 23237420140855886082683993)
  ·
    refine ⟨17428065105641914562012995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23237420140855886082683993 17428065105641914562012995)
    ·
      refine ⟨26142097658462871843019493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17428065105641914562012995 26142097658462871843019493)
      ·
        refine ⟨4901643310961788470566155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26142097658462871843019493 4901643310961788470566155)
        ·
          refine ⟨7352464966442682705849233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4901643310961788470566155 7352464966442682705849233)
          ·
            refine ⟨5514348724832012029386925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7352464966442682705849233 5514348724832012029386925)
            ·
              refine ⟨2067880771812004511020097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5514348724832012029386925 2067880771812004511020097)
              ·
                refine ⟨1550910578859003383265073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2067880771812004511020097 1550910578859003383265073)
                ·
                  refine ⟨1163182934144252537448805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1550910578859003383265073 1163182934144252537448805)
                  ·
                    refine ⟨218096800152047350771651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1163182934144252537448805 218096800152047350771651)
                    ·
                      rfl

theorem cell22_637113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 3, 2, 2, 4].length) (baseStart_637113 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_637113 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_637113 prefixEnd_637113 := by exact prefixLift 637113
  have htrace : WordTrace (prefixWord ++ tailWord_637113) baseStart_637113 baseEnd_637113 := by
    simpa [prefixWord, tailWord_637113, baseEnd_637113] using wordTrace_append hprefix tailTrace_637113
  have hstable : (prefixWord ++ tailWord_637113).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_637113).length < 2 ^ (prefixWord ++ tailWord_637113).sum := by decide
  have hdescent : baseEnd_637113 < baseStart_637113 := by decide
  rcases family_descends (prefixWord ++ tailWord_637113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_637143 : List Nat := [1, 1, 3, 2, 1, 2, 1, 3, 5, 3]
def baseStart_637143 : Nat := 118140960795 + 637143 * 2 ^ 59
def prefixEnd_637143 : Nat := 4983230072969 + 3 ^ 40 * 637143 * 2
def baseEnd_637143 : Nat := 218107069765137272521559

theorem tailTrace_637143 : CollatzResearch.WordTrace tailWord_637143 prefixEnd_637143 218107069765137272521559 := by
  unfold tailWord_637143
  simp only [CollatzResearch.WordTrace]
  refine ⟨23238514330747201206276083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15492342887164800804184055 23238514330747201206276083)
  ·
    refine ⟨34857771496120801809414125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23238514330747201206276083 34857771496120801809414125)
    ·
      refine ⟨13071664311045300678530297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34857771496120801809414125 13071664311045300678530297)
      ·
        refine ⟨9803748233283975508897723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13071664311045300678530297 9803748233283975508897723)
        ·
          refine ⟨14705622349925963263346585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9803748233283975508897723 14705622349925963263346585)
          ·
            refine ⟨11029216762444472447509939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14705622349925963263346585 11029216762444472447509939)
            ·
              refine ⟨16543825143666708671264909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11029216762444472447509939 16543825143666708671264909)
              ·
                refine ⟨6203934428875015751724341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16543825143666708671264909 6203934428875015751724341)
                ·
                  refine ⟨581618852707032726724157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 6203934428875015751724341 581618852707032726724157)
                  ·
                    refine ⟨218107069765137272521559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 581618852707032726724157 218107069765137272521559)
                    ·
                      rfl

theorem cell22_637143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 3, 5, 3].length) (baseStart_637143 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_637143 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_637143 prefixEnd_637143 := by exact prefixLift 637143
  have htrace : WordTrace (prefixWord ++ tailWord_637143) baseStart_637143 baseEnd_637143 := by
    simpa [prefixWord, tailWord_637143, baseEnd_637143] using wordTrace_append hprefix tailTrace_637143
  have hstable : (prefixWord ++ tailWord_637143).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_637143).length < 2 ^ (prefixWord ++ tailWord_637143).sum := by decide
  have hdescent : baseEnd_637143 < baseStart_637143 := by decide
  rcases family_descends (prefixWord ++ tailWord_637143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_637224 : List Nat := [2, 1, 5, 1, 4, 1, 1, 2, 5]
def baseStart_637224 : Nat := 118140960795 + 637224 * 2 ^ 59
def prefixEnd_637224 : Nat := 4983230072969 + 3 ^ 40 * 637224 * 2
def baseEnd_637224 : Nat := 72711599240160020415437

theorem tailTrace_637224 : CollatzResearch.WordTrace tailWord_637224 prefixEnd_637224 72711599240160020415437 := by
  unfold tailWord_637224
  simp only [CollatzResearch.WordTrace]
  refine ⟨11620734321726876019987363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15494312428969168026649817 11620734321726876019987363)
  ·
    refine ⟨17431101482590314029981045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11620734321726876019987363 17431101482590314029981045)
    ·
      refine ⟨1634165763992841940310723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 17431101482590314029981045 1634165763992841940310723)
      ·
        refine ⟨2451248645989262910466085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1634165763992841940310723 2451248645989262910466085)
        ·
          refine ⟨459609121122986795712391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2451248645989262910466085 459609121122986795712391)
          ·
            refine ⟨689413681684480193568587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 459609121122986795712391 689413681684480193568587)
            ·
              refine ⟨1034120522526720290352881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 689413681684480193568587 1034120522526720290352881)
              ·
                refine ⟨775590391895040217764661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1034120522526720290352881 775590391895040217764661)
                ·
                  refine ⟨72711599240160020415437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 775590391895040217764661 72711599240160020415437)
                  ·
                    rfl

theorem cell22_637224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 4, 1, 1, 2, 5].length) (baseStart_637224 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_637224 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_637224 prefixEnd_637224 := by exact prefixLift 637224
  have htrace : WordTrace (prefixWord ++ tailWord_637224) baseStart_637224 baseEnd_637224 := by
    simpa [prefixWord, tailWord_637224, baseEnd_637224] using wordTrace_append hprefix tailTrace_637224
  have hstable : (prefixWord ++ tailWord_637224).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_637224).length < 2 ^ (prefixWord ++ tailWord_637224).sum := by decide
  have hdescent : baseEnd_637224 < baseStart_637224 := by decide
  rcases family_descends (prefixWord ++ tailWord_637224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_637235 : List Nat := [1, 1, 1, 2, 5, 1, 1, 6, 4]
def baseStart_637235 : Nat := 118140960795 + 637235 * 2 ^ 59
def prefixEnd_637235 : Nat := 4983230072969 + 3 ^ 40 * 637235 * 2
def baseEnd_637235 : Nat := 72712854415093233073759

theorem tailTrace_637235 : CollatzResearch.WordTrace tailWord_637235 prefixEnd_637235 72712854415093233073759 := by
  unfold tailWord_637235
  simp only [CollatzResearch.WordTrace]
  refine ⟨23241869846413900918625159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15494579897609267279083439 23241869846413900918625159)
  ·
    refine ⟨34862804769620851377937739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23241869846413900918625159 34862804769620851377937739)
    ·
      refine ⟨52294207154431277066906609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34862804769620851377937739 52294207154431277066906609)
      ·
        refine ⟨39220655365823457800179957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52294207154431277066906609 39220655365823457800179957)
        ·
          refine ⟨3676936440545949168766871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 39220655365823457800179957 3676936440545949168766871)
          ·
            refine ⟨5515404660818923753150307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3676936440545949168766871 5515404660818923753150307)
            ·
              refine ⟨8273106991228385629725461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5515404660818923753150307 8273106991228385629725461)
              ·
                refine ⟨387801890213830576393381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 8273106991228385629725461 387801890213830576393381)
                ·
                  refine ⟨72712854415093233073759, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 387801890213830576393381 72712854415093233073759)
                  ·
                    rfl

theorem cell22_637235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 6, 4].length) (baseStart_637235 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_637235 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_637235 prefixEnd_637235 := by exact prefixLift 637235
  have htrace : WordTrace (prefixWord ++ tailWord_637235) baseStart_637235 baseEnd_637235 := by
    simpa [prefixWord, tailWord_637235, baseEnd_637235] using wordTrace_append hprefix tailTrace_637235
  have hstable : (prefixWord ++ tailWord_637235).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_637235).length < 2 ^ (prefixWord ++ tailWord_637235).sum := by decide
  have hdescent : baseEnd_637235 < baseStart_637235 := by decide
  rcases family_descends (prefixWord ++ tailWord_637235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_637248 : List Nat := [2, 1, 1, 2, 2, 1, 2, 1, 6, 4]
def baseStart_637248 : Nat := 118140960795 + 637248 * 2 ^ 59
def prefixEnd_637248 : Nat := 4983230072969 + 3 ^ 40 * 637248 * 2
def baseEnd_637248 : Nat := 218143013410951998646237

theorem tailTrace_637248 : CollatzResearch.WordTrace tailWord_637248 prefixEnd_637248 218143013410951998646237 := by
  unfold tailWord_637248
  simp only [CollatzResearch.WordTrace]
  refine ⟨11621171997683402069424199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15494895996911202759232265 11621171997683402069424199)
  ·
    refine ⟨17431757996525103104136299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11621171997683402069424199 17431757996525103104136299)
    ·
      refine ⟨26147636994787654656204449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17431757996525103104136299 26147636994787654656204449)
      ·
        refine ⟨19610727746090740992153337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26147636994787654656204449 19610727746090740992153337)
        ·
          refine ⟨14708045809568055744115003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19610727746090740992153337 14708045809568055744115003)
          ·
            refine ⟨22062068714352083616172505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14708045809568055744115003 22062068714352083616172505)
            ·
              refine ⟨16546551535764062712129379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22062068714352083616172505 16546551535764062712129379)
              ·
                refine ⟨24819827303646094068194069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16546551535764062712129379 24819827303646094068194069)
                ·
                  refine ⟨1163429404858410659446597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 24819827303646094068194069 1163429404858410659446597)
                  ·
                    refine ⟨218143013410951998646237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1163429404858410659446597 218143013410951998646237)
                    ·
                      rfl

theorem cell22_637248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 1, 6, 4].length) (baseStart_637248 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_637248 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_637248 prefixEnd_637248 := by exact prefixLift 637248
  have htrace : WordTrace (prefixWord ++ tailWord_637248) baseStart_637248 baseEnd_637248 := by
    simpa [prefixWord, tailWord_637248, baseEnd_637248] using wordTrace_append hprefix tailTrace_637248
  have hstable : (prefixWord ++ tailWord_637248).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_637248).length < 2 ^ (prefixWord ++ tailWord_637248).sum := by decide
  have hdescent : baseEnd_637248 < baseStart_637248 := by decide
  rcases family_descends (prefixWord ++ tailWord_637248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_637269 : List Nat := [1, 3, 2, 2, 4, 2, 1, 3, 4]
def baseStart_637269 : Nat := 118140960795 + 637269 * 2 ^ 59
def prefixEnd_637269 : Nat := 4983230072969 + 3 ^ 40 * 637269 * 2
def baseEnd_637269 : Nat := 72716734046704981290391

theorem tailTrace_637269 : CollatzResearch.WordTrace tailWord_637269 prefixEnd_637269 72716734046704981290391 := by
  unfold tailWord_637269
  simp only [CollatzResearch.WordTrace]
  refine ⟨23243109928290724725362861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15495406618860483150241907 23243109928290724725362861)
  ·
    refine ⟨8716166223109021772011073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23243109928290724725362861 8716166223109021772011073)
    ·
      refine ⟨6537124667331766329008305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8716166223109021772011073 6537124667331766329008305)
      ·
        refine ⟨4902843500498824746756229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6537124667331766329008305 4902843500498824746756229)
        ·
          refine ⟨919283156343529640016793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4902843500498824746756229 919283156343529640016793)
          ·
            refine ⟨689462367257647230012595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 919283156343529640016793 689462367257647230012595)
            ·
              refine ⟨1034193550886470845018893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 689462367257647230012595 1034193550886470845018893)
              ·
                refine ⟨387822581582426566882085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1034193550886470845018893 387822581582426566882085)
                ·
                  refine ⟨72716734046704981290391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 387822581582426566882085 72716734046704981290391)
                  ·
                    rfl

theorem cell22_637269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 2, 1, 3, 4].length) (baseStart_637269 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_637269 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_637269 prefixEnd_637269 := by exact prefixLift 637269
  have htrace : WordTrace (prefixWord ++ tailWord_637269) baseStart_637269 baseEnd_637269 := by
    simpa [prefixWord, tailWord_637269, baseEnd_637269] using wordTrace_append hprefix tailTrace_637269
  have hstable : (prefixWord ++ tailWord_637269).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_637269).length < 2 ^ (prefixWord ++ tailWord_637269).sum := by decide
  have hdescent : baseEnd_637269 < baseStart_637269 := by decide
  rcases family_descends (prefixWord ++ tailWord_637269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_637280 : List Nat := [2, 1, 1, 3, 5, 2, 8]
def baseStart_637280 : Nat := 118140960795 + 637280 * 2 ^ 59
def prefixEnd_637280 : Nat := 4983230072969 + 3 ^ 40 * 637280 * 2
def baseEnd_637280 : Nat := 8079776580182021549857

theorem tailTrace_637280 : CollatzResearch.WordTrace tailWord_637280 prefixEnd_637280 8079776580182021549857 := by
  unfold tailWord_637280
  simp only [CollatzResearch.WordTrace]
  refine ⟨11621755565625436802006647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15495674087500582402675529 11621755565625436802006647)
  ·
    refine ⟨17432633348438155203009971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11621755565625436802006647 17432633348438155203009971)
    ·
      refine ⟨26148950022657232804514957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17432633348438155203009971 26148950022657232804514957)
      ·
        refine ⟨9805856258496462301693109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26148950022657232804514957 9805856258496462301693109)
        ·
          refine ⟨919299024234043340783729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 9805856258496462301693109 919299024234043340783729)
          ·
            refine ⟨689474268175532505587797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 919299024234043340783729 689474268175532505587797)
            ·
              refine ⟨8079776580182021549857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 689474268175532505587797 8079776580182021549857)
              ·
                rfl

theorem cell22_637280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 2, 8].length) (baseStart_637280 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_637280 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_637280 prefixEnd_637280 := by exact prefixLift 637280
  have htrace : WordTrace (prefixWord ++ tailWord_637280) baseStart_637280 baseEnd_637280 := by
    simpa [prefixWord, tailWord_637280, baseEnd_637280] using wordTrace_append hprefix tailTrace_637280
  have hstable : (prefixWord ++ tailWord_637280).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_637280).length < 2 ^ (prefixWord ++ tailWord_637280).sum := by decide
  have hdescent : baseEnd_637280 < baseStart_637280 := by decide
  rcases family_descends (prefixWord ++ tailWord_637280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_637282 : List Nat := [3, 3, 2, 1, 1, 3, 1, 2, 2, 4]
def baseStart_637282 : Nat := 118140960795 + 637282 * 2 ^ 59
def prefixEnd_637282 : Nat := 4983230072969 + 3 ^ 40 * 637282 * 2
def baseEnd_637282 : Nat := 218154652305787243296133

theorem tailTrace_637282 : CollatzResearch.WordTrace tailWord_637282 prefixEnd_637282 218154652305787243296133 := by
  unfold tailWord_637282
  simp only [CollatzResearch.WordTrace]
  refine ⟨5810896019310906986396525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15495722718162418630390733 5810896019310906986396525)
  ·
    refine ⟨2179086007241590119898697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5810896019310906986396525 2179086007241590119898697)
    ·
      refine ⟨1634314505431192589924023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2179086007241590119898697 1634314505431192589924023)
      ·
        refine ⟨2451471758146788884886035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1634314505431192589924023 2451471758146788884886035)
        ·
          refine ⟨3677207637220183327329053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2451471758146788884886035 3677207637220183327329053)
          ·
            refine ⟨1378952863957568747748395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3677207637220183327329053 1378952863957568747748395)
            ·
              refine ⟨2068429295936353121622593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1378952863957568747748395 2068429295936353121622593)
              ·
                refine ⟨1551321971952264841216945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2068429295936353121622593 1551321971952264841216945)
                ·
                  refine ⟨1163491478964198630912709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1551321971952264841216945 1163491478964198630912709)
                  ·
                    refine ⟨218154652305787243296133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1163491478964198630912709 218154652305787243296133)
                    ·
                      rfl

theorem cell22_637282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 1, 2, 2, 4].length) (baseStart_637282 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_637282 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_637282 prefixEnd_637282 := by exact prefixLift 637282
  have htrace : WordTrace (prefixWord ++ tailWord_637282) baseStart_637282 baseEnd_637282 := by
    simpa [prefixWord, tailWord_637282, baseEnd_637282] using wordTrace_append hprefix tailTrace_637282
  have hstable : (prefixWord ++ tailWord_637282).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_637282).length < 2 ^ (prefixWord ++ tailWord_637282).sum := by decide
  have hdescent : baseEnd_637282 < baseStart_637282 := by decide
  rcases family_descends (prefixWord ++ tailWord_637282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_637295 : List Nat := [1, 1, 2, 1, 3, 1, 2, 5, 3, 3]
def baseStart_637295 : Nat := 118140960795 + 637295 * 2 ^ 59
def prefixEnd_637295 : Nat := 4983230072969 + 3 ^ 40 * 637295 * 2
def baseEnd_637295 : Nat := 218159102471459542721093

theorem tailTrace_637295 : CollatzResearch.WordTrace tailWord_637295 prefixEnd_637295 218159102471459542721093 := by
  unfold tailWord_637295
  simp only [CollatzResearch.WordTrace]
  refine ⟨23244058226196531165809339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15496038817464354110539559 23244058226196531165809339)
  ·
    refine ⟨34866087339294796748714009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23244058226196531165809339 34866087339294796748714009)
    ·
      refine ⟨26149565504471097561535507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34866087339294796748714009 26149565504471097561535507)
      ·
        refine ⟨39224348256706646342303261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26149565504471097561535507 39224348256706646342303261)
        ·
          refine ⟨14709130596264992378363723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39224348256706646342303261 14709130596264992378363723)
          ·
            refine ⟨22063695894397488567545585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14709130596264992378363723 22063695894397488567545585)
            ·
              refine ⟨16547771920798116425659189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22063695894397488567545585 16547771920798116425659189)
              ·
                refine ⟨1551353617574823414905549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16547771920798116425659189 1551353617574823414905549)
                ·
                  refine ⟨581757606590558780589581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1551353617574823414905549 581757606590558780589581)
                  ·
                    refine ⟨218159102471459542721093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 581757606590558780589581 218159102471459542721093)
                    ·
                      rfl

theorem cell22_637295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 5, 3, 3].length) (baseStart_637295 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_637295 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_637295 prefixEnd_637295 := by exact prefixLift 637295
  have htrace : WordTrace (prefixWord ++ tailWord_637295) baseStart_637295 baseEnd_637295 := by
    simpa [prefixWord, tailWord_637295, baseEnd_637295] using wordTrace_append hprefix tailTrace_637295
  have hstable : (prefixWord ++ tailWord_637295).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_637295).length < 2 ^ (prefixWord ++ tailWord_637295).sum := by decide
  have hdescent : baseEnd_637295 < baseStart_637295 := by decide
  rcases family_descends (prefixWord ++ tailWord_637295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_637301 : List Nat := [1, 3, 4, 1, 2, 3, 2, 1, 2, 3]
def baseStart_637301 : Nat := 118140960795 + 637301 * 2 ^ 59
def prefixEnd_637301 : Nat := 4983230072969 + 3 ^ 40 * 637301 * 2
def baseEnd_637301 : Nat := 218161156394077527071075

theorem tailTrace_637301 : CollatzResearch.WordTrace tailWord_637301 prefixEnd_637301 218161156394077527071075 := by
  unfold tailWord_637301
  simp only [CollatzResearch.WordTrace]
  refine ⟨23244277064174794190527757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15496184709449862793685171 23244277064174794190527757)
  ·
    refine ⟨8716603899065547821447909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23244277064174794190527757 8716603899065547821447909)
    ·
      refine ⟨1634363231074790216521483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8716603899065547821447909 1634363231074790216521483)
      ·
        refine ⟨2451544846612185324782225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1634363231074790216521483 2451544846612185324782225)
        ·
          refine ⟨1838658634959138993586669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2451544846612185324782225 1838658634959138993586669)
          ·
            refine ⟨689496988109677122595001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1838658634959138993586669 689496988109677122595001)
            ·
              refine ⟨517122741082257841946251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 689496988109677122595001 517122741082257841946251)
              ·
                refine ⟨775684111623386762919377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 517122741082257841946251 775684111623386762919377)
                ·
                  refine ⟨581763083717540072189533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 775684111623386762919377 581763083717540072189533)
                  ·
                    refine ⟨218161156394077527071075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 581763083717540072189533 218161156394077527071075)
                    ·
                      rfl

theorem cell22_637301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 3, 2, 1, 2, 3].length) (baseStart_637301 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_637301 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_637301 prefixEnd_637301 := by exact prefixLift 637301
  have htrace : WordTrace (prefixWord ++ tailWord_637301) baseStart_637301 baseEnd_637301 := by
    simpa [prefixWord, tailWord_637301, baseEnd_637301] using wordTrace_append hprefix tailTrace_637301
  have hstable : (prefixWord ++ tailWord_637301).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_637301).length < 2 ^ (prefixWord ++ tailWord_637301).sum := by decide
  have hdescent : baseEnd_637301 < baseStart_637301 := by decide
  rcases family_descends (prefixWord ++ tailWord_637301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_637308 : List Nat := [2, 2, 2, 1, 1, 1, 2, 2, 9]
def baseStart_637308 : Nat := 118140960795 + 637308 * 2 ^ 59
def prefixEnd_637308 : Nat := 4983230072969 + 3 ^ 40 * 637308 * 2
def baseEnd_637308 : Nat := 72721184212377280715351

theorem tailTrace_637308 : CollatzResearch.WordTrace tailWord_637308 prefixEnd_637308 72721184212377280715351 := by
  unfold tailWord_637308
  simp only [CollatzResearch.WordTrace]
  refine ⟨11622266187574717193016289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15496354916766289590688385 11622266187574717193016289)
  ·
    refine ⟨8716699640681037894762217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11622266187574717193016289 8716699640681037894762217)
    ·
      refine ⟨6537524730510778421071663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8716699640681037894762217 6537524730510778421071663)
      ·
        refine ⟨9806287095766167631607495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6537524730510778421071663 9806287095766167631607495)
        ·
          refine ⟨14709430643649251447411243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9806287095766167631607495 14709430643649251447411243)
          ·
            refine ⟨22064145965473877171116865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14709430643649251447411243 22064145965473877171116865)
            ·
              refine ⟨16548109474105407878337649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22064145965473877171116865 16548109474105407878337649)
              ·
                refine ⟨12411082105579055908753237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16548109474105407878337649 12411082105579055908753237)
                ·
                  refine ⟨72721184212377280715351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 12411082105579055908753237 72721184212377280715351)
                  ·
                    rfl

theorem cell22_637308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 2, 9].length) (baseStart_637308 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_637308 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_637308 prefixEnd_637308 := by exact prefixLift 637308
  have htrace : WordTrace (prefixWord ++ tailWord_637308) baseStart_637308 baseEnd_637308 := by
    simpa [prefixWord, tailWord_637308, baseEnd_637308] using wordTrace_append hprefix tailTrace_637308
  have hstable : (prefixWord ++ tailWord_637308).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_637308).length < 2 ^ (prefixWord ++ tailWord_637308).sum := by decide
  have hdescent : baseEnd_637308 < baseStart_637308 := by decide
  rcases family_descends (prefixWord ++ tailWord_637308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_637353 : List Nat := [1, 2, 1, 1, 1, 1, 3, 2, 10]
def baseStart_637353 : Nat := 118140960795 + 637353 * 2 ^ 59
def prefixEnd_637353 : Nat := 4983230072969 + 3 ^ 40 * 637353 * 2
def baseEnd_637353 : Nat := 72726319018922241590305

theorem tailTrace_637353 : CollatzResearch.WordTrace tailWord_637353 prefixEnd_637353 72726319018922241590305 := by
  unfold tailWord_637353
  simp only [CollatzResearch.WordTrace]
  refine ⟨23246173659986407071420713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15497449106657604714280475 23246173659986407071420713)
  ·
    refine ⟨17434630244989805303565535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23246173659986407071420713 17434630244989805303565535)
    ·
      refine ⟨26151945367484707955348303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17434630244989805303565535 26151945367484707955348303)
      ·
        refine ⟨39227918051227061933022455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26151945367484707955348303 39227918051227061933022455)
        ·
          refine ⟨58841877076840592899533683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39227918051227061933022455 58841877076840592899533683)
          ·
            refine ⟨88262815615260889349300525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58841877076840592899533683 88262815615260889349300525)
            ·
              refine ⟨33098555855722833505987697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 88262815615260889349300525 33098555855722833505987697)
              ·
                refine ⟨24823916891792125129490773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33098555855722833505987697 24823916891792125129490773)
                ·
                  refine ⟨72726319018922241590305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 24823916891792125129490773 72726319018922241590305)
                  ·
                    rfl

theorem cell22_637353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 2, 10].length) (baseStart_637353 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_637353 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_637353 prefixEnd_637353 := by exact prefixLift 637353
  have htrace : WordTrace (prefixWord ++ tailWord_637353) baseStart_637353 baseEnd_637353 := by
    simpa [prefixWord, tailWord_637353, baseEnd_637353] using wordTrace_append hprefix tailTrace_637353
  have hstable : (prefixWord ++ tailWord_637353).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_637353).length < 2 ^ (prefixWord ++ tailWord_637353).sum := by decide
  have hdescent : baseEnd_637353 < baseStart_637353 := by decide
  rcases family_descends (prefixWord ++ tailWord_637353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_637372 : List Nat := [2, 2, 2, 4, 1, 1, 2, 1, 3, 4]
def baseStart_637372 : Nat := 118140960795 + 637372 * 2 ^ 59
def prefixEnd_637372 : Nat := 4983230072969 + 3 ^ 40 * 637372 * 2
def baseEnd_637372 : Nat := 218185461145057008545857

theorem tailTrace_637372 : CollatzResearch.WordTrace tailWord_637372 prefixEnd_637372 218185461145057008545857 := by
  unfold tailWord_637372
  simp only [CollatzResearch.WordTrace]
  refine ⟨11623433323458786658181185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15497911097945048877574913 11623433323458786658181185)
  ·
    refine ⟨8717574992594089993635889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11623433323458786658181185 8717574992594089993635889)
    ·
      refine ⟨6538181244445567495226917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8717574992594089993635889 6538181244445567495226917)
      ·
        refine ⟨1225908983333543905355047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6538181244445567495226917 1225908983333543905355047)
        ·
          refine ⟨1838863475000315858032571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1225908983333543905355047 1838863475000315858032571)
          ·
            refine ⟨2758295212500473787048857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1838863475000315858032571 2758295212500473787048857)
            ·
              refine ⟨2068721409375355340286643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2758295212500473787048857 2068721409375355340286643)
              ·
                refine ⟨3103082114063033010429965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2068721409375355340286643 3103082114063033010429965)
                ·
                  refine ⟨1163655792773637378911237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3103082114063033010429965 1163655792773637378911237)
                  ·
                    refine ⟨218185461145057008545857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1163655792773637378911237 218185461145057008545857)
                    ·
                      rfl

theorem cell22_637372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 2, 1, 3, 4].length) (baseStart_637372 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_637372 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_637372 prefixEnd_637372 := by exact prefixLift 637372
  have htrace : WordTrace (prefixWord ++ tailWord_637372) baseStart_637372 baseEnd_637372 := by
    simpa [prefixWord, tailWord_637372, baseEnd_637372] using wordTrace_append hprefix tailTrace_637372
  have hstable : (prefixWord ++ tailWord_637372).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_637372).length < 2 ^ (prefixWord ++ tailWord_637372).sum := by decide
  have hdescent : baseEnd_637372 < baseStart_637372 := by decide
  rcases family_descends (prefixWord ++ tailWord_637372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_637385 : List Nat := [1, 2, 1, 1, 2, 1, 6, 2, 1, 5]
def baseStart_637385 : Nat := 118140960795 + 637385 * 2 ^ 59
def prefixEnd_637385 : Nat := 4983230072969 + 3 ^ 40 * 637385 * 2
def baseEnd_637385 : Nat := 218189911310729307970817

theorem tailTrace_637385 : CollatzResearch.WordTrace tailWord_637385 prefixEnd_637385 218189911310729307970817 := by
  unfold tailWord_637385
  simp only [CollatzResearch.WordTrace]
  refine ⟨23247340795870476536585609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15498227197246984357723739 23247340795870476536585609)
  ·
    refine ⟨17435505596902857402439207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23247340795870476536585609 17435505596902857402439207)
    ·
      refine ⟨26153258395354286103658811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17435505596902857402439207 26153258395354286103658811)
      ·
        refine ⟨39229887593031429155488217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26153258395354286103658811 39229887593031429155488217)
        ·
          refine ⟨29422415694773571866616163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39229887593031429155488217 29422415694773571866616163)
          ·
            refine ⟨44133623542160357799924245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29422415694773571866616163 44133623542160357799924245)
            ·
              refine ⟨2068763603538766771871449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 44133623542160357799924245 2068763603538766771871449)
              ·
                refine ⟨1551572702654075078903587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2068763603538766771871449 1551572702654075078903587)
                ·
                  refine ⟨2327359053981112618355381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1551572702654075078903587 2327359053981112618355381)
                  ·
                    refine ⟨218189911310729307970817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2327359053981112618355381 218189911310729307970817)
                    ·
                      rfl

theorem cell22_637385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 6, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 6, 2, 1, 5].length) (baseStart_637385 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_637385 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_637385 prefixEnd_637385 := by exact prefixLift 637385
  have htrace : WordTrace (prefixWord ++ tailWord_637385) baseStart_637385 baseEnd_637385 := by
    simpa [prefixWord, tailWord_637385, baseEnd_637385] using wordTrace_append hprefix tailTrace_637385
  have hstable : (prefixWord ++ tailWord_637385).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_637385).length < 2 ^ (prefixWord ++ tailWord_637385).sum := by decide
  have hdescent : baseEnd_637385 < baseStart_637385 := by decide
  rcases family_descends (prefixWord ++ tailWord_637385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_637400 : List Nat := [2, 1, 2, 2, 2, 1, 1, 3, 4, 4]
def baseStart_637400 : Nat := 118140960795 + 637400 * 2 ^ 59
def prefixEnd_637400 : Nat := 4983230072969 + 3 ^ 40 * 637400 * 2
def baseEnd_637400 : Nat := 218195046117274268845771

theorem tailTrace_637400 : CollatzResearch.WordTrace tailWord_637400 prefixEnd_637400 218195046117274268845771 := by
  unfold tailWord_637400
  simp only [CollatzResearch.WordTrace]
  refine ⟨11623943945408067049190827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15498591927210756065587769 11623943945408067049190827)
  ·
    refine ⟨17435915918112100573786241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11623943945408067049190827 17435915918112100573786241)
    ·
      refine ⟨13076936938584075430339681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17435915918112100573786241 13076936938584075430339681)
      ·
        refine ⟨9807702703938056572754761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13076936938584075430339681 9807702703938056572754761)
        ·
          refine ⟨7355777027953542429566071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9807702703938056572754761 7355777027953542429566071)
          ·
            refine ⟨11033665541930313644349107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7355777027953542429566071 11033665541930313644349107)
            ·
              refine ⟨16550498312895470466523661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11033665541930313644349107 16550498312895470466523661)
              ·
                refine ⟨6206436867335801424946373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16550498312895470466523661 6206436867335801424946373)
                ·
                  refine ⟨1163706912625462767177445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6206436867335801424946373 1163706912625462767177445)
                  ·
                    refine ⟨218195046117274268845771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1163706912625462767177445 218195046117274268845771)
                    ·
                      rfl

theorem cell22_637400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 3, 4, 4].length) (baseStart_637400 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_637400 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_637400 prefixEnd_637400 := by exact prefixLift 637400
  have htrace : WordTrace (prefixWord ++ tailWord_637400) baseStart_637400 baseEnd_637400 := by
    simpa [prefixWord, tailWord_637400, baseEnd_637400] using wordTrace_append hprefix tailTrace_637400
  have hstable : (prefixWord ++ tailWord_637400).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_637400).length < 2 ^ (prefixWord ++ tailWord_637400).sum := by decide
  have hdescent : baseEnd_637400 < baseStart_637400 := by decide
  rcases family_descends (prefixWord ++ tailWord_637400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_637402 : List Nat := [3, 1, 1, 2, 3, 1, 3, 1, 4, 3]
def baseStart_637402 : Nat := 118140960795 + 637402 * 2 ^ 59
def prefixEnd_637402 : Nat := 4983230072969 + 3 ^ 40 * 637402 * 2
def baseEnd_637402 : Nat := 218195730758146930295765

theorem tailTrace_637402 : CollatzResearch.WordTrace tailWord_637402 prefixEnd_637402 218195730758146930295765 := by
  unfold tailWord_637402
  simp only [CollatzResearch.WordTrace]
  refine ⟨5811990209202222109988615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15498640557872592293302973 5811990209202222109988615)
  ·
    refine ⟨8717985313803333164982923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5811990209202222109988615 8717985313803333164982923)
    ·
      refine ⟨13076977970704999747474385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8717985313803333164982923 13076977970704999747474385)
      ·
        refine ⟨9807733478028749810605789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13076977970704999747474385 9807733478028749810605789)
        ·
          refine ⟨3677900054260781178977171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9807733478028749810605789 3677900054260781178977171)
          ·
            refine ⟨5516850081391171768465757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3677900054260781178977171 5516850081391171768465757)
            ·
              refine ⟨2068818780521689413174659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5516850081391171768465757 2068818780521689413174659)
              ·
                refine ⟨3103228170782534119761989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2068818780521689413174659 3103228170782534119761989)
                ·
                  refine ⟨581855282021725147455373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3103228170782534119761989 581855282021725147455373)
                  ·
                    refine ⟨218195730758146930295765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 581855282021725147455373 218195730758146930295765)
                    ·
                      rfl

theorem cell22_637402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 3, 1, 4, 3].length) (baseStart_637402 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_637402 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_637402 prefixEnd_637402 := by exact prefixLift 637402
  have htrace : WordTrace (prefixWord ++ tailWord_637402) baseStart_637402 baseEnd_637402 := by
    simpa [prefixWord, tailWord_637402, baseEnd_637402] using wordTrace_append hprefix tailTrace_637402
  have hstable : (prefixWord ++ tailWord_637402).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_637402).length < 2 ^ (prefixWord ++ tailWord_637402).sum := by decide
  have hdescent : baseEnd_637402 < baseStart_637402 := by decide
  rcases family_descends (prefixWord ++ tailWord_637402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_637415 : List Nat := [1, 1, 5, 2, 1, 1, 2, 9]
def baseStart_637415 : Nat := 118140960795 + 637415 * 2 ^ 59
def prefixEnd_637415 : Nat := 4983230072969 + 3 ^ 40 * 637415 * 2
def baseEnd_637415 : Nat := 24244464547091025524525

theorem tailTrace_637415 : CollatzResearch.WordTrace tailWord_637415 prefixEnd_637415 24244464547091025524525 := by
  unfold tailWord_637415
  simp only [CollatzResearch.WordTrace]
  refine ⟨23248434985761791660177699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15498956657174527773451799 23248434985761791660177699)
  ·
    refine ⟨34872652478642687490266549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23248434985761791660177699 34872652478642687490266549)
    ·
      refine ⟨3269311169872751952212489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 34872652478642687490266549 3269311169872751952212489)
      ·
        refine ⟨2451983377404563964159367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3269311169872751952212489 2451983377404563964159367)
        ·
          refine ⟨3677975066106845946239051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2451983377404563964159367 3677975066106845946239051)
          ·
            refine ⟨5516962599160268919358577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3677975066106845946239051 5516962599160268919358577)
            ·
              refine ⟨4137721949370201689518933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5516962599160268919358577 4137721949370201689518933)
              ·
                refine ⟨24244464547091025524525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 4137721949370201689518933 24244464547091025524525)
                ·
                  rfl

theorem cell22_637415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 2, 9].length) (baseStart_637415 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_637415 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_637415 prefixEnd_637415 := by exact prefixLift 637415
  have htrace : WordTrace (prefixWord ++ tailWord_637415) baseStart_637415 baseEnd_637415 := by
    simpa [prefixWord, tailWord_637415, baseEnd_637415] using wordTrace_append hprefix tailTrace_637415
  have hstable : (prefixWord ++ tailWord_637415).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_637415).length < 2 ^ (prefixWord ++ tailWord_637415).sum := by decide
  have hdescent : baseEnd_637415 < baseStart_637415 := by decide
  rcases family_descends (prefixWord ++ tailWord_637415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_637419 : List Nat := [1, 1, 1, 1, 2, 3, 7, 1, 2, 3]
def baseStart_637419 : Nat := 118140960795 + 637419 * 2 ^ 59
def prefixEnd_637419 : Nat := 4983230072969 + 3 ^ 40 * 637419 * 2
def baseEnd_637419 : Nat := 218201550205564552620713

theorem tailTrace_637419 : CollatzResearch.WordTrace tailWord_637419 prefixEnd_637419 218201550205564552620713 := by
  unfold tailWord_637419
  simp only [CollatzResearch.WordTrace]
  refine ⟨23248580877747300343323311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15499053918498200228882207 23248580877747300343323311)
  ·
    refine ⟨34872871316620950514984967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23248580877747300343323311 34872871316620950514984967)
    ·
      refine ⟨52309306974931425772477451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34872871316620950514984967 52309306974931425772477451)
      ·
        refine ⟨78463960462397138658716177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52309306974931425772477451 78463960462397138658716177)
        ·
          refine ⟨58847970346797853994037133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78463960462397138658716177 58847970346797853994037133)
          ·
            refine ⟨22067988880049195247763925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 58847970346797853994037133 22067988880049195247763925)
            ·
              refine ⟨517218489376153013619467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 22067988880049195247763925 517218489376153013619467)
              ·
                refine ⟨775827734064229520429201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 517218489376153013619467 775827734064229520429201)
                ·
                  refine ⟨581870800548172140321901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 775827734064229520429201 581870800548172140321901)
                  ·
                    refine ⟨218201550205564552620713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 581870800548172140321901 218201550205564552620713)
                    ·
                      rfl

theorem cell22_637419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 7, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 7, 1, 2, 3].length) (baseStart_637419 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_637419 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_637419 prefixEnd_637419 := by exact prefixLift 637419
  have htrace : WordTrace (prefixWord ++ tailWord_637419) baseStart_637419 baseEnd_637419 := by
    simpa [prefixWord, tailWord_637419, baseEnd_637419] using wordTrace_append hprefix tailTrace_637419
  have hstable : (prefixWord ++ tailWord_637419).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_637419).length < 2 ^ (prefixWord ++ tailWord_637419).sum := by decide
  have hdescent : baseEnd_637419 < baseStart_637419 := by decide
  rcases family_descends (prefixWord ++ tailWord_637419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_637464 : List Nat := [2, 1, 2, 3, 3, 1, 3, 1, 3, 3]
def baseStart_637464 : Nat := 118140960795 + 637464 * 2 ^ 59
def prefixEnd_637464 : Nat := 4983230072969 + 3 ^ 40 * 637464 * 2
def baseEnd_637464 : Nat := 218216954625199435245575

theorem tailTrace_637464 : CollatzResearch.WordTrace tailWord_637464 prefixEnd_637464 218216954625199435245575 := by
  unfold tailWord_637464
  simp only [CollatzResearch.WordTrace]
  refine ⟨11625111081292136514355723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15500148108389515352474297 11625111081292136514355723)
  ·
    refine ⟨17437666621938204771533585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11625111081292136514355723 17437666621938204771533585)
    ·
      refine ⟨13078249966453653578650189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17437666621938204771533585 13078249966453653578650189)
      ·
        refine ⟨4904343737420120091993821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13078249966453653578650189 4904343737420120091993821)
        ·
          refine ⟨1839128901532545034497683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4904343737420120091993821 1839128901532545034497683)
          ·
            refine ⟨2758693352298817551746525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1839128901532545034497683 2758693352298817551746525)
            ·
              refine ⟨1034510007112056581904947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2758693352298817551746525 1034510007112056581904947)
              ·
                refine ⟨1551765010668084872857421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1034510007112056581904947 1551765010668084872857421)
                ·
                  refine ⟨581911879000531827321533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1551765010668084872857421 581911879000531827321533)
                  ·
                    refine ⟨218216954625199435245575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 581911879000531827321533 218216954625199435245575)
                    ·
                      rfl

theorem cell22_637464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 3, 1, 3, 3].length) (baseStart_637464 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_637464 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_637464 prefixEnd_637464 := by exact prefixLift 637464
  have htrace : WordTrace (prefixWord ++ tailWord_637464) baseStart_637464 baseEnd_637464 := by
    simpa [prefixWord, tailWord_637464, baseEnd_637464] using wordTrace_append hprefix tailTrace_637464
  have hstable : (prefixWord ++ tailWord_637464).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_637464).length < 2 ^ (prefixWord ++ tailWord_637464).sum := by decide
  have hdescent : baseEnd_637464 < baseStart_637464 := by decide
  rcases family_descends (prefixWord ++ tailWord_637464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_637507 : List Nat := [1, 1, 1, 3, 1, 2, 1, 7, 1, 4]
def baseStart_637507 : Nat := 118140960795 + 637507 * 2 ^ 59
def prefixEnd_637507 : Nat := 4983230072969 + 3 ^ 40 * 637507 * 2
def baseEnd_637507 : Nat := 218231674403961656420443

theorem tailTrace_637507 : CollatzResearch.WordTrace tailWord_637507 prefixEnd_637507 218231674403961656420443 := by
  unfold tailWord_637507
  simp only [CollatzResearch.WordTrace]
  refine ⟨23251790501428491372526775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15501193667618994248351183 23251790501428491372526775)
  ·
    refine ⟨34877685752142737058790163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23251790501428491372526775 34877685752142737058790163)
    ·
      refine ⟨52316528628214105588185245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34877685752142737058790163 52316528628214105588185245)
      ·
        refine ⟨19618698235580289595569467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52316528628214105588185245 19618698235580289595569467)
        ·
          refine ⟨29428047353370434393354201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19618698235580289595569467 29428047353370434393354201)
          ·
            refine ⟨22071035515027825795015651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29428047353370434393354201 22071035515027825795015651)
            ·
              refine ⟨33106553272541738692523477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22071035515027825795015651 33106553272541738692523477)
              ·
                refine ⟨775934842325197000606019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 33106553272541738692523477 775934842325197000606019)
                ·
                  refine ⟨1163902263487795500909029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 775934842325197000606019 1163902263487795500909029)
                  ·
                    refine ⟨218231674403961656420443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1163902263487795500909029 218231674403961656420443)
                    ·
                      rfl

theorem cell22_637507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 7, 1, 4].length) (baseStart_637507 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_637507 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_637507 prefixEnd_637507 := by exact prefixLift 637507
  have htrace : WordTrace (prefixWord ++ tailWord_637507) baseStart_637507 baseEnd_637507 := by
    simpa [prefixWord, tailWord_637507, baseEnd_637507] using wordTrace_append hprefix tailTrace_637507
  have hstable : (prefixWord ++ tailWord_637507).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_637507).length < 2 ^ (prefixWord ++ tailWord_637507).sum := by decide
  have hdescent : baseEnd_637507 < baseStart_637507 := by decide
  rcases family_descends (prefixWord ++ tailWord_637507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_637522 : List Nat := [3, 2, 2, 1, 2, 1, 2, 3, 6]
def baseStart_637522 : Nat := 118140960795 + 637522 * 2 ^ 59
def prefixEnd_637522 : Nat := 4983230072969 + 3 ^ 40 * 637522 * 2
def baseEnd_637522 : Nat := 72745603070168872431799

theorem tailTrace_637522 : CollatzResearch.WordTrace tailWord_637522 prefixEnd_637522 72745603070168872431799 := by
  unfold tailWord_637522
  simp only [CollatzResearch.WordTrace]
  refine ⟨5813084399093537233580705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15501558397582765956215213 5813084399093537233580705)
  ·
    refine ⟨4359813299320152925185529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5813084399093537233580705 4359813299320152925185529)
    ·
      refine ⟨3269859974490114693889147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4359813299320152925185529 3269859974490114693889147)
      ·
        refine ⟨4904789961735172040833721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3269859974490114693889147 4904789961735172040833721)
        ·
          refine ⟨3678592471301379030625291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4904789961735172040833721 3678592471301379030625291)
          ·
            refine ⟨5517888706952068545937937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3678592471301379030625291 5517888706952068545937937)
            ·
              refine ⟨4138416530214051409453453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5517888706952068545937937 4138416530214051409453453)
              ·
                refine ⟨1551906198830269278545045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4138416530214051409453453 1551906198830269278545045)
                ·
                  refine ⟨72745603070168872431799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1551906198830269278545045 72745603070168872431799)
                  ·
                    rfl

theorem cell22_637522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 2, 3, 6].length) (baseStart_637522 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_637522 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_637522 prefixEnd_637522 := by exact prefixLift 637522
  have htrace : WordTrace (prefixWord ++ tailWord_637522) baseStart_637522 baseEnd_637522 := by
    simpa [prefixWord, tailWord_637522, baseEnd_637522] using wordTrace_append hprefix tailTrace_637522
  have hstable : (prefixWord ++ tailWord_637522).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_637522).length < 2 ^ (prefixWord ++ tailWord_637522).sum := by decide
  have hdescent : baseEnd_637522 < baseStart_637522 := by decide
  rcases family_descends (prefixWord ++ tailWord_637522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_637537 : List Nat := [1, 2, 3, 1, 1, 4, 1, 3, 1, 5]
def baseStart_637537 : Nat := 118140960795 + 637537 * 2 ^ 59
def prefixEnd_637537 : Nat := 4983230072969 + 3 ^ 40 * 637537 * 2
def baseEnd_637537 : Nat := 218241944017051578170351

theorem tailTrace_637537 : CollatzResearch.WordTrace tailWord_637537 prefixEnd_637537 218241944017051578170351 := by
  unfold tailWord_637537
  simp only [CollatzResearch.WordTrace]
  refine ⟨23252884691319806496118865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15501923127546537664079243 23252884691319806496118865)
  ·
    refine ⟨17439663518489854872089149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23252884691319806496118865 17439663518489854872089149)
    ·
      refine ⟨6539873819433695577033431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17439663518489854872089149 6539873819433695577033431)
      ·
        refine ⟨9809810729150543365550147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6539873819433695577033431 9809810729150543365550147)
        ·
          refine ⟨14714716093725815048325221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9809810729150543365550147 14714716093725815048325221)
          ·
            refine ⟨2759009267573590321560979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14714716093725815048325221 2759009267573590321560979)
            ·
              refine ⟨4138513901360385482341469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2759009267573590321560979 4138513901360385482341469)
              ·
                refine ⟨1551942713010144555878051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4138513901360385482341469 1551942713010144555878051)
                ·
                  refine ⟨2327914069515216833817077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1551942713010144555878051 2327914069515216833817077)
                  ·
                    refine ⟨218241944017051578170351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2327914069515216833817077 218241944017051578170351)
                    ·
                      rfl

theorem cell22_637537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 1, 3, 1, 5].length) (baseStart_637537 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_637537 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_637537 prefixEnd_637537 := by exact prefixLift 637537
  have htrace : WordTrace (prefixWord ++ tailWord_637537) baseStart_637537 baseEnd_637537 := by
    simpa [prefixWord, tailWord_637537, baseEnd_637537] using wordTrace_append hprefix tailTrace_637537
  have hstable : (prefixWord ++ tailWord_637537).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_637537).length < 2 ^ (prefixWord ++ tailWord_637537).sum := by decide
  have hdescent : baseEnd_637537 < baseStart_637537 := by decide
  rcases family_descends (prefixWord ++ tailWord_637537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_637597 : List Nat := [1, 4, 2, 1, 1, 1, 2, 2, 2, 6]
def baseStart_637597 : Nat := 118140960795 + 637597 * 2 ^ 59
def prefixEnd_637597 : Nat := 4983230072969 + 3 ^ 40 * 637597 * 2
def baseEnd_637597 : Nat := 218262483243231421670167

theorem tailTrace_637597 : CollatzResearch.WordTrace tailWord_637597 prefixEnd_637597 218262483243231421670167 := by
  unfold tailWord_637597
  simp only [CollatzResearch.WordTrace]
  refine ⟨23255073071102436743303045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15503382047401624495535363 23255073071102436743303045)
  ·
    refine ⟨4360326200831706889369321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23255073071102436743303045 4360326200831706889369321)
    ·
      refine ⟨3270244650623780167026991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4360326200831706889369321 3270244650623780167026991)
      ·
        refine ⟨4905366975935670250540487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3270244650623780167026991 4905366975935670250540487)
        ·
          refine ⟨7358050463903505375810731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4905366975935670250540487 7358050463903505375810731)
          ·
            refine ⟨11037075695855258063716097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7358050463903505375810731 11037075695855258063716097)
            ·
              refine ⟨8277806771891443547787073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11037075695855258063716097 8277806771891443547787073)
              ·
                refine ⟨6208355078918582660840305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8277806771891443547787073 6208355078918582660840305)
                ·
                  refine ⟨4656266309188936995630229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6208355078918582660840305 4656266309188936995630229)
                  ·
                    refine ⟨218262483243231421670167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4656266309188936995630229 218262483243231421670167)
                    ·
                      rfl

theorem cell22_637597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 2, 2, 6].length) (baseStart_637597 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_637597 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_637597 prefixEnd_637597 := by exact prefixLift 637597
  have htrace : WordTrace (prefixWord ++ tailWord_637597) baseStart_637597 baseEnd_637597 := by
    simpa [prefixWord, tailWord_637597, baseEnd_637597] using wordTrace_append hprefix tailTrace_637597
  have hstable : (prefixWord ++ tailWord_637597).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_637597).length < 2 ^ (prefixWord ++ tailWord_637597).sum := by decide
  have hdescent : baseEnd_637597 < baseStart_637597 := by decide
  rcases family_descends (prefixWord ++ tailWord_637597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_637601 : List Nat := [1, 2, 3, 3, 3, 2, 2, 6]
def baseStart_637601 : Nat := 118140960795 + 637601 * 2 ^ 59
def prefixEnd_637601 : Nat := 4983230072969 + 3 ^ 40 * 637601 * 2
def baseEnd_637601 : Nat := 24251539169441860507795

theorem tailTrace_637601 : CollatzResearch.WordTrace tailWord_637601 prefixEnd_637601 24251539169441860507795 := by
  unfold tailWord_637601
  simp only [CollatzResearch.WordTrace]
  refine ⟨23255218963087945426448657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15503479308725296950965771 23255218963087945426448657)
  ·
    refine ⟨17441414222315959069836493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23255218963087945426448657 17441414222315959069836493)
    ·
      refine ⟨6540530333368484651188685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17441414222315959069836493 6540530333368484651188685)
      ·
        refine ⟨2452698875013181744195757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6540530333368484651188685 2452698875013181744195757)
        ·
          refine ⟨919762078129943154073409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2452698875013181744195757 919762078129943154073409)
          ·
            refine ⟨689821558597457365555057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 919762078129943154073409 689821558597457365555057)
            ·
              refine ⟨517366168948093024166293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 689821558597457365555057 517366168948093024166293)
              ·
                refine ⟨24251539169441860507795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 517366168948093024166293 24251539169441860507795)
                ·
                  rfl

theorem cell22_637601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 2, 2, 6].length) (baseStart_637601 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_637601 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_637601 prefixEnd_637601 := by exact prefixLift 637601
  have htrace : WordTrace (prefixWord ++ tailWord_637601) baseStart_637601 baseEnd_637601 := by
    simpa [prefixWord, tailWord_637601, baseEnd_637601] using wordTrace_append hprefix tailTrace_637601
  have hstable : (prefixWord ++ tailWord_637601).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_637601).length < 2 ^ (prefixWord ++ tailWord_637601).sum := by decide
  have hdescent : baseEnd_637601 < baseStart_637601 := by decide
  rcases family_descends (prefixWord ++ tailWord_637601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_637646 : List Nat := [4, 1, 1, 1, 3, 2, 4, 1, 5]
def baseStart_637646 : Nat := 118140960795 + 637646 * 2 ^ 59
def prefixEnd_637646 : Nat := 4983230072969 + 3 ^ 40 * 637646 * 2
def baseEnd_637646 : Nat := 72759752314870542398339

theorem tailTrace_637646 : CollatzResearch.WordTrace tailWord_637646 prefixEnd_637646 72759752314870542398339 := by
  unfold tailWord_637646
  simp only [CollatzResearch.WordTrace]
  refine ⟨2907107530990614763979599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15504573498616612074557861 2907107530990614763979599)
  ·
    refine ⟨4360661296485922145969399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2907107530990614763979599 4360661296485922145969399)
    ·
      refine ⟨6540991944728883218954099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4360661296485922145969399 6540991944728883218954099)
      ·
        refine ⟨9811487917093324828431149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6540991944728883218954099 9811487917093324828431149)
        ·
          refine ⟨3679307968909996810661681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9811487917093324828431149 3679307968909996810661681)
          ·
            refine ⟨2759480976682497607996261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3679307968909996810661681 2759480976682497607996261)
            ·
              refine ⟨517402683127968301499299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2759480976682497607996261 517402683127968301499299)
              ·
                refine ⟨776104024691952452248949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 517402683127968301499299 776104024691952452248949)
                ·
                  refine ⟨72759752314870542398339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 776104024691952452248949 72759752314870542398339)
                  ·
                    rfl

theorem cell22_637646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 4, 1, 5].length) (baseStart_637646 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_637646 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_637646 prefixEnd_637646 := by exact prefixLift 637646
  have htrace : WordTrace (prefixWord ++ tailWord_637646) baseStart_637646 baseEnd_637646 := by
    simpa [prefixWord, tailWord_637646, baseEnd_637646] using wordTrace_append hprefix tailTrace_637646
  have hstable : (prefixWord ++ tailWord_637646).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_637646).length < 2 ^ (prefixWord ++ tailWord_637646).sum := by decide
  have hdescent : baseEnd_637646 < baseStart_637646 := by decide
  rcases family_descends (prefixWord ++ tailWord_637646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_637657 : List Nat := [1, 2, 1, 2, 3, 2, 2, 1, 8]
def baseStart_637657 : Nat := 118140960795 + 637657 * 2 ^ 59
def prefixEnd_637657 : Nat := 4983230072969 + 3 ^ 40 * 637657 * 2
def baseEnd_637657 : Nat := 72761007489803755056661

theorem tailTrace_637657 : CollatzResearch.WordTrace tailWord_637657 prefixEnd_637657 72761007489803755056661 := by
  unfold tailWord_637657
  simp only [CollatzResearch.WordTrace]
  refine ⟨23257261450885066990487225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15504840967256711326991483 23257261450885066990487225)
  ·
    refine ⟨17442946088163800242865419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23257261450885066990487225 17442946088163800242865419)
    ·
      refine ⟨26164419132245700364298129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17442946088163800242865419 26164419132245700364298129)
      ·
        refine ⟨19623314349184275273223597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26164419132245700364298129 19623314349184275273223597)
        ·
          refine ⟨7358742880944103227458849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19623314349184275273223597 7358742880944103227458849)
          ·
            refine ⟨5519057160708077420594137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7358742880944103227458849 5519057160708077420594137)
            ·
              refine ⟨4139292870531058065445603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5519057160708077420594137 4139292870531058065445603)
              ·
                refine ⟨6208939305796587098168405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4139292870531058065445603 6208939305796587098168405)
                ·
                  refine ⟨72761007489803755056661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 6208939305796587098168405 72761007489803755056661)
                  ·
                    rfl

theorem cell22_637657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 2, 1, 8].length) (baseStart_637657 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_637657 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_637657 prefixEnd_637657 := by exact prefixLift 637657
  have htrace : WordTrace (prefixWord ++ tailWord_637657) baseStart_637657 baseEnd_637657 := by
    simpa [prefixWord, tailWord_637657, baseEnd_637657] using wordTrace_append hprefix tailTrace_637657
  have hstable : (prefixWord ++ tailWord_637657).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_637657).length < 2 ^ (prefixWord ++ tailWord_637657).sum := by decide
  have hdescent : baseEnd_637657 < baseStart_637657 := by decide
  rcases family_descends (prefixWord ++ tailWord_637657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_637687 : List Nat := [1, 1, 3, 1, 1, 1, 3, 2, 3, 6]
def baseStart_637687 : Nat := 118140960795 + 637687 * 2 ^ 59
def prefixEnd_637687 : Nat := 4983230072969 + 3 ^ 40 * 637687 * 2
def baseEnd_637687 : Nat := 218293292082501186919891

theorem tailTrace_637687 : CollatzResearch.WordTrace tailWord_637687 prefixEnd_637687 218293292082501186919891 := by
  unfold tailWord_637687
  simp only [CollatzResearch.WordTrace]
  refine ⟨23258355640776382114079315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15505570427184254742719543 23258355640776382114079315)
  ·
    refine ⟨34887533461164573171118973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23258355640776382114079315 34887533461164573171118973)
    ·
      refine ⟨13082825047936714939169615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34887533461164573171118973 13082825047936714939169615)
      ·
        refine ⟨19624237571905072408754423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13082825047936714939169615 19624237571905072408754423)
        ·
          refine ⟨29436356357857608613131635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19624237571905072408754423 29436356357857608613131635)
          ·
            refine ⟨44154534536786412919697453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29436356357857608613131635 44154534536786412919697453)
            ·
              refine ⟨16557950451294904844886545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44154534536786412919697453 16557950451294904844886545)
              ·
                refine ⟨12418462838471178633664909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16557950451294904844886545 12418462838471178633664909)
                ·
                  refine ⟨4656923564426691987624341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12418462838471178633664909 4656923564426691987624341)
                  ·
                    refine ⟨218293292082501186919891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4656923564426691987624341 218293292082501186919891)
                    ·
                      rfl

theorem cell22_637687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 2, 3, 6].length) (baseStart_637687 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_637687 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_637687 prefixEnd_637687 := by exact prefixLift 637687
  have htrace : WordTrace (prefixWord ++ tailWord_637687) baseStart_637687 baseEnd_637687 := by
    simpa [prefixWord, tailWord_637687, baseEnd_637687] using wordTrace_append hprefix tailTrace_637687
  have hstable : (prefixWord ++ tailWord_637687).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_637687).length < 2 ^ (prefixWord ++ tailWord_637687).sum := by decide
  have hdescent : baseEnd_637687 < baseStart_637687 := by decide
  rcases family_descends (prefixWord ++ tailWord_637687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_637689 : List Nat := [1, 2, 1, 3, 1, 1, 1, 5, 4, 3]
def baseStart_637689 : Nat := 118140960795 + 637689 * 2 ^ 59
def prefixEnd_637689 : Nat := 4983230072969 + 3 ^ 40 * 637689 * 2
def baseEnd_637689 : Nat := 218293976723373848369885

theorem tailTrace_637689 : CollatzResearch.WordTrace tailWord_637689 prefixEnd_637689 218293976723373848369885 := by
  unfold tailWord_637689
  simp only [CollatzResearch.WordTrace]
  refine ⟨23258428586769136455652121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15505619057846090970434747 23258428586769136455652121)
  ·
    refine ⟨17443821440076852341739091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23258428586769136455652121 17443821440076852341739091)
    ·
      refine ⟨26165732160115278512608637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17443821440076852341739091 26165732160115278512608637)
      ·
        refine ⟨9812149560043229442228239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26165732160115278512608637 9812149560043229442228239)
        ·
          refine ⟨14718224340064844163342359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9812149560043229442228239 14718224340064844163342359)
          ·
            refine ⟨22077336510097266245013539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14718224340064844163342359 22077336510097266245013539)
            ·
              refine ⟨33116004765145899367520309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22077336510097266245013539 33116004765145899367520309)
              ·
                refine ⟨3104625446732428065705029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 33116004765145899367520309 3104625446732428065705029)
                ·
                  refine ⟨582117271262330262319693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3104625446732428065705029 582117271262330262319693)
                  ·
                    refine ⟨218293976723373848369885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 582117271262330262319693 218293976723373848369885)
                    ·
                      rfl

theorem cell22_637689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 5, 4, 3].length) (baseStart_637689 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_637689 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_637689 prefixEnd_637689 := by exact prefixLift 637689
  have htrace : WordTrace (prefixWord ++ tailWord_637689) baseStart_637689 baseEnd_637689 := by
    simpa [prefixWord, tailWord_637689, baseEnd_637689] using wordTrace_append hprefix tailTrace_637689
  have hstable : (prefixWord ++ tailWord_637689).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_637689).length < 2 ^ (prefixWord ++ tailWord_637689).sum := by decide
  have hdescent : baseEnd_637689 < baseStart_637689 := by decide
  rcases family_descends (prefixWord ++ tailWord_637689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_637706 : List Nat := [3, 1, 2, 2, 1, 2, 1, 5, 2, 3]
def baseStart_637706 : Nat := 118140960795 + 637706 * 2 ^ 59
def prefixEnd_637706 : Nat := 4983230072969 + 3 ^ 40 * 637706 * 2
def baseEnd_637706 : Nat := 218299796170791470694833

theorem tailTrace_637706 : CollatzResearch.WordTrace tailWord_637706 prefixEnd_637706 218299796170791470694833 := by
  unfold tailWord_637706
  simp only [CollatzResearch.WordTrace]
  refine ⟨5814762156926887089755243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15506032418471698906013981 5814762156926887089755243)
  ·
    refine ⟨8722143235390330634632865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5814762156926887089755243 8722143235390330634632865)
    ·
      refine ⟨6541607426542747975974649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8722143235390330634632865 6541607426542747975974649)
      ·
        refine ⟨4906205569907060981980987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6541607426542747975974649 4906205569907060981980987)
        ·
          refine ⟨7359308354860591472971481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4906205569907060981980987 7359308354860591472971481)
          ·
            refine ⟨5519481266145443604728611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7359308354860591472971481 5519481266145443604728611)
            ·
              refine ⟨8279221899218165407092917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5519481266145443604728611 8279221899218165407092917)
              ·
                refine ⟨776177053051703006914961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8279221899218165407092917 776177053051703006914961)
                ·
                  refine ⟨582132789788777255186221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 776177053051703006914961 582132789788777255186221)
                  ·
                    refine ⟨218299796170791470694833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 582132789788777255186221 218299796170791470694833)
                    ·
                      rfl

theorem cell22_637706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 5, 2, 3].length) (baseStart_637706 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_637706 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_637706 prefixEnd_637706 := by exact prefixLift 637706
  have htrace : WordTrace (prefixWord ++ tailWord_637706) baseStart_637706 baseEnd_637706 := by
    simpa [prefixWord, tailWord_637706, baseEnd_637706] using wordTrace_append hprefix tailTrace_637706
  have hstable : (prefixWord ++ tailWord_637706).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_637706).length < 2 ^ (prefixWord ++ tailWord_637706).sum := by decide
  have hdescent : baseEnd_637706 < baseStart_637706 := by decide
  rcases family_descends (prefixWord ++ tailWord_637706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_637725 : List Nat := [1, 4, 2, 4, 1, 1, 2, 3, 4]
def baseStart_637725 : Nat := 118140960795 + 637725 * 2 ^ 59
def prefixEnd_637725 : Nat := 4983230072969 + 3 ^ 40 * 637725 * 2
def baseEnd_637725 : Nat := 72768766753027251489925

theorem tailTrace_637725 : CollatzResearch.WordTrace tailWord_637725 prefixEnd_637725 72768766753027251489925 := by
  unfold tailWord_637725
  simp only [CollatzResearch.WordTrace]
  refine ⟨23259741614638714603962629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15506494409759143069308419 23259741614638714603962629)
  ·
    refine ⟨4361201552744758988242993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23259741614638714603962629 4361201552744758988242993)
    ·
      refine ⟨3270901164558569241182245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4361201552744758988242993 3270901164558569241182245)
      ·
        refine ⟨613293968354731732721671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3270901164558569241182245 613293968354731732721671)
        ·
          refine ⟨919940952532097599082507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 613293968354731732721671 919940952532097599082507)
          ·
            refine ⟨1379911428798146398623761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 919940952532097599082507 1379911428798146398623761)
            ·
              refine ⟨1034933571598609798967821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1379911428798146398623761 1034933571598609798967821)
              ·
                refine ⟨388100089349478674612933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1034933571598609798967821 388100089349478674612933)
                ·
                  refine ⟨72768766753027251489925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 388100089349478674612933 72768766753027251489925)
                  ·
                    rfl

theorem cell22_637725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 2, 3, 4].length) (baseStart_637725 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_637725 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_637725 prefixEnd_637725 := by exact prefixLift 637725
  have htrace : WordTrace (prefixWord ++ tailWord_637725) baseStart_637725 baseEnd_637725 := by
    simpa [prefixWord, tailWord_637725, baseEnd_637725] using wordTrace_append hprefix tailTrace_637725
  have hstable : (prefixWord ++ tailWord_637725).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_637725).length < 2 ^ (prefixWord ++ tailWord_637725).sum := by decide
  have hdescent : baseEnd_637725 < baseStart_637725 := by decide
  rcases family_descends (prefixWord ++ tailWord_637725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_637751 : List Nat := [1, 1, 3, 1, 2, 1, 6, 1, 3, 3]
def baseStart_637751 : Nat := 118140960795 + 637751 * 2 ^ 59
def prefixEnd_637751 : Nat := 4983230072969 + 3 ^ 40 * 637751 * 2
def baseEnd_637751 : Nat := 218315200590426353319695

theorem tailTrace_637751 : CollatzResearch.WordTrace tailWord_637751 prefixEnd_637751 218315200590426353319695 := by
  unfold tailWord_637751
  simp only [CollatzResearch.WordTrace]
  refine ⟨23260689912544521044409107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15507126608363014029606071 23260689912544521044409107)
  ·
    refine ⟨34891034868816781566613661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23260689912544521044409107 34891034868816781566613661)
    ·
      refine ⟨13084138075806293087480123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34891034868816781566613661 13084138075806293087480123)
      ·
        refine ⟨19626207113709439631220185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13084138075806293087480123 19626207113709439631220185)
        ·
          refine ⟨14719655335282079723415139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19626207113709439631220185 14719655335282079723415139)
          ·
            refine ⟨22079483002923119585122709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14719655335282079723415139 22079483002923119585122709)
            ·
              refine ⟨1034975765762021230552627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 22079483002923119585122709 1034975765762021230552627)
              ·
                refine ⟨1552463648643031845828941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1034975765762021230552627 1552463648643031845828941)
                ·
                  refine ⟨582173868241136942185853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1552463648643031845828941 582173868241136942185853)
                  ·
                    refine ⟨218315200590426353319695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 582173868241136942185853 218315200590426353319695)
                    ·
                      rfl

theorem cell22_637751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 6, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 6, 1, 3, 3].length) (baseStart_637751 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_637751 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_637751 prefixEnd_637751 := by exact prefixLift 637751
  have htrace : WordTrace (prefixWord ++ tailWord_637751) baseStart_637751 baseEnd_637751 := by
    simpa [prefixWord, tailWord_637751, baseEnd_637751] using wordTrace_append hprefix tailTrace_637751
  have hstable : (prefixWord ++ tailWord_637751).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_637751).length < 2 ^ (prefixWord ++ tailWord_637751).sum := by decide
  have hdescent : baseEnd_637751 < baseStart_637751 := by decide
  rcases family_descends (prefixWord ++ tailWord_637751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_637785 : List Nat := [1, 2, 1, 2, 2, 6, 1, 3, 1, 3]
def baseStart_637785 : Nat := 118140960795 + 637785 * 2 ^ 59
def prefixEnd_637785 : Nat := 4983230072969 + 3 ^ 40 * 637785 * 2
def baseEnd_637785 : Nat := 218326839485261597969591

theorem tailTrace_637785 : CollatzResearch.WordTrace tailWord_637785 prefixEnd_637785 218326839485261597969591 := by
  unfold tailWord_637785
  simp only [CollatzResearch.WordTrace]
  refine ⟨23261929994421344851146809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15507953329614229900764539 23261929994421344851146809)
  ·
    refine ⟨17446447495816008638360107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23261929994421344851146809 17446447495816008638360107)
    ·
      refine ⟨26169671243724012957540161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17446447495816008638360107 26169671243724012957540161)
      ·
        refine ⟨19627253432793009718155121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26169671243724012957540161 19627253432793009718155121)
        ·
          refine ⟨14720440074594757288616341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19627253432793009718155121 14720440074594757288616341)
          ·
            refine ⟨690020628496629247903891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 14720440074594757288616341 690020628496629247903891)
            ·
              refine ⟨1035030942744943871855837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 690020628496629247903891 1035030942744943871855837)
              ·
                refine ⟨388136603529353951945939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1035030942744943871855837 388136603529353951945939)
                ·
                  refine ⟨582204905294030927918909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 388136603529353951945939 582204905294030927918909)
                  ·
                    refine ⟨218326839485261597969591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 582204905294030927918909 218326839485261597969591)
                    ·
                      rfl

theorem cell22_637785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 6, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 6, 1, 3, 1, 3].length) (baseStart_637785 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_637785 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_637785 prefixEnd_637785 := by exact prefixLift 637785
  have htrace : WordTrace (prefixWord ++ tailWord_637785) baseStart_637785 baseEnd_637785 := by
    simpa [prefixWord, tailWord_637785, baseEnd_637785] using wordTrace_append hprefix tailTrace_637785
  have hstable : (prefixWord ++ tailWord_637785).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_637785).length < 2 ^ (prefixWord ++ tailWord_637785).sum := by decide
  have hdescent : baseEnd_637785 < baseStart_637785 := by decide
  rcases family_descends (prefixWord ++ tailWord_637785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_637856 : List Nat := [2, 1, 1, 4, 1, 1, 4, 2, 2, 4]
def baseStart_637856 : Nat := 118140960795 + 637856 * 2 ^ 59
def prefixEnd_637856 : Nat := 4983230072969 + 3 ^ 40 * 637856 * 2
def baseEnd_637856 : Nat := 218351144236241079444373

theorem tailTrace_637856 : CollatzResearch.WordTrace tailWord_637856 prefixEnd_637856 218351144236241079444373 := by
  unfold tailWord_637856
  simp only [CollatzResearch.WordTrace]
  refine ⟨11632259788582061988490711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15509679718109415984654281 11632259788582061988490711)
  ·
    refine ⟨17448389682873092982736067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11632259788582061988490711 17448389682873092982736067)
    ·
      refine ⟨26172584524309639474104101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17448389682873092982736067 26172584524309639474104101)
      ·
        refine ⟨4907359598308057401394519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26172584524309639474104101 4907359598308057401394519)
        ·
          refine ⟨7361039397462086102091779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4907359598308057401394519 7361039397462086102091779)
          ·
            refine ⟨11041559096193129153137669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7361039397462086102091779 11041559096193129153137669)
            ·
              refine ⟨2070292330536211716213313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11041559096193129153137669 2070292330536211716213313)
              ·
                refine ⟨1552719247902158787159985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2070292330536211716213313 1552719247902158787159985)
                ·
                  refine ⟨1164539435926619090369989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1552719247902158787159985 1164539435926619090369989)
                  ·
                    refine ⟨218351144236241079444373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1164539435926619090369989 218351144236241079444373)
                    ·
                      rfl

theorem cell22_637856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 4, 2, 2, 4].length) (baseStart_637856 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_637856 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_637856 prefixEnd_637856 := by exact prefixLift 637856
  have htrace : WordTrace (prefixWord ++ tailWord_637856) baseStart_637856 baseEnd_637856 := by
    simpa [prefixWord, tailWord_637856, baseEnd_637856] using wordTrace_append hprefix tailTrace_637856
  have hstable : (prefixWord ++ tailWord_637856).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_637856).length < 2 ^ (prefixWord ++ tailWord_637856).sum := by decide
  have hdescent : baseEnd_637856 < baseStart_637856 := by decide
  rcases family_descends (prefixWord ++ tailWord_637856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_637946 : List Nat := [3, 1, 1, 1, 1, 2, 1, 5, 3, 4]
def baseStart_637946 : Nat := 118140960795 + 637946 * 2 ^ 59
def prefixEnd_637946 : Nat := 4983230072969 + 3 ^ 40 * 637946 * 2
def baseEnd_637946 : Nat := 218381953075510844694097

theorem tailTrace_637946 : CollatzResearch.WordTrace tailWord_637946 prefixEnd_637946 218381953075510844694097 := by
  unfold tailWord_637946
  simp only [CollatzResearch.WordTrace]
  refine ⟨5816950536709517336939423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15511868097892046231838461 5816950536709517336939423)
  ·
    refine ⟨8725425805064276005409135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5816950536709517336939423 8725425805064276005409135)
    ·
      refine ⟨13088138707596414008113703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8725425805064276005409135 13088138707596414008113703)
      ·
        refine ⟨19632208061394621012170555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13088138707596414008113703 19632208061394621012170555)
        ·
          refine ⟨29448312092091931518255833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19632208061394621012170555 29448312092091931518255833)
          ·
            refine ⟨22086234069068948638691875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29448312092091931518255833 22086234069068948638691875)
            ·
              refine ⟨33129351103603422958037813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22086234069068948638691875 33129351103603422958037813)
              ·
                refine ⟨3105876665962820902316045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 33129351103603422958037813 3105876665962820902316045)
                ·
                  refine ⟨1164703749736057838368517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3105876665962820902316045 1164703749736057838368517)
                  ·
                    refine ⟨218381953075510844694097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1164703749736057838368517 218381953075510844694097)
                    ·
                      rfl

theorem cell22_637946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 5, 3, 4].length) (baseStart_637946 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_637946 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_637946 prefixEnd_637946 := by exact prefixLift 637946
  have htrace : WordTrace (prefixWord ++ tailWord_637946) baseStart_637946 baseEnd_637946 := by
    simpa [prefixWord, tailWord_637946, baseEnd_637946] using wordTrace_append hprefix tailTrace_637946
  have hstable : (prefixWord ++ tailWord_637946).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_637946).length < 2 ^ (prefixWord ++ tailWord_637946).sum := by decide
  have hdescent : baseEnd_637946 < baseStart_637946 := by decide
  rcases family_descends (prefixWord ++ tailWord_637946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_637963 : List Nat := [1, 1, 1, 1, 6, 2, 2, 3, 1, 4]
def baseStart_637963 : Nat := 118140960795 + 637963 * 2 ^ 59
def prefixEnd_637963 : Nat := 4983230072969 + 3 ^ 40 * 637963 * 2
def baseEnd_637963 : Nat := 218387772522928467019045

theorem tailTrace_637963 : CollatzResearch.WordTrace tailWord_637963 prefixEnd_637963 218387772522928467019045 := by
  unfold tailWord_637963
  simp only [CollatzResearch.WordTrace]
  refine ⟨23268422187776481251126543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15512281458517654167417695 23268422187776481251126543)
  ·
    refine ⟨34902633281664721876689815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23268422187776481251126543 34902633281664721876689815)
    ·
      refine ⟨52353949922497082815034723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34902633281664721876689815 52353949922497082815034723)
      ·
        refine ⟨78530924883745624222552085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52353949922497082815034723 78530924883745624222552085)
        ·
          refine ⟨3681137103925576135432129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 78530924883745624222552085 3681137103925576135432129)
          ·
            refine ⟨2760852827944182101574097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3681137103925576135432129 2760852827944182101574097)
            ·
              refine ⟨2070639620958136576180573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2760852827944182101574097 2070639620958136576180573)
              ·
                refine ⟨776489857859301216067715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2070639620958136576180573 776489857859301216067715)
                ·
                  refine ⟨1164734786788951824101573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 776489857859301216067715 1164734786788951824101573)
                  ·
                    refine ⟨218387772522928467019045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1164734786788951824101573 218387772522928467019045)
                    ·
                      rfl

theorem cell22_637963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 2, 3, 1, 4].length) (baseStart_637963 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_637963 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_637963 prefixEnd_637963 := by exact prefixLift 637963
  have htrace : WordTrace (prefixWord ++ tailWord_637963) baseStart_637963 baseEnd_637963 := by
    simpa [prefixWord, tailWord_637963, baseEnd_637963] using wordTrace_append hprefix tailTrace_637963
  have hstable : (prefixWord ++ tailWord_637963).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_637963).length < 2 ^ (prefixWord ++ tailWord_637963).sum := by decide
  have hdescent : baseEnd_637963 < baseStart_637963 := by decide
  rcases family_descends (prefixWord ++ tailWord_637963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_637984 : List Nat := [2, 1, 1, 7, 2, 1, 2, 1, 5]
def baseStart_637984 : Nat := 118140960795 + 637984 * 2 ^ 59
def prefixEnd_637984 : Nat := 4983230072969 + 3 ^ 40 * 637984 * 2
def baseEnd_637984 : Nat := 72798320417363804081327

theorem tailTrace_637984 : CollatzResearch.WordTrace tailWord_637984 prefixEnd_637984 72798320417363804081327 := by
  unfold tailWord_637984
  simp only [CollatzResearch.WordTrace]
  refine ⟨11634594060350200918820503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15512792080466934558427337 11634594060350200918820503)
  ·
    refine ⟨17451891090525301378230755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11634594060350200918820503 17451891090525301378230755)
    ·
      refine ⟨26177836635787952067346133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17451891090525301378230755 26177836635787952067346133)
      ·
        refine ⟨613543046151280126578425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 26177836635787952067346133 613543046151280126578425)
        ·
          refine ⟨460157284613460094933819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 613543046151280126578425 460157284613460094933819)
          ·
            refine ⟨690235926920190142400729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 460157284613460094933819 690235926920190142400729)
            ·
              refine ⟨517676945190142606800547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 690235926920190142400729 517676945190142606800547)
              ·
                refine ⟨776515417785213910200821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 517676945190142606800547 776515417785213910200821)
                ·
                  refine ⟨72798320417363804081327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 776515417785213910200821 72798320417363804081327)
                  ·
                    rfl

theorem cell22_637984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 2, 1, 2, 1, 5].length) (baseStart_637984 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_637984 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_637984 prefixEnd_637984 := by exact prefixLift 637984
  have htrace : WordTrace (prefixWord ++ tailWord_637984) baseStart_637984 baseEnd_637984 := by
    simpa [prefixWord, tailWord_637984, baseEnd_637984] using wordTrace_append hprefix tailTrace_637984
  have hstable : (prefixWord ++ tailWord_637984).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_637984).length < 2 ^ (prefixWord ++ tailWord_637984).sum := by decide
  have hdescent : baseEnd_637984 < baseStart_637984 := by decide
  rcases family_descends (prefixWord ++ tailWord_637984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_638008 : List Nat := [2, 1, 2, 1, 5, 1, 1, 3, 2, 4]
def baseStart_638008 : Nat := 118140960795 + 638008 * 2 ^ 59
def prefixEnd_638008 : Nat := 4983230072969 + 3 ^ 40 * 638008 * 2
def baseEnd_638008 : Nat := 218403176942563349643907

theorem tailTrace_638008 : CollatzResearch.WordTrace tailWord_638008 prefixEnd_638008 218403176942563349643907 := by
  unfold tailWord_638008
  simp only [CollatzResearch.WordTrace]
  refine ⟨11635031736306726968257339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15513375648408969291009785 11635031736306726968257339)
  ·
    refine ⟨17452547604460090452386009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11635031736306726968257339 17452547604460090452386009)
    ·
      refine ⟨13089410703345067839289507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17452547604460090452386009 13089410703345067839289507)
      ·
        refine ⟨19634116055017601758934261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13089410703345067839289507 19634116055017601758934261)
        ·
          refine ⟨1840698380157900164900087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 19634116055017601758934261 1840698380157900164900087)
          ·
            refine ⟨2761047570236850247350131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1840698380157900164900087 2761047570236850247350131)
            ·
              refine ⟨4141571355355275371025197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2761047570236850247350131 4141571355355275371025197)
              ·
                refine ⟨1553089258258228264134449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4141571355355275371025197 1553089258258228264134449)
                ·
                  refine ⟨1164816943693671198100837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1553089258258228264134449 1164816943693671198100837)
                  ·
                    refine ⟨218403176942563349643907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1164816943693671198100837 218403176942563349643907)
                    ·
                      rfl

theorem cell22_638008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 1, 3, 2, 4].length) (baseStart_638008 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_638008 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_638008 prefixEnd_638008 := by exact prefixLift 638008
  have htrace : WordTrace (prefixWord ++ tailWord_638008) baseStart_638008 baseEnd_638008 := by
    simpa [prefixWord, tailWord_638008, baseEnd_638008] using wordTrace_append hprefix tailTrace_638008
  have hstable : (prefixWord ++ tailWord_638008).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_638008).length < 2 ^ (prefixWord ++ tailWord_638008).sum := by decide
  have hdescent : baseEnd_638008 < baseStart_638008 := by decide
  rcases family_descends (prefixWord ++ tailWord_638008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_638029 : List Nat := [1, 6, 1, 1, 1, 4, 2, 2, 4]
def baseStart_638029 : Nat := 118140960795 + 638029 * 2 ^ 59
def prefixEnd_638029 : Nat := 4983230072969 + 3 ^ 40 * 638029 * 2
def baseEnd_638029 : Nat := 72803455223908764956281

theorem tailTrace_638029 : CollatzResearch.WordTrace tailWord_638029 prefixEnd_638029 72803455223908764956281 := by
  unfold tailWord_638029
  simp only [CollatzResearch.WordTrace]
  refine ⟨23270829405537374523029141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15513886270358249682019427 23270829405537374523029141)
  ·
    refine ⟨1090820128384564430766991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 23270829405537374523029141 1090820128384564430766991)
    ·
      refine ⟨1636230192576846646150487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1090820128384564430766991 1636230192576846646150487)
      ·
        refine ⟨2454345288865269969225731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1636230192576846646150487 2454345288865269969225731)
        ·
          refine ⟨3681517933297904953838597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2454345288865269969225731 3681517933297904953838597)
          ·
            refine ⟨690284612493357178844737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3681517933297904953838597 690284612493357178844737)
            ·
              refine ⟨517713459370017884133553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 690284612493357178844737 517713459370017884133553)
              ·
                refine ⟨388285094527513413100165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 517713459370017884133553 388285094527513413100165)
                ·
                  refine ⟨72803455223908764956281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 388285094527513413100165 72803455223908764956281)
                  ·
                    rfl

theorem cell22_638029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 4, 2, 2, 4].length) (baseStart_638029 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_638029 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_638029 prefixEnd_638029 := by exact prefixLift 638029
  have htrace : WordTrace (prefixWord ++ tailWord_638029) baseStart_638029 baseEnd_638029 := by
    simpa [prefixWord, tailWord_638029, baseEnd_638029] using wordTrace_append hprefix tailTrace_638029
  have hstable : (prefixWord ++ tailWord_638029).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_638029).length < 2 ^ (prefixWord ++ tailWord_638029).sum := by decide
  have hdescent : baseEnd_638029 < baseStart_638029 := by decide
  rcases family_descends (prefixWord ++ tailWord_638029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_638051 : List Nat := [1, 1, 1, 5, 1, 1, 1, 2, 9]
def baseStart_638051 : Nat := 118140960795 + 638051 * 2 ^ 59
def prefixEnd_638051 : Nat := 4983230072969 + 3 ^ 40 * 638051 * 2
def baseEnd_638051 : Nat := 72805965573775190272925

theorem tailTrace_638051 : CollatzResearch.WordTrace tailWord_638051 prefixEnd_638051 72805965573775190272925 := by
  unfold tailWord_638051
  simp only [CollatzResearch.WordTrace]
  refine ⟨23271631811457672280330007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15514421207638448186886671 23271631811457672280330007)
  ·
    refine ⟨34907447717186508420495011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23271631811457672280330007 34907447717186508420495011)
    ·
      refine ⟨52361171575779762630742517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34907447717186508420495011 52361171575779762630742517)
      ·
        refine ⟨4908859835229352746632111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 52361171575779762630742517 4908859835229352746632111)
        ·
          refine ⟨7363289752844029119948167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4908859835229352746632111 7363289752844029119948167)
          ·
            refine ⟨11044934629266043679922251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7363289752844029119948167 11044934629266043679922251)
            ·
              refine ⟨16567401943899065519883377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11044934629266043679922251 16567401943899065519883377)
              ·
                refine ⟨12425551457924299139912533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16567401943899065519883377 12425551457924299139912533)
                ·
                  refine ⟨72805965573775190272925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 12425551457924299139912533 72805965573775190272925)
                  ·
                    rfl

theorem cell22_638051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 2, 9].length) (baseStart_638051 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_638051 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_638051 prefixEnd_638051 := by exact prefixLift 638051
  have htrace : WordTrace (prefixWord ++ tailWord_638051) baseStart_638051 baseEnd_638051 := by
    simpa [prefixWord, tailWord_638051, baseEnd_638051] using wordTrace_append hprefix tailTrace_638051
  have hstable : (prefixWord ++ tailWord_638051).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_638051).length < 2 ^ (prefixWord ++ tailWord_638051).sum := by decide
  have hdescent : baseEnd_638051 < baseStart_638051 := by decide
  rcases family_descends (prefixWord ++ tailWord_638051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_638055 : List Nat := [1, 1, 5, 1, 1, 4, 1, 2, 3, 3]
def baseStart_638055 : Nat := 118140960795 + 638055 * 2 ^ 59
def prefixEnd_638055 : Nat := 4983230072969 + 3 ^ 40 * 638055 * 2
def baseEnd_638055 : Nat := 218419266003070893718763

theorem tailTrace_638055 : CollatzResearch.WordTrace tailWord_638055 prefixEnd_638055 218419266003070893718763 := by
  unfold tailWord_638055
  simp only [CollatzResearch.WordTrace]
  refine ⟨23271777703443180963475619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15514518468962120642317079 23271777703443180963475619)
  ·
    refine ⟨34907666555164771445213429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23271777703443180963475619 34907666555164771445213429)
    ·
      refine ⟨3272593739546697322988759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 34907666555164771445213429 3272593739546697322988759)
      ·
        refine ⟨4908890609320045984483139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3272593739546697322988759 4908890609320045984483139)
        ·
          refine ⟨7363335913980068976724709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4908890609320045984483139 7363335913980068976724709)
          ·
            refine ⟨1380625483871262933135883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7363335913980068976724709 1380625483871262933135883)
            ·
              refine ⟨2070938225806894399703825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1380625483871262933135883 2070938225806894399703825)
              ·
                refine ⟨1553203669355170799777869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2070938225806894399703825 1553203669355170799777869)
                ·
                  refine ⟨582451376008189049916701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1553203669355170799777869 582451376008189049916701)
                  ·
                    refine ⟨218419266003070893718763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 582451376008189049916701 218419266003070893718763)
                    ·
                      rfl

theorem cell22_638055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 1, 2, 3, 3].length) (baseStart_638055 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_638055 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_638055 prefixEnd_638055 := by exact prefixLift 638055
  have htrace : WordTrace (prefixWord ++ tailWord_638055) baseStart_638055 baseEnd_638055 := by
    simpa [prefixWord, tailWord_638055, baseEnd_638055] using wordTrace_append hprefix tailTrace_638055
  have hstable : (prefixWord ++ tailWord_638055).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_638055).length < 2 ^ (prefixWord ++ tailWord_638055).sum := by decide
  have hdescent : baseEnd_638055 < baseStart_638055 := by decide
  rcases family_descends (prefixWord ++ tailWord_638055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_638078 : List Nat := [4, 2, 4, 1, 1, 2, 1, 2, 2, 3]
def baseStart_638078 : Nat := 118140960795 + 638078 * 2 ^ 59
def prefixEnd_638078 : Nat := 4983230072969 + 3 ^ 40 * 638078 * 2
def baseEnd_638078 : Nat := 218427139373106500393693

theorem tailTrace_638078 : CollatzResearch.WordTrace tailWord_638078 prefixEnd_638078 218427139373106500393693 := by
  unfold tailWord_638078
  simp only [CollatzResearch.WordTrace]
  refine ⟨2909077072794981986445361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15515077721573237261041925 2909077072794981986445361)
  ·
    refine ⟨2181807804596236489834021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2909077072794981986445361 2181807804596236489834021)
    ·
      refine ⟨409088963361794341843879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2181807804596236489834021 409088963361794341843879)
      ·
        refine ⟨613633445042691512765819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 409088963361794341843879 613633445042691512765819)
        ·
          refine ⟨920450167564037269148729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 613633445042691512765819 920450167564037269148729)
          ·
            refine ⟨690337625673027951861547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 920450167564037269148729 690337625673027951861547)
            ·
              refine ⟨1035506438509541927792321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 690337625673027951861547 1035506438509541927792321)
              ·
                refine ⟨776629828882156445844241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1035506438509541927792321 776629828882156445844241)
                ·
                  refine ⟨582472371661617334383181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 776629828882156445844241 582472371661617334383181)
                  ·
                    refine ⟨218427139373106500393693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 582472371661617334383181 218427139373106500393693)
                    ·
                      rfl

theorem cell22_638078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 2, 1, 2, 2, 3].length) (baseStart_638078 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_638078 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_638078 prefixEnd_638078 := by exact prefixLift 638078
  have htrace : WordTrace (prefixWord ++ tailWord_638078) baseStart_638078 baseEnd_638078 := by
    simpa [prefixWord, tailWord_638078, baseEnd_638078] using wordTrace_append hprefix tailTrace_638078
  have hstable : (prefixWord ++ tailWord_638078).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_638078).length < 2 ^ (prefixWord ++ tailWord_638078).sum := by decide
  have hdescent : baseEnd_638078 < baseStart_638078 := by decide
  rcases family_descends (prefixWord ++ tailWord_638078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
